
use std::alloc::Global;

use feanor_math::algorithms::convolution::rns::{RNSConvolution, RNSConvolutionZn};
use feanor_math::algorithms::interpolate::interpolate;
use feanor_math::algorithms::linsolve::LinSolveRingStore;
use feanor_math::algorithms::miller_rabin::is_prime;
use feanor_math::algorithms::multipointeval::multipointeval;
use feanor_math::divisibility::{DivisibilityRing, DivisibilityRingStore};
use feanor_math::homomorphism::{CanHomFrom, Homomorphism};
use feanor_math::matrix::OwnedMatrix;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::primitive_int::{StaticRing, StaticRingBase};
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::zn::{ZnRingStore, zn_64};
use feanor_math::seq::{VectorFn, VectorView};
use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
use feanor_math::integer::{BigIntRing, BigIntRingBase, IntegerRing, IntegerRingStore, int_cast};
use feanor_math::ring::*;
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use feanor_math::rings::zn::zn_64::Zn;
use tracing::instrument;

use crate::poly_eval::to_circuit::poly_to_circuit;
use crate::circuit::PlaintextCircuit;
use crate::{NiceZn, ZZbig, ZZi64};

///
/// The digit extraction operation, as required during BFV and
/// BGV bootstrapping.
/// 
/// Concretely, this encapsulates an efficient implementation of the
/// per-slot digit extraction function
/// ```text
///   Z/p^eZ -> Z/p^rZ x Z/p^eZ,  x -> (x - (x mod p^v) / p^v, x mod p^v)
/// ```
/// for `v = e - r`. Here `x mod p^v` refers to the smallest positive element
/// of `Z/p^eZ` that is congruent to `x` modulo `p^v`.
/// 
/// This function can also be applied to values in a ring `Z/p^e'Z` for
/// `e' > e`, i.e. it will then have the signature
/// ```text
///   Z/p^e'Z -> Z/p^(e' - e + r)Z x Z/p^e'Z
/// ```
/// In this case, the results are only specified modulo `p^r` resp. `p^e`, i.e.
/// may be perturbed by an arbitrary value `p^r a` resp. `p^e a'`.
/// 
pub struct DigitExtract<R: ?Sized + RingBase = StaticRingBase<i64>> {
    extraction_circuits: Vec<(Vec<usize>, PlaintextCircuit<R>)>,
    /// the one-input, one-output identity circuit
    identity_circuit: PlaintextCircuit<R>,
    /// the two-input, one-output addition circuit
    add_circuit: PlaintextCircuit<R>,
    /// the two-input, one-output subtraction circuit
    sub_circuit: PlaintextCircuit<R>,
    v: usize,
    e: usize,
    p: El<BigIntRing>
}

impl DigitExtract {

    ///
    /// Creates a [`DigitExtract`] for a scalar ring `Z/2^eZ`.
    /// 
    /// Uses the precomputed table of best digit extraction circuits for `e <= 23`.
    /// 
    #[instrument(skip_all)]
    pub fn new_precomputed_p_is_2(p: i64, e: usize, r: usize) -> Self {
        assert_eq!(2, p);
        assert!(is_prime(&StaticRing::<i64>::RING, &p, 10));
        return Self::new_with_circuits(
            int_cast(p, ZZbig, ZZi64), 
            e, 
            r, 
            StaticRing::<i64>::RING, 
            [1, 2, 4, 8, 16, 23].into_iter().map(|e| (
                [1, 2, 4, 8, 16, 23].into_iter().take_while(|i| *i <= e).collect(),
                precomputed_p_2(e)
            )).collect::<Vec<_>>()
        );
    }
    
    ///
    /// Creates a [`DigitExtract`] for a scalar ring `Z/p^eZ`.
    /// 
    /// Uses the Chen-Han digit retain polynomials <https://ia.cr/2018/067> together with
    /// a heuristic method to compile them into an arithmetic circuit, based on the
    /// Paterson-Stockmeyer method.
    /// 
    #[instrument(skip_all)]
    pub fn new_default(p: i64, e: usize, r: usize) -> Self {
        assert!(is_prime(&StaticRing::<i64>::RING, &p, 10));
        assert!(e > r);
        let v = e - r;
        
        let digit_extraction_circuits = (1..=v).rev().map(|i| {
            let required_digits = (2..=(v - i + 1)).chain([r + v - i + 1].into_iter()).collect::<Vec<_>>();
            let poly_ring = DensePolyRing::new(Zn::new(StaticRing::<i64>::RING.pow(p, *required_digits.last().unwrap()) as u64), "X");
            let circuit = poly_to_circuit(&poly_ring, &required_digits.iter().map(|j| digit_retain_poly(&poly_ring, *j)).collect::<Vec<_>>())
                .change_ring_uniform(|x| x.change_ring(|x| poly_ring.base_ring().smallest_lift(x)));
            return (required_digits, circuit);
        }).collect::<Vec<_>>();
        assert!(digit_extraction_circuits.is_sorted_by_key(|(digits, _)| *digits.last().unwrap()));
        
        return Self::new_with_circuits(int_cast(p, ZZbig, ZZi64), e, r, StaticRing::<i64>::RING, digit_extraction_circuits);
    }

    ///
    /// Creates a [`DigitExtract`] for a scalar ring `Z/p^eZ`.
    /// 
    /// Uses the Ma, Huang, Wang and Want digit extraction polynomials <https://ia.cr/2024/115> 
    /// for errors bounded by `B` and large `p`, together with a heuristic method to compile them
    /// into an algebraic circuit, based on the Paterson-Stockmeyer method.
    /// 
    #[instrument(skip_all)]
    pub fn new_bounded_error(p: i64, e: usize, B: i64) -> Self {
        assert!(is_prime(&ZZi64, &p, 10));
        assert!(B >= 0);
        assert!(2 * B + 1 <= p);
        
        let poly_ring = DensePolyRing::new(Zn::new(StaticRing::<i64>::RING.pow(p, e) as u64), "X");
        let p_half = poly_ring.inclusion().map(poly_ring.base_ring().coerce(&ZZi64, p / 2));
        let circuit = poly_to_circuit(&poly_ring, &[
            poly_ring.add(poly_ring.evaluate(&bounded_digit_retain_poly(&poly_ring, B), &poly_ring.sub_ref_snd(poly_ring.indeterminate(), &p_half), poly_ring.inclusion()), p_half)
        ]).change_ring_uniform(|x| x.change_ring(|x| poly_ring.base_ring().smallest_lift(x)));
        let digit_extraction_circuits = vec![(vec![e], circuit)];
        
        return Self::new_with_circuits(int_cast(p, ZZbig, ZZi64), e, e - 1, StaticRing::<i64>::RING, digit_extraction_circuits);
    }
}

impl<R: ?Sized + RingBase> DigitExtract<R> {

    ///
    /// Creates a new [`DigitExtract`] from the given circuits.
    /// 
    /// This functions expects the list of circuits to contain tuples `(digits, C)`,
    /// where the circuit `C` takes a single input and computes `digits.len()` outputs, 
    /// such that the `i`-th output is congruent to `lift(input mod p)` modulo 
    /// `p^digits[i]`.
    /// 
    /// If you want to use the default choice of circuits, consider using [`DigitExtract::new_default()`].
    /// 
    pub fn new_with_circuits<S: Copy + RingStore<Type = R>>(p: El<BigIntRing>, e: usize, r: usize, ring: S, extraction_circuits: Vec<(Vec<usize>, PlaintextCircuit<R>)>) -> Self {
        assert!(is_prime(ZZbig, &p, 10));
        assert!(e > r);
        for (digits, circuit) in &extraction_circuits {
            assert!(digits.is_sorted());
            assert_eq!(digits.len(), circuit.output_count());
            assert_eq!(1, circuit.input_count());
        }
        assert!(extraction_circuits.iter().any(|(digits, _)| *digits.last().unwrap() >= e));
        Self {
            extraction_circuits: extraction_circuits,
            add_circuit: PlaintextCircuit::add(ring),
            sub_circuit: PlaintextCircuit::sub(ring),
            identity_circuit: PlaintextCircuit::identity(1, ring),
            v: e - r,
            p: p,
            e: e
        }
    }

    pub fn r(&self) -> usize {
        self.e - self.v
    }

    pub fn e(&self) -> usize {
        self.e
    }

    pub fn v(&self) -> usize {
        self.v
    }

    pub fn p(&self) -> &El<BigIntRing> {
        &self.p
    }
    
    ///
    /// Evaluates the digit extraction function over any representation of elements of `Z/p^iZ`, which
    /// supports the evaluation of [`PlaintextCircuit`]s. Since digit extraction requires computations
    /// in all the rings `Z/p^(r - 1)Z, ...., Z/p^eZ`, we also require a `change_space` function, with
    /// the following properties:
    /// ```text
    ///   change_space(e, e', .): Z/p^eZ -> Z/p^e' Z
    ///   change_space(e, e', x mod p^e) = x p^(e' - e) mod p^e'      if e' > e
    ///   change_space(e, e', x mod p^e) = x / p^(e - e') mod p^e'    if e' < e and p^(e - e') | x
    /// ```
    /// If the passed functions behave as specified, `change_space(e, e', x)` will never be called for
    /// `e' < e` and an `x` which is not divisible by `p^(e - e')`.
    /// 
    /// Furthermore, the `eval_circuit` is given the exponent of the current ring we work in as the first
    /// parameter. The result of [`DigitExtract::evaluate_generic()`] is then the tuple `(quo, rem)` with
    /// `quo` in `Z/p^rZ` and `rem` in `Z/p^eZ` such that `x = p^(e - r) * quo + rem` and `rem < p^(e - r)`.
    /// 
    /// If [`DigitExtract`] is used on elements of `Z/p^e'Z` with `e' > e` (as mentioned at the end of
    /// the doc of [`DigitExtract`]), the moduli passed to `eval_circuit()` and `change_space()` remain
    /// nevertheless unchanged - after all, `evaluate_generic()` does not know that we are in a larger
    /// ring. If necessary, you have to manually offset all exponents passed to `eval_circuit` and 
    /// `change_space` by `e' - e`.
    /// 
    pub fn evaluate_generic<T, EvalCircuit, ChangeSpace>(&self, 
        input: T,
        mut eval_circuit: EvalCircuit,
        mut change_space: ChangeSpace
    ) -> (T, T) 
        where EvalCircuit: FnMut(/* exponent of p */ usize, &[T], &PlaintextCircuit<R>) -> Vec<T>,
            ChangeSpace: FnMut(/* input exponent of p */ usize, /* output exponent of p */ usize, T) -> T
    {
        let e = self.e;
        let r = self.e - self.v;

        enum OneOrTwoValues<T> {
            One(T), Two([T; 2])
        }

        impl<T> OneOrTwoValues<T> {

            fn with_first_el<'a>(&'a mut self, first: T) -> &'a mut [T; 2] {
                take_mut::take(self, |value| match value {
                    OneOrTwoValues::One(second) => OneOrTwoValues::Two([first, second]),
                    OneOrTwoValues::Two([_, second]) => OneOrTwoValues::Two([first, second])
                });
                return match self {
                    OneOrTwoValues::One(_) => unreachable!(),
                    OneOrTwoValues::Two(data) => data
                };
            }

            fn get_second<'a>(&'a self) -> &'a T {
                match self {
                    OneOrTwoValues::One(second) => second,
                    OneOrTwoValues::Two([_, second]) => second
                }
            }
        }

        let clone_value = |modulus_exp: usize, value: &T, eval_circuit: &mut EvalCircuit| eval_circuit(modulus_exp, std::slice::from_ref(value), &self.identity_circuit).into_iter().next().unwrap();
        let sub_values = |modulus_exp: usize, params: &[T; 2], eval_circuit: &mut EvalCircuit| eval_circuit(modulus_exp, params, &self.sub_circuit).into_iter().next().unwrap();
        let add_values = |modulus_exp: usize, params: &[T; 2], eval_circuit: &mut EvalCircuit| eval_circuit(modulus_exp, params, &self.add_circuit).into_iter().next().unwrap();

        let mut mod_result: Option<T> = None;
        let mut partial_floor_divs = (0..self.v).map(|_| Some(clone_value(e, &input, &mut eval_circuit))).collect::<Vec<_>>();
        let mut floor_div_result = input;
        for i in 0..self.v {
            let remaining_digits = e - i;
            debug_assert!(self.extraction_circuits.is_sorted_by_key(|(digits, _)| *digits.last().unwrap()));
            let (use_circuit_digits, use_circuit) = self.extraction_circuits.iter().filter(|(digits, _)| *digits.last().unwrap() >= remaining_digits).next().unwrap();
            debug_assert!(use_circuit_digits.is_sorted());

            let current = change_space(e, remaining_digits, partial_floor_divs[i].take().unwrap());
            let digit_extracted = eval_circuit(remaining_digits, std::slice::from_ref(&current), use_circuit);
            let mut digit_extracted = digit_extracted.into_iter().map(|value| OneOrTwoValues::One(change_space(remaining_digits, e, value))).collect::<Vec<_>>();
            
            let last_digit_extracted = digit_extracted.last_mut().unwrap();
            take_mut::take(&mut floor_div_result, |current| sub_values(e, last_digit_extracted.with_first_el(current), &mut eval_circuit));
            if let Some(mod_result) = &mut mod_result {
                take_mut::take(mod_result, |current| add_values(e, last_digit_extracted.with_first_el(current), &mut eval_circuit));
            } else {
                mod_result = Some(clone_value(e, last_digit_extracted.get_second(), &mut eval_circuit));
            }

            for j in (i + 1)..self.v {
                let digit_extracted_index = use_circuit_digits.iter().enumerate().filter(|(_, cleared_digits)| **cleared_digits > j - i).next().unwrap().0;
                take_mut::take(partial_floor_divs[j].as_mut().unwrap(), |current| sub_values(e, digit_extracted[digit_extracted_index].with_first_el(current), &mut eval_circuit));
            }
        }

        return (change_space(e, r, floor_div_result), mod_result.unwrap());
    }

    ///
    /// Computes `(quo, rem)` with `input = quo * p^(e - r) + rem` and `rem < p^(e - r)`.
    /// Note that both `quo` and `rem` are returned as elements of `Z/p^eZ`, which means that
    /// `quo` is defined only up to a multiple of `p^r`.
    /// 
    /// This function is designed to test digit extraction, since `quo` and `rem` will be computed
    /// exactly in the same way as in a homomorphic setting. Note also that performing euclidean
    /// division can be done much easier with [`EuclideanRing::euclidean_div_rem()`]
    /// when you have access to the ring elements.
    /// 
    /// This function does not perform any checks on the underlying ring, in particular, you can
    /// call it on an input in `Z/p^e'Z` with `e' > e` or an input in `Z`. Of course, in any case,
    /// the output will only be correct modulo `p^r` resp. `p^e`.
    /// 
    /// [`EuclideanRing::euclidean_div_rem()`]: feanor_math::pid::EuclideanRing::euclidean_div_rem()
    /// 
    pub fn evaluate<H, S>(&self, input: S::Element, hom: H) -> (S::Element, S::Element)
        where H: Homomorphism<R, S>,
            S: ?Sized + RingBase + DivisibilityRing
    {
        // temporarily copied from feanor-math
        fn map_from_integer_ring<I, R>(from: I, to: R, mut x: El<I>) -> El<R>
            where I: RingStore,
                I::Type: IntegerRing,
                R: RingStore
        {
            let basis = to.int_hom().map(1 << 16);
            let is_neg = if from.is_neg(&x) {
                from.negate_inplace(&mut x);
                true
            } else {
                false
            };
            let mut current = to.zero();
            let mut current_pow = to.one();
            while !from.is_zero(&x) {
                let mut quo = from.clone_el(&x);
                from.euclidean_div_pow_2(&mut quo, 16);
                let mut rem = from.clone_el(&quo);
                from.mul_pow_2(&mut rem, 16);
                from.sub_self_assign(&mut rem, x);
                let rem = int_cast(rem, StaticRing::<i32>::RING, &from);
                to.add_assign(&mut current, to.mul_ref_snd(to.int_hom().map(rem), &current_pow));
                x = quo;
                to.mul_assign_ref(&mut current_pow, &basis);
            }
            if is_neg {
                return to.negate(current);
            } else {
                return current;
            }
        }

        let p = map_from_integer_ring(ZZbig, hom.codomain(), ZZbig.clone_el(&self.p));
        self.evaluate_generic(
            input,
            |_, params, circuit| circuit.evaluate_no_galois(params, &hom),
            |from, to, x| if from < to {
                hom.codomain().mul(x, hom.codomain().pow(hom.codomain().clone_el(&p), to - from))
            } else {
                hom.codomain().checked_div(&x, &hom.codomain().pow(hom.codomain().clone_el(&p), from - to)).unwrap()
            }
        )
    }
}

///
/// Returns the best arithmetic circuit that computes a function
/// ```text
///   digitex: Z/2^eZ -> (Z/2^eZ)^log(e)
/// ```
/// that satisfies `digitex(x)[i] = (x mod 2) mod 2^(2^i)`.
/// `e` must be a power of two.
/// 
/// Uses a lookup-table, consisting mainly of the values from <https://ia.cr/2022/1364>, except for
/// `e > 8`, where there seemed to be a mistake in the paper.
/// 
pub fn precomputed_p_2(e: usize) -> PlaintextCircuit<StaticRingBase<i64>> {
    assert!(e <= 23, "no precomputed tables are available for t > 2^23");
    let log2_e_ceil = ZZi64.abs_log2_ceil(&(e as i64)).unwrap();
    
    let id = || PlaintextCircuit::linear_transform_ring(&[1], ZZi64);
    let f0 = id().clone(ZZi64);
    if log2_e_ceil == 0 {
        return f0;
    }

    let f1 = id().tensor(PlaintextCircuit::square(ZZi64), ZZi64).compose(PlaintextCircuit::select(1, &[0, 0], ZZi64).compose(f0, ZZi64), ZZi64);
    if log2_e_ceil == 1 {
        return f1;
    }

    let f2 = id().tensor(id(), ZZi64).tensor(PlaintextCircuit::square(ZZi64), ZZi64).compose(PlaintextCircuit::select(2, &[0, 1, 1], ZZi64).compose(f1, ZZi64), ZZi64);
    if log2_e_ceil == 2 {
        return f2;
    }
    
    let f3_comp = PlaintextCircuit::add(ZZi64).compose(
        PlaintextCircuit::linear_transform_ring(&[112], ZZi64).tensor(PlaintextCircuit::square(ZZi64).compose(
            PlaintextCircuit::linear_transform_ring(&[94, 121], ZZi64), ZZi64
        ), ZZi64), ZZi64
    ).compose(
        PlaintextCircuit::select(2, &[0, 0, 1], ZZi64), ZZi64
    );
    let f3 = id().tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(f3_comp, ZZi64).compose(
        PlaintextCircuit::select(3, &[0, 1, 2, 1, 2], ZZi64), ZZi64
    ).compose(f2, ZZi64);
    if log2_e_ceil == 3 {
        return f3;
    }

    let f4_comp = PlaintextCircuit::add(ZZi64).compose(
        PlaintextCircuit::linear_transform_ring(&[1984, 528, 22620], ZZi64).tensor(PlaintextCircuit::mul(ZZi64).compose(
            PlaintextCircuit::linear_transform_ring(&[226, 113], ZZi64).tensor(PlaintextCircuit::linear_transform_ring(&[8, 2, 301], ZZi64), ZZi64), ZZi64
        ), ZZi64), ZZi64
    ).compose(
        PlaintextCircuit::select(3, &[0, 1, 2, 1, 2, 0, 1, 2], ZZi64), ZZi64
    );
    let f4 = id().tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(f4_comp, ZZi64).compose(
        PlaintextCircuit::select(4, &[0, 1, 2, 3, 1, 2, 3], ZZi64), ZZi64
    ).compose(f3, ZZi64);
    if log2_e_ceil == 4 {
        return f4;
    }

    let f5_comp = PlaintextCircuit::add(ZZi64).compose(
        PlaintextCircuit::linear_transform_ring(&[4849408, 3564625, 2737008, 6563608], ZZi64).tensor(PlaintextCircuit::mul(ZZi64).compose(
            PlaintextCircuit::linear_transform_ring(&[997183, 8295548, 419894, 879825], ZZi64).tensor(PlaintextCircuit::linear_transform_ring(&[443729, 555132, 491350, 758385], ZZi64), ZZi64), ZZi64
        ), ZZi64), ZZi64
    ).compose(
        PlaintextCircuit::select(4, &[0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3], ZZi64), ZZi64
    );
    let f5 = id().tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(f5_comp, ZZi64).compose(
        PlaintextCircuit::select(5, &[0, 1, 2, 3, 4, 1, 2, 3, 4], ZZi64), ZZi64
    ).compose(f4, ZZi64);
    if log2_e_ceil == 5 {
        return f5;
    }
    unreachable!()
}

///
/// Computes a low-degree polynomial `f` such that `f(x + py) = x` for
/// `x` in `{ -B, ..., B }` over `Z/p^eZ`.
/// 
#[instrument(skip_all)]
pub fn bounded_digit_retain_poly<P>(poly_ring: P, bound: i64) -> El<P>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn
{
    let base_ring = poly_ring.base_ring();
    let (p, e) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    assert!(base_ring.integer_ring().is_lt(&int_cast(2 * bound, base_ring.integer_ring(), ZZi64), &p));
    let hom = base_ring.can_hom(&ZZi64).unwrap();

    // poly that is zero modulo p on the support
    let base_null_poly = poly_ring.prod((-bound..=bound).map(|i| poly_ring.from_terms([(base_ring.one(), 1), (hom.map(i), 0)])));
    // poly that is zero modulo p^e on the support
    let null_polys = (0..=e).scan(poly_ring.one(), |current, _| {
        let result = poly_ring.clone_el(current);
        poly_ring.mul_assign_ref(current, &base_null_poly);
        return Some(result);
    }).collect::<Vec<_>>();
    let null_poly = null_polys.last().unwrap();
    let modulus = (0..poly_ring.degree(null_poly).unwrap()).map(|i| base_ring.negate(base_ring.clone_el(poly_ring.coefficient_at(null_poly, i)))).collect::<Vec<_>>();
    let mod_null_poly_ring = FreeAlgebraImpl::new(base_ring, poly_ring.degree(&null_poly).unwrap(), modulus);
    // poly whose value is `= x mod p` and independent of `y` on `x + p y`
    let base_poly = mod_null_poly_ring.poly_repr(&poly_ring, &mod_null_poly_ring.pow_gen(mod_null_poly_ring.canonical_gen(), base_ring.modulus(), base_ring.integer_ring()), base_ring.identity());

    let len = 2 * bound as usize + 1;
    let x = (0..len).map_fn(|i| hom.map(i as i64 - bound));
    let mut matrix = OwnedMatrix::from_fn(len, len, |i, j| base_ring.pow(x.at(i), j));
    let mut expected = OwnedMatrix::from_fn(len, 1, |i, _| base_ring.sub(x.at(i), poly_ring.evaluate(&base_poly, &x.at(i), base_ring.identity())));
    let mut result = OwnedMatrix::zero(len, 1, base_ring);
    <_ as LinSolveRingStore>::solve_right(base_ring, matrix.data_mut(), expected.data_mut(), result.data_mut()).assert_solved();
    let digit_extraction_poly = poly_ring.add(
        base_poly,
        poly_ring.from_terms((0..len).map(|i| (base_ring.clone_el(result.at(i, 0)), i)))
    );
    let mut digit_retain_poly = mod_null_poly_ring.canonical_gen();
    for _ in 1..e {
        digit_retain_poly = poly_ring.evaluate(&digit_extraction_poly, &digit_retain_poly, mod_null_poly_ring.inclusion());
    }

    let digit_retain_poly = mod_null_poly_ring.poly_repr(&poly_ring, &digit_retain_poly, base_ring.identity());
    return reduce_mod_null_poly_lattice(&poly_ring, digit_retain_poly, &null_polys, &int_cast(p, ZZbig, base_ring.integer_ring()), e);
}

///
/// Computes `min { n | n! % p^e == 0 }`
/// 
pub fn mu(p: i64, e: usize) -> El<BigIntRing> {
    let mut n = int_cast(p, ZZbig, ZZi64);
    let mut n_fac = int_cast(p, ZZbig, ZZi64);
    let divisor = ZZbig.pow(int_cast(p, ZZbig, ZZi64), e);
    while ZZbig.checked_div(&n_fac, &divisor).is_none() {
        ZZbig.add_assign(&mut n, int_cast(p, ZZbig, ZZi64));
        ZZbig.mul_assign_ref(&mut n_fac, &n);
    }
    return n;
}

///
/// Computes `prod_(i < m) (X - i)`.
/// 
pub fn falling_factorial_poly<P>(poly_ring: P, m: usize) -> El<P>
    where P: RingStore,
        P::Type: PolyRing
{
    poly_ring.prod((0..m).map(|j| poly_ring.sub(poly_ring.indeterminate(), poly_ring.int_hom().map(j as i32))))
}

#[instrument(skip_all)]
fn reduce_mod_null_poly_lattice<P>(poly_ring: P, poly: El<P>, null_polys: &[El<P>], p: &El<BigIntRing>, e: usize) -> El<P>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: DivisibilityRing + CanHomFrom<BigIntRingBase>
{
    let base_ring = poly_ring.base_ring();
    let hom = base_ring.can_hom(&ZZbig).unwrap();
    let mut current = poly;
    let mut current_e = 0;
    while current_e <= e && base_ring.checked_div(poly_ring.lc(&current).unwrap(), &base_ring.pow(hom.map_ref(p), current_e)).is_some() {
        let null_poly = poly_ring.inclusion().mul_ref_fst_map(
            &null_polys[e - current_e],
            base_ring.pow(hom.map_ref(p), current_e)
        );
        while let Some(quo) = base_ring.checked_div(poly_ring.lc(&current).unwrap(), &poly_ring.lc(&null_poly).unwrap()) {
            if poly_ring.degree(&current).unwrap() < poly_ring.degree(&null_poly).unwrap() {
                break;
            }
            let mut subtractor = poly_ring.inclusion().mul_ref_map(&null_poly, &quo);
            poly_ring.mul_assign_monomial(&mut subtractor, poly_ring.degree(&current).unwrap() - poly_ring.degree(&null_poly).unwrap());
            poly_ring.sub_assign(&mut current, subtractor);
        }
        current_e += 1;
    }
    return current;
}

///
/// Returns the lowest-degree polynomial `f` such that `f(x + p^i y) = x mod p^(i + 1)` for
/// `x in { -(p - 1)/2, ..., (p - 1)/2 }`, any `y` and `0 < i < e` (if `p = 2`, this is instead
/// the case for `x in { 0, 1 }`).
/// 
/// The degree of the polynomial is `p`.
/// 
#[instrument(skip_all)]
pub fn centered_digit_extract_poly<P>(poly_ring: P, e: usize) -> El<P>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn
{
    let base_ring = poly_ring.base_ring();
    let (p, e_max) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    assert!(e <= e_max);
    let p = int_cast(p, ZZi64, base_ring.integer_ring());

    let null_polys = (0..=e).map(|i| falling_factorial_poly(poly_ring, int_cast(mu(p, i), ZZi64, ZZbig) as usize)).collect::<Vec<_>>();
    let Fp = zn_64::Zn::new(p as u64).as_field().unwrap();
    let convolution = RNSConvolutionZn::from(RNSConvolution::new(ZZi64.abs_log2_ceil(&(p as i64)).unwrap() + 1));
    let poly_ring_mod_p = DensePolyRing::new_with_convolution(Fp, "X", Global, convolution);
    let mod_p = poly_ring_mod_p.base_ring().can_hom(base_ring.integer_ring()).unwrap();
    let mut current = poly_ring.pow(poly_ring.indeterminate(), p as usize);
    for i in 1..=e {
        let pi = base_ring.integer_ring().pow(int_cast(p, base_ring.integer_ring(), ZZi64), i);
        let x = ((-(p - 1)/2)..=((p - 1)/2)).map(|x| base_ring.coerce(&ZZi64, x)).collect::<Vec<_>>();
        let evaluations = multipointeval(&poly_ring, &current, &x);
        let x = ((-(p - 1)/2)..=((p - 1)/2)).map(|x| poly_ring_mod_p.base_ring().coerce(&ZZi64, x)).collect::<Vec<_>>();
        let y = ((-(p - 1)/2)..=((p - 1)/2)).zip(evaluations.into_iter()).map(|(x, y)| mod_p.map(
            base_ring.integer_ring().checked_div(
                &base_ring.smallest_lift(base_ring.sub(y, base_ring.coerce(&ZZi64, x))), 
                &pi
            ).unwrap()
        )).collect::<Vec<_>>();
        let fix_poly = interpolate(
            &poly_ring_mod_p, 
            x.copy_els(), 
            y.copy_els(), 
            Global
        ).unwrap();
        let pi = base_ring.coerce(base_ring.integer_ring(), pi);
        poly_ring.get_ring().add_assign_from_terms(&mut current, poly_ring_mod_p.terms(&fix_poly).map(|(c, i)| (base_ring.mul_ref_snd(base_ring.coerce(&ZZi64, -poly_ring_mod_p.base_ring().smallest_lift(*c)), &pi), i)));
        // invariant: `current = X^p + p * (...)` and `current(x + p^k y) = x mod p^(k + 1)` for all `k <= i`
    }
    return reduce_mod_null_poly_lattice(poly_ring, current, &null_polys, &int_cast(p, ZZbig, ZZi64), e);
}

///
/// Returns the lowest-degree polynomial `f` such that `f(x + py) = x mod p^e` for
/// `x in { -(p - 1)/2, ..., (p - 1)/2 }` and any `y` (if `p = 2`, this is instead
/// the case for `x in { 0, 1 }`).
/// 
/// The degree of this polynomial is at most `(p - 1)(e - 1) + 1`, but may be smaller
/// than that. This function will always compute the polynomial of lowest degree with
/// above property. For the reason why a polynomial of degree `<= (p - 1)(e - 1) + 1`
/// with the property exists, see Chen and Han's paper <https://ia.cr/2022/1364>.
/// 
#[instrument(skip_all)]
pub fn centered_digit_retain_poly<P>(poly_ring: P, e: usize) -> El<P>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn
{
    assert!(e > 0);
    if e == 1 {
        return poly_ring.indeterminate();
    }
    let base_ring = poly_ring.base_ring();
    let (p, e_max) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    assert!(e <= e_max);
    let p = int_cast(p, ZZi64, base_ring.integer_ring());
    if p == 2 {
        // poly that is zero modulo p^e on the support
        let null_polys = (0..=e).map(|i| falling_factorial_poly(poly_ring, int_cast(mu(p, i), ZZi64, ZZbig) as usize)).collect::<Vec<_>>();
        let null_poly = null_polys.last().unwrap();
        let modulus = (0..poly_ring.degree(null_poly).unwrap()).map(|i| base_ring.negate(base_ring.clone_el(poly_ring.coefficient_at(null_poly, i)))).collect::<Vec<_>>();
        let mod_null_poly_ring = FreeAlgebraImpl::new(base_ring, poly_ring.degree(&null_poly).unwrap(), modulus);

        let digit_retain_poly = mod_null_poly_ring.poly_repr(&poly_ring, &mod_null_poly_ring.pow(mod_null_poly_ring.canonical_gen(), 1 << e), base_ring.identity());
        return reduce_mod_null_poly_lattice(poly_ring, digit_retain_poly, &null_polys, &int_cast(2, ZZbig, ZZi64), e);
    } else if e == 2 {
        return centered_digit_extract_poly(poly_ring, e);
    } else {
        return bounded_digit_retain_poly(poly_ring, p.div_floor(2));
    }
}

///
/// Returns the lowest-degree polynomial `f` such that `f(x + py) = x mod p^e` for
/// `x in { 0, ..., p - 1 }` and any `y`.
/// 
/// The degree of this polynomial is at most `(p - 1)(e - 1) + 1`, but may be smaller
/// than that. This function will always compute the polynomial of lowest degree with
/// above property. For the reason why a polynomial of degree `<= (p - 1)(e - 1) + 1`
/// with the property exists, see Chen and Han's paper <https://ia.cr/2022/1364>.
/// 
#[instrument(skip_all)]
pub fn digit_retain_poly<P>(poly_ring: P, e: usize) -> El<P>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn
{
    assert!(e > 0);
    if e == 1 {
        return poly_ring.indeterminate();
    }
    let base_ring = poly_ring.base_ring();
    let (p, _) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    let p = int_cast(p, ZZi64, base_ring.integer_ring());
    let summand = if p == 2 { 0 } else { ZZi64.checked_div(&(p - 1), &2).unwrap() };
    let result = centered_digit_retain_poly(poly_ring, e);
    return poly_ring.add(
        poly_ring.evaluate(&result, &poly_ring.from_terms([(base_ring.one(), 1), (base_ring.coerce(&ZZi64, -summand), 0)]), poly_ring.inclusion()),
        poly_ring.inclusion().map(base_ring.coerce(&ZZi64, summand))
    );
}

#[cfg(test)]
use feanor_math::assert_el_eq;

#[cfg(test)]
pub fn cmod(x: i64, y: i64) -> i64 {
    x - ZZi64.rounded_div(x, &y) * y
}

#[test]
#[ignore]
fn test_digit_extraction_p_2_complete() {
    let circuit = precomputed_p_2(23);
    let ring = Zn::new(1 << 23);
    let hom = ring.can_hom(&ZZi64).unwrap();
    for x in 0..(1 << 23) {
        for (e, actual) in [1, 2, 4, 8, 16, 23].into_iter().zip(circuit.evaluate_no_galois(&[hom.map(x)], &hom)) {
            assert_eq!(x % 2, ring.smallest_positive_lift(actual) % (1 << e));
        }
    }
}

#[test]
fn test_digit_extraction_p_2() {
    let circuit = precomputed_p_2(17);
    let ring = Zn::new(1 << 17);
    let hom = ring.can_hom(&ZZi64).unwrap();
    for x in 0..(1 << 17) {
        for (e, actual) in [1, 2, 4, 8, 16, 17].into_iter().zip(circuit.evaluate_no_galois(&[hom.map(x)], &hom)) {
            assert_eq!(x % 2, ring.smallest_positive_lift(actual) % (1 << e));
        }
    }
}

#[test]
fn test_centered_digit_retain_poly() {
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 3);
    assert_eq!(Some(33), P.degree(&digit_retain));
    for k in 0..(17 * 17 * 17) {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, cmod(k, 17)), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity()));
    }

    let Zn = Zn::new(19 * 19 * 19);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 2);
    for k in 0..(19 * 19 * 19) {
        assert_eq!(cmod(k, 19), cmod(Zn.smallest_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())), 19 * 19));
    }
    assert_eq!(Some(19), P.degree(&digit_retain));

    let Zn = Zn::new(1024);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 3);
    assert_eq!(Some(3), P.degree(&digit_retain));
    for k in 0..1024 {
        assert_eq!(k % 2, Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 8);
    }
    let digit_retain = centered_digit_retain_poly(&P, 6);
    assert_eq!(Some(6), P.degree(&digit_retain));
    for k in 0..1024 {
        assert_eq!(k % 2, Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 64);
    }
    
    let Zn = Zn::new(257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 2);
    assert_eq!(Some(257), P.degree(&digit_retain));
    for k in 0..257 {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, 2), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity()));
    }

    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 1);
    assert_el_eq!(&P,  P.indeterminate(), digit_retain);
}

#[test]
fn test_centered_digit_extract_poly() {
    let cmod = |x, y| x - ZZi64.rounded_div(x, &y) * y;

    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = centered_digit_extract_poly(&P, 3);
    for k in 0..(17 * 17 * 17) {
        assert_eq!(cmod(k, 17), cmod(Zn.smallest_lift(P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, k), Zn.identity())), 17 * 17));
        assert_eq!(cmod(k, 17), Zn.smallest_lift(P.evaluate(&digit_extract, &P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, k), Zn.identity()), Zn.identity())));
    }
    assert_eq!(Some(17), P.degree(&digit_extract));

    let Zn = Zn::new(19 * 19 * 19);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = centered_digit_extract_poly(&P, 2);
    for k in 0..(19 * 19 * 19) {
        assert_eq!(cmod(k, 19), cmod(Zn.smallest_lift(P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, k), Zn.identity())), 19 * 19));
        assert_eq!(cmod(k, 19), Zn.smallest_lift(P.evaluate(&digit_extract, &P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, k), Zn.identity()), Zn.identity())));
    }
    assert_eq!(Some(19), P.degree(&digit_extract));
    
    let Zn = Zn::new(257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = centered_digit_extract_poly(&P, 2);
    for k in 0..257 {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, 2), &P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity()));
    }
    assert_eq!(Some(257), P.degree(&digit_extract));

    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = centered_digit_extract_poly(&P, 1);
    assert_el_eq!(&P,  P.indeterminate(), digit_extract);
}

#[test]
fn test_digit_retain_poly_small() {
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    for k in 0..(17 * 17 * 17) {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, k % 17), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity()));
    }
    assert_eq!(Some(33), P.degree(&digit_retain));
    
    let Zn = Zn::new(1024);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    for k in 0..1024 {
        assert_eq!(k % 2, Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 8);
    }
    assert_eq!(Some(3), P.degree(&digit_retain));
    let digit_retain = digit_retain_poly(&P, 6);
    for k in 0..1024 {
        assert_eq!(k % 2, Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 64);
    }
    assert_eq!(Some(6), P.degree(&digit_retain));
    
    let Zn = Zn::new(257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 2);
    for k in 0..257 {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, 2), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity()));
    }
    assert_eq!(Some(257), P.degree(&digit_retain));

    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 1);
    assert_el_eq!(&P,  P.indeterminate(), digit_retain);
}

#[test]
fn test_bounded_digit_retain_poly() {
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = bounded_digit_retain_poly(&P, 3);
    for x in -3..=3 {
        for y in 0..(17 * 17) {
            assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, x), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, x + 17 * y), &Zn.identity()));
        }
    }
    assert_eq!(Some(17), P.degree(&digit_retain));
    
    let Zn = Zn::new(257 * 257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = bounded_digit_retain_poly(&P, 4);
    for x in -4..=4 {
        for y in 0..(257 * 257) {
            assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, x), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, x + 257 * y), &Zn.identity()));
        }
    }
    assert_eq!(Some(25), P.degree(&digit_retain));

    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = bounded_digit_retain_poly(&P, 3);
    assert_el_eq!(&P,  P.indeterminate(), digit_retain);
}

#[test]
fn test_digit_retain_poly_large() {
    let Zn = Zn::new(257 * 257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, 251), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 132092), &Zn.identity()));
    for k in 0..(257 * 257) {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, 2), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity()));
    }
}

#[test]
fn test_digit_extract_p2_polys() {
    let digitextract = DigitExtract::new_default(2, 17, 9);
    let ring = Zn::new(ZZi64.pow(2, 17) as u64);
    let hom = ring.can_hom(&ZZi64).unwrap();

    for x in 0..*ring.modulus() {
        let (quo, rem) = digitextract.evaluate_generic(
            (17, hom.map(x)),
            |exp, params, circuit| {
                assert!(params.iter().all(|(p_exp, _)| *p_exp == exp));
                circuit.evaluate_no_galois(&params.iter().map(|(_, x)| *x).collect::<Vec<_>>(), &hom).into_iter().map(|x| (exp, x)).collect()
            },
            |from, to, (exp, x)| {
                assert_eq!(from, exp);
                if from < to {
                    (to, ring.mul(x, ring.pow(hom.map(2), to - from)))
                } else {
                    (to, ring.checked_div(&x, &ring.pow(hom.map(2), from - to)).unwrap())
                }
            }
        );
        assert_eq!(17, rem.0);
        assert_el_eq!(&ring, hom.map(x % (1 << 8)), rem.1);
        assert_eq!(9, quo.0);
        assert_eq!(x / (1 << 8), ring.smallest_positive_lift(quo.1) % (1 << 9));
    }
}

#[test]
fn test_digit_extract() {
    let digitextract = DigitExtract::new_default(3, 5, 2);
    let ring = Zn::new(StaticRing::<i64>::RING.pow(3, 5) as u64);
    let hom = ring.can_hom(&StaticRing::<i64>::RING).unwrap();

    for x in 0..*ring.modulus() {
        let (quo, rem) = digitextract.evaluate_generic(
            (5, hom.map(x)),
            |exp, params, circuit| {
                assert!(params.iter().all(|(p_exp, _)| *p_exp == exp));
                circuit.evaluate_no_galois(&params.iter().map(|(_, x)| *x).collect::<Vec<_>>(), &hom).into_iter().map(|x| (exp, x)).collect()
            },
            |from, to, (exp, x)| {
                assert_eq!(from, exp);
                if from < to {
                    (to, ring.mul(x, ring.pow(hom.map(3), to - from)))
                } else {
                    (to, ring.checked_div(&x, &ring.pow(hom.map(3), from - to)).unwrap())
                }
            }
        );
        assert_eq!(5, rem.0);
        assert_el_eq!(&ring, hom.map(x % 27), rem.1);
        assert_eq!(2, quo.0);
        assert_eq!(x / 27, ring.smallest_positive_lift(quo.1) % 9);
    }
}

#[test]
fn test_digit_extract_evaluate() {
    let ring = Zn::new(16);
    let digit_extract = DigitExtract::new_default(2, 4, 2);
    for x in 0..16 {
        let (actual_high, actual_low) = digit_extract.evaluate(ring.int_hom().map(x), ring.can_hom(&StaticRing::<i64>::RING).unwrap());
        assert_eq!(x / 4, ring.smallest_positive_lift(actual_high) as i32 % 4);
        assert_eq!(x % 4, ring.smallest_positive_lift(actual_low) as i32);
    }

    let ring = Zn::new(81);
    let digit_extract = DigitExtract::new_default(3, 4, 2);
    for x in 0..81 {
        let (actual_high, actual_low) = digit_extract.evaluate(ring.int_hom().map(x), ring.can_hom(&StaticRing::<i64>::RING).unwrap());
        assert_eq!(x / 9, ring.smallest_positive_lift(actual_high) as i32 % 9);
        assert_eq!(x % 9, ring.smallest_positive_lift(actual_low) as i32);
    }

    let ring = Zn::new(125);
    let digit_extract = DigitExtract::new_default(5, 3, 2);
    for x in 0..125 {
        let (actual_high, actual_low) = digit_extract.evaluate(ring.int_hom().map(x), ring.can_hom(&StaticRing::<i64>::RING).unwrap());
        assert_eq!(x / 5, ring.smallest_positive_lift(actual_high) as i32 % 25);
        assert_eq!(x % 5, ring.smallest_positive_lift(actual_low) as i32);
    }
}

#[test]
fn test_digit_extract_evaluate_ignore_higher() {
    let ring = Zn::new(64);
    let digit_extract = DigitExtract::new_default(2, 4, 2);
    for x in 0..64 {
        let (actual_high, actual_low) = digit_extract.evaluate(ring.int_hom().map(x), ring.can_hom(&StaticRing::<i64>::RING).unwrap());
        assert_eq!((x / 4) % 4, ring.smallest_positive_lift(actual_high) as i32 % 4);
        assert_eq!(x % 4, ring.smallest_positive_lift(actual_low) as i32 % 16);
    }

    let ring = Zn::new(243);
    let digit_extract = DigitExtract::new_default(3, 4, 2);
    for x in 0..243 {
        let (actual_high, actual_low) = digit_extract.evaluate(ring.int_hom().map(x), ring.can_hom(&StaticRing::<i64>::RING).unwrap());
        assert_eq!((x / 9) % 9, ring.smallest_positive_lift(actual_high) as i32 % 9);
        assert_eq!(x % 9, ring.smallest_positive_lift(actual_low) as i32 % 81);
    }

    let ring = Zn::new(625);
    let digit_extract = DigitExtract::new_default(5, 3, 2);
    for x in 0..625 {
        let (actual_high, actual_low) = digit_extract.evaluate(ring.int_hom().map(x), ring.can_hom(&StaticRing::<i64>::RING).unwrap());
        assert_eq!((x / 5) % 25, ring.smallest_positive_lift(actual_high) as i32 % 25);
        assert_eq!(x % 5, ring.smallest_positive_lift(actual_low) as i32 % 125);
    }
}
