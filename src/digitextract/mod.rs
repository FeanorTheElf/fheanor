
use feanor_math::algorithms::miller_rabin::is_prime;
use feanor_math::divisibility::*;
use feanor_math::primitive_int::{StaticRing, StaticRingBase};
use feanor_math::ring::*;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::zn::zn_64::Zn;
use feanor_math::homomorphism::*;
use polys::{digit_retain_poly, poly_to_circuit, precomputed_p_2};
use tracing::instrument;

use crate::circuit::PlaintextCircuit;

pub mod polys;

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
    p: i64
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
        return Self::new_with(
            p, 
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
            let circuit = poly_to_circuit(&poly_ring, &required_digits.iter().map(|j| digit_retain_poly(&poly_ring, *j)).collect::<Vec<_>>());
            return (required_digits, circuit);
        }).collect::<Vec<_>>();
        assert!(digit_extraction_circuits.is_sorted_by_key(|(digits, _)| *digits.last().unwrap()));
        
        return Self::new_with(p, e, r, StaticRing::<i64>::RING, digit_extraction_circuits);
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
    pub fn new_with<S: Copy + RingStore<Type = R>>(p: i64, e: usize, r: usize, ring: S, extraction_circuits: Vec<(Vec<usize>, PlaintextCircuit<R>)>) -> Self {
        assert!(is_prime(&StaticRing::<i64>::RING, &p, 10));
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

    pub fn p(&self) -> i64 {
        self.p
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
    /// division can be done much easier with [`feanor_math::pid::EuclideanRing::euclidean_div_rem()`]
    /// when you have access to the ring elements.
    /// 
    /// This function does not perform any checks on the underlying ring, in particular, you can
    /// call it on an input in `Z/p^e'Z` with `e' > e` or an input in `Z`. Of course, in any case,
    /// the output will only be correct modulo `p^r` resp. `p^e`.
    /// 
    pub fn evaluate<H, S>(&self, input: S::Element, hom: H) -> (S::Element, S::Element)
        where H: Homomorphism<R, S>,
            S: ?Sized + RingBase + DivisibilityRing
    {
        let p = hom.codomain().int_hom().map(self.p as i32);
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

#[cfg(test)]
use feanor_math::rings::zn::ZnRingStore;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::divisibility::DivisibilityRingStore;
#[cfg(test)]
use feanor_math::rings::extension::FreeAlgebraStore;
#[cfg(test)]
use feanor_math::seq::VectorFn;
#[cfg(test)]
use rand::SeedableRng;
#[cfg(test)]
use rand::rngs::StdRng;
#[cfg(test)]
use crate::bfv::*;
#[cfg(test)]
use crate::DefaultNegacyclicNTT;
#[cfg(test)]
use std::alloc::Global;
#[cfg(test)]
use std::marker::PhantomData;

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
fn test_digit_extract_homomorphic() {
    let mut rng = StdRng::from_seed([1; 32]);
    
    let params = Pow2BFV {
        log2_q_min: 500,
        log2_q_max: 520,
        log2_N: 6,
        ciphertext_allocator: Global,
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };
    let digits = 3;
    
    let P1 = params.create_plaintext_ring(17 * 17);
    let P2 = params.create_plaintext_ring(17 * 17 * 17);
    let (C, C_mul) = params.create_ciphertext_rings();

    let sk = Pow2BFV::gen_sk(&C, &mut rng, None);
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, digits);

    let m = P2.int_hom().map(17 * 17 + 2 * 17 + 5);
    let ct = Pow2BFV::enc_sym(&P2, &C, &mut rng, &m, &sk);

    let digitextract = DigitExtract::new_default(17, 2, 1);

    let (ct_high, ct_low) = digitextract.evaluate_bfv::<Pow2BFV>(&P1, std::slice::from_ref(&P2), &C, &C_mul, ct, &rk);

    let m_high = Pow2BFV::dec(&P1, &C, Pow2BFV::clone_ct(&C, &ct_high), &sk);
    assert!(P1.wrt_canonical_basis(&m_high).iter().skip(1).all(|x| P1.base_ring().is_zero(&x)));
    let m_high = P1.base_ring().smallest_positive_lift(P1.wrt_canonical_basis(&m_high).at(0));
    assert_eq!(2, m_high % 17);

    let m_low = Pow2BFV::dec(&P2, &C, Pow2BFV::clone_ct(&C, &ct_low), &sk);
    assert!(P1.wrt_canonical_basis(&m_low).iter().skip(1).all(|x| P2.base_ring().is_zero(&x)));
    let m_low = P1.base_ring().smallest_positive_lift(P1.wrt_canonical_basis(&m_low).at(0));
    assert_eq!(5, m_low % (17 * 17));
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
