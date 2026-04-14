use std::alloc::Global;

use feanor_math::algorithms::convolution::rns::{RNSConvolution, RNSConvolutionZn};
use feanor_math::algorithms::interpolate::interpolate;
use feanor_math::algorithms::linsolve::LinSolveRingStore;
use feanor_math::algorithms::multipointeval::multipointeval;
use feanor_math::divisibility::{DivisibilityRing, DivisibilityRingStore};
use feanor_math::homomorphism::{CanHomFrom, Homomorphism};
use feanor_math::matrix::OwnedMatrix;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::zn::{ZnRingStore, zn_64};
use feanor_math::seq::{VectorFn, VectorView};
use feanor_math::{algorithms::int_factor::is_prime_power, rings::extension::extension_impl::FreeAlgebraImpl};
use feanor_math::integer::{BigIntRing, BigIntRingBase, IntegerRingStore, int_cast};
use feanor_math::ring::*;
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use tracing::instrument;

use crate::{NiceZn, ZZbig, ZZi64};

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
use crate::digit_extract::polys::*;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;

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
