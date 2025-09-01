use std::alloc::Global;

use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::algorithms::interpolate::interpolate;
use feanor_math::divisibility::*;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::{int_cast, BigIntRing, IntegerRingStore};
use feanor_math::primitive_int::{StaticRing, StaticRingBase};
use feanor_math::ring::*;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::zn::zn_64::Zn;
use feanor_math::seq::*;
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use feanor_math::rings::zn::{zn_64, ZnRing, ZnRingStore};

use crate::circuit::{Coefficient, PlaintextCircuit};
use crate::digit_extract::paterson_stockmeyer::paterson_stockmeyer_circuit;
use crate::ZZi64;

type IntegerCircuit = PlaintextCircuit<StaticRingBase<i64>>;

const ZZ: StaticRing<i64> = StaticRing::RING;

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
pub fn precomputed_p_2(e: usize) -> IntegerCircuit {
    assert!(e <= 23, "no precomputed tables are available for t > 2^23");
    let log2_e_ceil = StaticRing::<i64>::RING.abs_log2_ceil(&(e as i64)).unwrap();
    
    let id = || IntegerCircuit::linear_transform_ring(&[1], ZZ);
    let f0 = id().clone(ZZ);
    if log2_e_ceil == 0 {
        return f0;
    }

    let f1 = id().tensor(IntegerCircuit::square(ZZ), ZZ).compose(IntegerCircuit::select(1, &[0, 0], ZZ).compose(f0, ZZ), ZZ);
    if log2_e_ceil == 1 {
        return f1;
    }

    let f2 = id().tensor(id(), ZZ).tensor(IntegerCircuit::square(ZZ), ZZ).compose(IntegerCircuit::select(2, &[0, 1, 1], ZZ).compose(f1, ZZ), ZZ);
    if log2_e_ceil == 2 {
        return f2;
    }
    
    let f3_comp = IntegerCircuit::add(ZZ).compose(
        IntegerCircuit::linear_transform_ring(&[112], ZZ).tensor(IntegerCircuit::square(ZZ).compose(
            IntegerCircuit::linear_transform_ring(&[94, 121], ZZ), ZZ
        ), ZZ), ZZ
    ).compose(
        IntegerCircuit::select(2, &[0, 0, 1], ZZ), ZZ
    );
    let f3 = id().tensor(id(), ZZ).tensor(id(), ZZ).tensor(f3_comp, ZZ).compose(
        IntegerCircuit::select(3, &[0, 1, 2, 1, 2], ZZ), ZZ
    ).compose(f2, ZZ);
    if log2_e_ceil == 3 {
        return f3;
    }

    let f4_comp = IntegerCircuit::add(ZZ).compose(
        IntegerCircuit::linear_transform_ring(&[1984, 528, 22620], ZZ).tensor(IntegerCircuit::mul(ZZ).compose(
            IntegerCircuit::linear_transform_ring(&[226, 113], ZZ).tensor(IntegerCircuit::linear_transform_ring(&[8, 2, 301], ZZ), ZZ), ZZ
        ), ZZ), ZZ
    ).compose(
        IntegerCircuit::select(3, &[0, 1, 2, 1, 2, 0, 1, 2], ZZ), ZZ
    );
    let f4 = id().tensor(id(), ZZ).tensor(id(), ZZ).tensor(id(), ZZ).tensor(f4_comp, ZZ).compose(
        IntegerCircuit::select(4, &[0, 1, 2, 3, 1, 2, 3], ZZ), ZZ
    ).compose(f3, ZZ);
    if log2_e_ceil == 4 {
        return f4;
    }

    let f5_comp = IntegerCircuit::add(ZZ).compose(
        IntegerCircuit::linear_transform_ring(&[4849408, 3564625, 2737008, 6563608], ZZ).tensor(IntegerCircuit::mul(ZZ).compose(
            IntegerCircuit::linear_transform_ring(&[997183, 8295548, 419894, 879825], ZZ).tensor(IntegerCircuit::linear_transform_ring(&[443729, 555132, 491350, 758385], ZZ), ZZ), ZZ
        ), ZZ), ZZ
    ).compose(
        IntegerCircuit::select(4, &[0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3], ZZ), ZZ
    );
    let f5 = id().tensor(id(), ZZ).tensor(id(), ZZ).tensor(id(), ZZ).tensor(id(), ZZ).tensor(f5_comp, ZZ).compose(
        IntegerCircuit::select(5, &[0, 1, 2, 3, 4, 1, 2, 3, 4], ZZ), ZZ
    ).compose(f4, ZZ);
    if log2_e_ceil == 5 {
        return f5;
    }
    unreachable!()
}

///
/// Heuristically chooses a low-depth, low-complexity circuit that
/// evaluates all the given univariate polynomials.
/// 
/// Currently, this function uses [`paterson_stockmeyer::paterson_stockmeyer_circuit()`].
/// 
pub fn poly_to_circuit<P>(poly_ring: P, polys: &[El<P>]) -> IntegerCircuit
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing + DivisibilityRing
{
    let mut polynomials = Vec::new();
    for f in polys {
        let lc = poly_ring.lc(f).unwrap();
        if !poly_ring.base_ring().is_unit(lc) {
            let d = poly_ring.degree(f).unwrap();
            let c_X_d = poly_ring.from_terms([(poly_ring.base_ring().sub_ref_fst(lc, poly_ring.base_ring().one()), d)]);
            polynomials.push(poly_ring.sub_ref(f, &c_X_d));
            polynomials.push(c_X_d);
        } else {
            polynomials.push(poly_ring.clone_el(f));
        }
    }
    let result = paterson_stockmeyer_circuit(&poly_ring, &polynomials).change_ring_uniform(|x| 
        Coefficient::from(int_cast(poly_ring.base_ring().smallest_lift(x.to_ring_el(poly_ring.base_ring())), ZZi64, poly_ring.base_ring().integer_ring()), ZZi64)
    );
    let mut recombine = PlaintextCircuit::empty();
    for f in polys {
        if !poly_ring.base_ring().is_unit(&poly_ring.lc(f).unwrap()) {
            recombine = recombine.tensor(PlaintextCircuit::add(ZZi64), ZZi64);
        } else {
            recombine = recombine.tensor(PlaintextCircuit::identity(1, ZZi64), ZZi64);
        }
    }

    return recombine.compose(result, ZZi64);
}

fn digit_extraction_poly<P>(poly_ring: P) -> El<P>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing + DivisibilityRing
{
    let Zn = poly_ring.base_ring();
    let (p, e) = is_prime_power(Zn.integer_ring(), Zn.modulus()).unwrap();
    let p = int_cast(p, StaticRing::<i64>::RING, Zn.integer_ring()) as usize;
    let hom = Zn.can_hom(Zn.integer_ring()).unwrap().compose(Zn.integer_ring().can_hom(&StaticRing::<i64>::RING).unwrap());
    let mut current = poly_ring.pow(poly_ring.indeterminate(), p);
    for i in 1..e {
        let mut correction = interpolate(
            &poly_ring, 
            (0..p).map_fn(|j| hom.map(j as i64)), 
            (0..p).map_fn(|j| Zn.checked_div(
                &Zn.sub(poly_ring.evaluate(&current, &hom.map(j as i64), &Zn.identity()), hom.map(j as i64)), 
                &Zn.pow(hom.map(p as i64), i as usize)
            ).unwrap()),
            Global
        ).unwrap();
        poly_ring.inclusion().mul_assign_ref_map(&mut correction, &Zn.pow(hom.map(p as i64), i as usize));
        poly_ring.sub_assign(&mut current, correction);
    }
    return current;
}

pub fn basic_digit_extract_circuit(p: i64, e: usize) -> IntegerCircuit {
    let poly_ring = DensePolyRing::new(zn_64::Zn::new(StaticRing::<i64>::RING.pow(p, e) as u64), "X");
    let f = digit_extraction_poly(&poly_ring);
    let f_circuit = poly_to_circuit(&poly_ring, std::slice::from_ref(&f));
    let mut result = IntegerCircuit::identity(1, ZZ);
    for i in 1..e {
        result = IntegerCircuit::identity(i, ZZ).tensor(f_circuit.clone(ZZ).compose(IntegerCircuit::select(i, &[i - 1], ZZ), ZZ), ZZ).compose(result.output_twice(ZZ), ZZ);
    }
    return IntegerCircuit::select(e, &(1..e).collect::<Vec<_>>(), ZZ).compose(result, ZZ);
}

///
/// Computes `min { n | n! % k == 0 }`
/// 
pub fn mu(k: i64) -> i64 {
    const ZZbig: BigIntRing = BigIntRing::RING;
    let mut n = 1;
    let mut n_fac = ZZbig.one();
    while ZZbig.checked_div(&n_fac, &int_cast(k, &ZZbig, &StaticRing::<i64>::RING)).is_none() {
        n += 1;
        ZZbig.mul_assign(&mut n_fac, int_cast(n, &ZZbig, &StaticRing::<i64>::RING));
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

///
/// Returns the lowest-degree polynomial `f` such that `f(x) = lift(x mod p) mod p^k`.
/// 
pub fn digit_retain_poly<P>(poly_ring: P, k: usize) -> El<P>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing + DivisibilityRing
{
    assert!(k > 0);
    if k == 1 {
        return poly_ring.indeterminate();
    }
    let Zn = poly_ring.base_ring();
    let hom = Zn.can_hom(Zn.integer_ring()).unwrap().compose(Zn.integer_ring().can_hom(&StaticRing::<i64>::RING).unwrap());
    let (p, e) = is_prime_power(Zn.integer_ring(), Zn.modulus()).unwrap();
    assert!(e >= k);
    let p = int_cast(p, StaticRing::<i64>::RING, Zn.integer_ring());
    let mut current = poly_ring.evaluate(&digit_extraction_poly(&poly_ring), &digit_retain_poly(poly_ring, k - 1), &poly_ring.inclusion());

    let mut current_e = 0;
    while Zn.checked_div(poly_ring.lc(&current).unwrap(), &Zn.pow(hom.map(p), current_e)).is_some() {
        let null_poly = poly_ring.inclusion().mul_map(
            falling_factorial_poly(&poly_ring, mu(StaticRing::<i64>::RING.pow(p, k - current_e)) as usize),
            Zn.pow(hom.map(p), current_e)
        );
        while let Some(quo) = Zn.checked_div(poly_ring.lc(&current).unwrap(), &poly_ring.lc(&null_poly).unwrap()) {
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

pub fn digit_retain_circuit(p: i64, k: usize) -> IntegerCircuit {
    // following idea: if `f(x)` is the digit retain poly mod `p^(k - 1)`, and
    // `f'(x)` is the digit retain poly mod `p^k`, then `p(f' - f)` is a null poly
    // modulo `p^k`; however, since `f'` has degree smaller than the smallest
    // null-poly mod `p^k`, we know that `p` divides `f' - f`; now compute
    // `f` and `(f' - f)/p`, then combine it
    let ZnX = DensePolyRing::new(Zn::new(ZZi64.pow(p, k) as u64), "X");
    let p_zn = ZnX.base_ring().coerce(&ZZi64, p);
    let mut polys = vec![digit_extraction_poly(&ZnX)];
    let mut last_poly = ZnX.clone_el(polys.last().unwrap());
    for i in 3..=k {
        let retain_poly = digit_retain_poly(&ZnX, i);
        println!("{}", i);
        ZnX.println(&retain_poly);
        ZnX.println(&last_poly);
        let next_poly = ZnX.from_terms(ZnX.terms(&ZnX.sub_ref(&retain_poly, &last_poly)).map(|(c, d)| (
            ZnX.base_ring().checked_div(c, &p_zn).unwrap(), d
        )));
        polys.push(next_poly);
        last_poly = retain_poly;
    }
    let main_circuit = paterson_stockmeyer_circuit(&ZnX, &polys).change_ring_uniform(|x| 
        Coefficient::from(int_cast(ZnX.base_ring().smallest_lift(x.to_ring_el(ZnX.base_ring())), ZZi64, ZnX.base_ring().integer_ring()), ZZi64)
    );
    let mut result = main_circuit;
    for i in 2..k {
        result = PlaintextCircuit::identity(i - 2, ZZi64).tensor(
            PlaintextCircuit::identity(1, ZZi64).tensor(PlaintextCircuit::linear_transform_ring(&[1, p], ZZi64), ZZi64).compose(
                PlaintextCircuit::select(2, &[0, 0, 1], ZZi64), ZZi64
            ), ZZi64
        ).tensor(PlaintextCircuit::identity(k - i - 1, ZZi64), ZZi64).compose(result, ZZi64);
    }
    assert_eq!(k - 1, result.output_count());
    return result;
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::finite::FiniteRingStore;

#[test]
fn print_digit_extract_poly() {
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let f0 = digit_retain_poly(&P, 2);
    let f1 = digit_retain_poly(&P, 3);
    P.println(&f1);
    P.println(&f0);
    P.println(&P.sub_ref(&f1, &f0));
}

#[test]
#[ignore]
fn test_digit_extraction_p_2_complete() {
    let circuit = precomputed_p_2(23);
    let ring = Zn::new(1 << 23);
    let hom = ring.can_hom(&ZZ).unwrap();
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
    let hom = ring.can_hom(&StaticRing::<i64>::RING).unwrap();
    for x in 0..(1 << 17) {
        for (e, actual) in [1, 2, 4, 8, 16, 17].into_iter().zip(circuit.evaluate_no_galois(&[hom.map(x)], &hom)) {
            assert_eq!(x % 2, ring.smallest_positive_lift(actual) % (1 << e));
        }
    }
}

#[test]
fn test_digit_extraction_poly() {
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = digit_extraction_poly(&P);
    for k in 0..(17 * 17 * 17) {
        assert_eq!(k % 17, Zn.smallest_positive_lift(P.evaluate(&digit_extract, &Zn.coerce(&StaticRing::<i64>::RING, k), &Zn.identity())) % (17 * 17));
    }
    for k_low in 0..17 {
        for k_high in (0..(17 * 17 * 17)).step_by(17 * 17) {
            assert_el_eq!(&Zn, &Zn.coerce(&StaticRing::<i64>::RING, k_low), &P.evaluate(&digit_extract, &Zn.coerce(&StaticRing::<i64>::RING, k_low + k_high), &Zn.identity()));
        }
    }
}

#[test]
fn test_digit_retain_poly() {
    let Zn = Zn::new(1024);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    assert_eq!(Some(3), P.degree(&digit_retain));
    for k in 0..1024 {
        assert_eq!(k % 2, Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&StaticRing::<i64>::RING, k), &Zn.identity())) % 8);
    }
    let digit_retain = digit_retain_poly(&P, 6);
    assert_eq!(Some(6), P.degree(&digit_retain));
    for k in 0..1024 {
        assert_eq!(k % 2, Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&StaticRing::<i64>::RING, k), &Zn.identity())) % 64);
    }

    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    assert_eq!(Some(33), P.degree(&digit_retain));
    for k in 0..(17 * 17 * 17) {
        assert_el_eq!(&Zn, &Zn.coerce(&StaticRing::<i64>::RING, k % 17), &P.evaluate(&digit_retain, &Zn.coerce(&StaticRing::<i64>::RING, k), &Zn.identity()));
    }
    
    let Zn = Zn::new(257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 2);
    assert_eq!(Some(257), P.degree(&digit_retain));
    for k in 0..257 {
        assert_el_eq!(&Zn, &Zn.coerce(&StaticRing::<i64>::RING, 2), &P.evaluate(&digit_retain, &Zn.coerce(&StaticRing::<i64>::RING, 2 + k * 257), &Zn.identity()));
    }
}

#[test]
fn test_digit_retain_circuit() {
    let Zn = Zn::new(17 * 17 * 17);
    let hom = Zn.can_hom(&ZZi64).unwrap();
    let circuit = digit_retain_circuit(17, 3);
    assert_eq!(2, circuit.output_count());
    for k in 0..(17 * 17 * 17) {
        assert_eq!(k % 17, Zn.smallest_positive_lift(circuit.evaluate_no_galois(&[hom.map(k)], &hom)[0]) % (17 * 17));
        assert_eq!(k % 17, Zn.smallest_positive_lift(circuit.evaluate_no_galois(&[hom.map(k)], &hom)[1]));
    }
}

#[test]
#[ignore]
fn test_digit_retain_poly_large() {
    let Zn = Zn::new(257 * 257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    assert_el_eq!(&Zn, &Zn.coerce(&StaticRing::<i64>::RING, 251), &P.evaluate(&digit_retain, &Zn.coerce(&StaticRing::<i64>::RING, 132092), &Zn.identity()));
    for k in 0..(257 * 257) {
        assert_el_eq!(&Zn, &Zn.coerce(&StaticRing::<i64>::RING, 2), &P.evaluate(&digit_retain, &Zn.coerce(&StaticRing::<i64>::RING, 2 + k * 257), &Zn.identity()));
    }
}

#[test]
fn test_poly_to_circuit() {
    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    // 1 + 2 X^3 + 3 X^4 + 4 X^5 + 8 X^7
    let poly = P.from_terms([(1, 0), (2, 3), (3, 4), (4, 5), (8, 7)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = poly_to_circuit(&P, &[P.clone_el(&poly)]);
    assert_eq!(3, circuit.max_mul_depth());
    assert_eq!(4, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        assert_el_eq!(Zn, P.evaluate(&poly, &x, &P.base_ring().identity()), circuit.evaluate_no_galois(&[x], P.base_ring().can_hom(&ZZ).unwrap()).into_iter().next().unwrap());
    }
}

#[test]
fn test_poly_to_circuit_multiple_polys() {
    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    // 1 + 2 X^3 + 3 X^4 + 4 X^5 + 8 X^7
    let f = P.from_terms([(1, 0), (2, 3), (3, 4), (4, 5), (8, 7)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    // 2 + X + 2 X^2 + 3 X^3 + 4 X^4 + 5 X^5 + 6 X^6 + 7 X^7 + 8 X^8 + 9 X^9
    let g = P.from_terms([(2, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = poly_to_circuit(&P, &[P.clone_el(&f), P.clone_el(&g)]);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(6, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZ).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }

    // 1 + X^12
    let h = P.from_terms([(1, 0), (3, 6), (7, 9), (1, 12)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = poly_to_circuit(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h)]);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(4, circuit.mul_depth(2));
    assert_eq!(8, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZ).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }

    // 1 + X + X^2 + ... + X^15 + X^16
    let l = P.from_terms((0..=16).map(|i| (Zn.one(), i)));
    let circuit = poly_to_circuit(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h), P.clone_el(&l)]);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(4, circuit.mul_depth(2));
    assert_eq!(4, circuit.mul_depth(3));
    assert_eq!(10, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZ).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&l, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }
}

#[test]
fn test_best_circuit_multiple_polys() {
    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let f = P.from_terms([(1, 0), (2, 3), (3, 4), (4, 5), (8, 7)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let g = P.from_terms([(2, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let h = P.from_terms([(1, 0), (3, 6), (7, 9), (1, 12)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = poly_to_circuit(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h)]);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(4, circuit.mul_depth(2));
    assert_eq!(8, circuit.multiplication_gate_count());
    
    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZ).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }

    let l = P.from_terms((0..=16).map(|i| (Zn.one(), i)));
    let circuit = poly_to_circuit(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h), P.clone_el(&l)]);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(4, circuit.mul_depth(2));
    assert_eq!(4, circuit.mul_depth(3));
    assert_eq!(10, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZ).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&l, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }
}