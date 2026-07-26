use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::assert_el_eq;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::IntegerRingStore;
use feanor_math::ring::{El, RingExtensionStore, RingStore};
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use feanor_math::rings::zn::*;

use crate::ZZi64;
use crate::circuit::{Coefficient, PlaintextCircuit};
use crate::number_ring::hypercube::isomorphism::BaseRing;

/// Returns the best arithmetic circuit that computes a function
/// ```text
///   digitex: Z/2^eZ -> (Z/2^eZ)^log(e)
/// ```
/// that satisfies `digitex(x)[i] = (x mod 2) mod 2^(2^i)`.
///
/// Uses a lookup-table, consisting mainly of the values from <https://ia.cr/2022/1364>, except for
/// `e > 8`, where there seemed to be a mistake in the paper.
pub fn precomputed_p_2<R>(Zpe: R) -> PlaintextCircuit<R::Type>
where
    R: RingStore,
    R::Type: ZnRing,
{
    let ring = &Zpe;
    let ZZ = Zpe.integer_ring();
    let e = ZZ.abs_log2_ceil(Zpe.modulus()).unwrap();
    assert_el_eq!(ZZ, ZZ.power_of_two(e), Zpe.modulus());
    assert!(e <= 23, "no precomputed tables are available for t > 2^23");
    let log2_e_ceil = ZZi64.abs_log2_ceil(&(e as i64)).unwrap();
    let lit = |x| ring.int_hom().map(x);

    let id = || PlaintextCircuit::linear_transform_ring(&[lit(1)], ring);
    let f0 = id().clone(ring);
    if log2_e_ceil == 0 {
        return f0;
    }

    let f1 = id()
        .tensor(PlaintextCircuit::square(ring), ring)
        .compose(PlaintextCircuit::select(1, &[0, 0], ring).compose(f0, ring), ring);
    if log2_e_ceil == 1 {
        return f1;
    }

    let f2 = id()
        .tensor(id(), ring)
        .tensor(PlaintextCircuit::square(ring), ring)
        .compose(PlaintextCircuit::select(2, &[0, 1, 1], ring).compose(f1, ring), ring);
    if log2_e_ceil == 2 {
        return f2;
    }

    let f3_comp = PlaintextCircuit::add(ring)
        .compose(
            PlaintextCircuit::linear_transform_ring(&[lit(112)], ring).tensor(
                PlaintextCircuit::square(ring).compose(
                    PlaintextCircuit::linear_transform_ring(&[lit(94), lit(121)], ring),
                    ring,
                ),
                ring,
            ),
            ring,
        )
        .compose(PlaintextCircuit::select(2, &[0, 0, 1], ring), ring);
    let f3 = id()
        .tensor(id(), ring)
        .tensor(id(), ring)
        .tensor(f3_comp, ring)
        .compose(PlaintextCircuit::select(3, &[0, 1, 2, 1, 2], ring), ring)
        .compose(f2, ring);
    if log2_e_ceil == 3 {
        return f3;
    }

    let f4_comp = PlaintextCircuit::add(ring)
        .compose(
            PlaintextCircuit::linear_transform_ring(&[lit(1984), lit(528), lit(22620)], ring).tensor(
                PlaintextCircuit::mul(ring).compose(
                    PlaintextCircuit::linear_transform_ring(&[lit(226), lit(113)], ring).tensor(
                        PlaintextCircuit::linear_transform_ring(&[lit(8), lit(2), lit(301)], ring),
                        ring,
                    ),
                    ring,
                ),
                ring,
            ),
            ring,
        )
        .compose(PlaintextCircuit::select(3, &[0, 1, 2, 1, 2, 0, 1, 2], ring), ring);
    let f4 = id()
        .tensor(id(), ring)
        .tensor(id(), ring)
        .tensor(id(), ring)
        .tensor(f4_comp, ring)
        .compose(PlaintextCircuit::select(4, &[0, 1, 2, 3, 1, 2, 3], ring), ring)
        .compose(f3, ring);
    if log2_e_ceil == 4 {
        return f4;
    }

    let f5_comp = PlaintextCircuit::add(ring)
        .compose(
            PlaintextCircuit::linear_transform_ring(&[lit(4849408), lit(3564625), lit(2737008), lit(6563608)], ring)
                .tensor(
                    PlaintextCircuit::mul(ring).compose(
                        PlaintextCircuit::linear_transform_ring(
                            &[lit(997183), lit(8295548), lit(419894), lit(879825)],
                            ring,
                        )
                        .tensor(
                            PlaintextCircuit::linear_transform_ring(
                                &[lit(443729), lit(555132), lit(491350), lit(758385)],
                                ring,
                            ),
                            ring,
                        ),
                        ring,
                    ),
                    ring,
                ),
            ring,
        )
        .compose(
            PlaintextCircuit::select(4, &[0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3], ring),
            ring,
        );
    let f5 = id()
        .tensor(id(), ring)
        .tensor(id(), ring)
        .tensor(id(), ring)
        .tensor(id(), ring)
        .tensor(f5_comp, ring)
        .compose(PlaintextCircuit::select(5, &[0, 1, 2, 3, 4, 1, 2, 3, 4], ring), ring)
        .compose(f4, ring);
    if log2_e_ceil == 5 {
        return f5;
    }
    unreachable!()
}

#[derive(PartialEq, Eq, Debug)]
pub enum Deg8PolyEvalError {
    InvalidDeg,
    NonUnitLC,
    Char2OddCoeff7,
    Char2NotSolvable,
}

pub fn degree_8_poly_circuit<R>(ZpeX: R, mut poly: El<R>) -> Result<PlaintextCircuit<BaseRing<R>>, Deg8PolyEvalError>
where
    R: RingStore,
    R::Type: PolyRing,
    BaseRing<R>: ZnRing,
{
    let Zpe = ZpeX.base_ring();
    let ZZ = Zpe.integer_ring();
    let (p, _e) = is_prime_power(ZZ, Zpe.modulus()).unwrap();
    if ZpeX.degree(&poly) != Some(8) {
        return Err(Deg8PolyEvalError::InvalidDeg);
    }
    let (lc, lc_inv) = if let Some(lc_inv) = Zpe.invert(ZpeX.lc(&poly).unwrap()) {
        (Zpe.clone_el(ZpeX.lc(&poly).unwrap()), lc_inv)
    } else {
        return Err(Deg8PolyEvalError::NonUnitLC);
    };
    ZpeX.inclusion().mul_assign_map(&mut poly, lc_inv);

    if ZZ.eq_el(&p, &ZZ.int_hom().map(2)) {
        // (x^2 + u x) x^2 = x^4 + u x^3
        // (x^4 + u x^3 + a2 x^2 + a1 x + a0)(x^4 + u x^3 + b2 x^2 + b1 x + b0) + c2 x^2 + c1 x + c0 =
        //     x^8 +
        //     2u x^7 +
        //     (u^2 + a2 + b2) x^6 +
        //     (u (a2 + b2) + (a1 + b1)) x^5 +
        //     (u (a1 + b1) + a2 b2 + (a0 + b0)) x^4 +
        //     (u (a0 + b0) + a2 b1 + b2 a1) x^3 +
        //     (b2 a0 + b1 a1 + b0 a2 + c2) x^2 +
        //     (a1 b0 + a0 b1 + c1) x +
        //     (a0 b0 + c0)
        let u = if let Some(u) = Zpe.checked_div(ZpeX.coefficient_at(&poly, 7), &Zpe.int_hom().map(2)) {
            u
        } else {
            return Err(Deg8PolyEvalError::Char2OddCoeff7);
        };
        // write A = a2 + b2, B = a1 + b1, C = a0 + b0 + a2 b2, D = u (a0 + b0) + a2 b1 + b2 a1
        let A = Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 6), Zpe.mul_ref(&u, &u));
        let B = Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 5), Zpe.mul_ref(&u, &A));
        let C = Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 4), Zpe.mul_ref(&u, &B));
        let D = Zpe.clone_el(ZpeX.coefficient_at(&poly, 3));

        // we have to find a zero of L := u x^2 + (B - uA) x - 2xy + Ay + uC - D;
        // we consider it over the 2-adic numbers to remove zero divisors, and find
        // 4L = g(g - 4y - 2B) - K, where g = 2x - A and K = u(A^2 - 4C) - 2(AB - 2D);
        // so the equation has a solution if there are g = A mod 2 and h = g - 2B mod 4 with K = gh
        //  - if A is odd: immediately solvable
        //  - if A even, B odd: solvable iff 8|K with g = 2 and h = K/2
        //  - if A even, B even: solvable iff K = 0, 4, 12 mod 16 (with g = 2 if K = 4, 12 mod 16 and g = 4
        //    otherwise)
        let K = Zpe.sum([
            Zpe.mul_ref_fst(&u, Zpe.mul_ref(&A, &A)),
            Zpe.int_hom().mul_map(Zpe.mul_ref(&C, &u), -4),
            Zpe.int_hom().mul_map(Zpe.mul_ref(&A, &B), -2),
            Zpe.int_hom().mul_ref_map(&D, &4),
        ]);
        let x = if Zpe.divides(&A, &Zpe.int_hom().map(2)) {
            let g = if Zpe.divides(&B, &Zpe.int_hom().map(2)) {
                match (
                    Zpe.divides(&K, &Zpe.int_hom().map(4)),
                    Zpe.divides(&K, &Zpe.int_hom().map(8)),
                    Zpe.divides(&K, &Zpe.int_hom().map(16)),
                ) {
                    (false, ..) => return Err(Deg8PolyEvalError::Char2NotSolvable),
                    (true, true, false) => return Err(Deg8PolyEvalError::Char2NotSolvable),
                    (true, true, true) => Zpe.int_hom().map(4),
                    (true, false, _) => Zpe.int_hom().map(2),
                }
            } else {
                if Zpe.divides(&K, &Zpe.int_hom().map(8)) {
                    Zpe.int_hom().map(2)
                } else {
                    return Err(Deg8PolyEvalError::Char2NotSolvable);
                }
            };
            Zpe.checked_div(&Zpe.sub_ref_fst(&A, g), &Zpe.int_hom().map(2)).unwrap()
        } else {
            Zpe.zero()
        };
        let y = Zpe
            .checked_div(
                &Zpe.sum([
                    Zpe.mul_ref_fst(&u, Zpe.mul_ref(&x, &x)),
                    Zpe.negate(Zpe.mul_ref_fst(&u, Zpe.mul_ref(&A, &x))),
                    Zpe.mul_ref(&B, &x),
                    Zpe.mul_ref(&u, &C),
                    Zpe.negate(D),
                ]),
                &Zpe.sub_ref_snd(Zpe.int_hom().mul_ref_map(&x, &2), &A),
            )
            .unwrap();

        let a2b2 = A;
        let a1b1 = B;
        let a2 = x;
        let b2 = Zpe.sub_ref(&a2b2, &a2);
        let a1 = y;
        let b1 = Zpe.sub_ref(&a1b1, &a1);
        let a0b0 = Zpe.sub_ref(&C, &Zpe.mul_ref(&a2, &b2));
        let a0 = a0b0;
        let b0 = Zpe.zero();
        let c2 = Zpe.sub(
            Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 2), Zpe.mul_ref(&b2, &a0)),
            Zpe.mul_ref(&b1, &a1),
        );
        let c1 = Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 1), Zpe.mul_ref(&b1, &a0));
        let c0 = Zpe.clone_el(ZpeX.coefficient_at(&poly, 0));

        let mut circuit = PlaintextCircuit::identity(1, Zpe)
            .tensor(PlaintextCircuit::square(Zpe), Zpe)
            .compose(PlaintextCircuit::identity(1, Zpe).output_twice(Zpe), Zpe);

        circuit = PlaintextCircuit::identity(2, Zpe)
            .tensor(
                PlaintextCircuit::mul(Zpe).compose(
                    PlaintextCircuit::linear_transform(
                        &[Coefficient::from_zn(Zpe.clone_el(&u), Zpe), Coefficient::One],
                        Zpe,
                    )
                    .tensor(PlaintextCircuit::select(2, &[1], Zpe), Zpe),
                    Zpe,
                ),
                Zpe,
            )
            .compose(circuit.output_times(3, Zpe), Zpe);
        let lhs = PlaintextCircuit::linear_transform(
            &[
                Coefficient::from_zn(a0, Zpe),
                Coefficient::from_zn(a1, Zpe),
                Coefficient::from_zn(a2, Zpe),
                Coefficient::One,
            ],
            Zpe,
        )
        .compose(
            PlaintextCircuit::one(Zpe).tensor(PlaintextCircuit::identity(3, Zpe), Zpe),
            Zpe,
        );
        let rhs = PlaintextCircuit::linear_transform(
            &[
                Coefficient::from_zn(b0, Zpe),
                Coefficient::from_zn(b1, Zpe),
                Coefficient::from_zn(b2, Zpe),
                Coefficient::One,
            ],
            Zpe,
        )
        .compose(
            PlaintextCircuit::one(Zpe).tensor(PlaintextCircuit::identity(3, Zpe), Zpe),
            Zpe,
        );
        circuit = PlaintextCircuit::mul(Zpe)
            .compose(lhs.tensor(rhs, Zpe), Zpe)
            .tensor(PlaintextCircuit::select(3, &[0, 1], Zpe), Zpe)
            .compose(circuit.output_times(3, Zpe), Zpe);
        circuit = PlaintextCircuit::linear_transform(
            &[
                Coefficient::One,
                Coefficient::from_zn(c1, Zpe),
                Coefficient::from_zn(c2, Zpe),
                Coefficient::from_zn(c0, Zpe),
            ],
            Zpe,
        )
        .compose(circuit.tensor(PlaintextCircuit::one(Zpe), Zpe), Zpe);
        circuit = PlaintextCircuit::linear_transform(&[Coefficient::from_zn(lc, Zpe)], Zpe).compose(circuit, Zpe);
        return Ok(circuit);
    } else {
        // (x^2 + u x) (x^2 + u x) = x^4 + 2u x^3 + u^2 x^2
        // (x^4 + 2u x^3 + a2 x^2 + a1 x + a0)(x^4 + 2u x^3 + b2 x^2 + b1 x + b0) + c2 x^2 + c1 x + c0 =
        //     x^8 +
        //     4u x^7 +
        //     (4u^2 + a2 + b2) x^6 +
        //     (2u (a2 + b2) + (a1 + b1)) x^5 +
        //     (2u (a1 + b1) + a2 b2 + (a0 + b0)) x^4 +
        //     (2u (a0 + b0) + a2 b1 + b2 a1) x^3 +
        //     (b2 a0 + b1 a1 + b0 a2 + c2) x^2 +
        //     (a1 b0 + a0 b1 + c1) x +
        //     (a0 b0 + c0)
        // b2 = 1 or 0
        let u = Zpe
            .checked_div(ZpeX.coefficient_at(&poly, 7), &Zpe.int_hom().map(4))
            .unwrap();
        let two_u = Zpe.add_ref(&u, &u);
        let a2b2 = Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 6), Zpe.mul_ref(&two_u, &two_u));
        let b2 = if Zpe.is_unit(&a2b2) {
            Zpe.zero()
        } else {
            debug_assert!(Zpe.is_unit(&Zpe.sub_ref_fst(&a2b2, Zpe.int_hom().map(2))));
            Zpe.one()
        };
        let a2 = Zpe.sub_ref(&a2b2, &b2);
        let a1b1 = Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 5), Zpe.mul_ref(&two_u, &a2b2));
        let a0b0 = Zpe.sub(
            Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 4), Zpe.mul_ref(&two_u, &a1b1)),
            Zpe.mul_ref(&a2, &b2),
        );
        debug_assert!(Zpe.is_unit(&Zpe.sub_ref(&b2, &a2)));
        let b1 = Zpe
            .checked_div(
                &Zpe.sub(
                    Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 3), Zpe.mul_ref(&two_u, &a0b0)),
                    Zpe.mul_ref(&a1b1, &b2),
                ),
                &Zpe.sub_ref(&a2, &b2),
            )
            .unwrap();
        let a1 = Zpe.sub_ref(&a1b1, &b1);
        debug_assert!(Zpe.eq_el(
            ZpeX.coefficient_at(&poly, 3),
            &Zpe.sum([Zpe.mul_ref(&two_u, &a0b0), Zpe.mul_ref(&a1, &b2), Zpe.mul_ref(&a2, &b1)])
        ));
        let a0 = a0b0;
        let b0 = Zpe.zero();
        let c2 = Zpe.sub(
            Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 2), Zpe.mul_ref(&b2, &a0)),
            Zpe.mul_ref(&b1, &a1),
        );
        let c1 = Zpe.sub_ref_fst(ZpeX.coefficient_at(&poly, 1), Zpe.mul_ref(&b1, &a0));
        let c0 = Zpe.clone_el(ZpeX.coefficient_at(&poly, 0));

        let mut circuit = PlaintextCircuit::identity(1, Zpe)
            .tensor(PlaintextCircuit::square(Zpe), Zpe)
            .compose(PlaintextCircuit::identity(1, Zpe).output_twice(Zpe), Zpe);
        circuit = PlaintextCircuit::identity(2, Zpe)
            .tensor(
                PlaintextCircuit::square(Zpe).compose(
                    PlaintextCircuit::linear_transform(
                        &[Coefficient::from_zn(Zpe.clone_el(&u), Zpe), Coefficient::One],
                        Zpe,
                    ),
                    Zpe,
                ),
                Zpe,
            )
            .compose(circuit.output_twice(Zpe), Zpe);
        let lhs = PlaintextCircuit::linear_transform(
            &[
                Coefficient::from_zn(a0, Zpe),
                Coefficient::from_zn(a1, Zpe),
                Coefficient::from_zn(Zpe.sub(a2, Zpe.mul_ref(&u, &u)), Zpe),
                Coefficient::One,
            ],
            Zpe,
        )
        .compose(
            PlaintextCircuit::one(Zpe).tensor(PlaintextCircuit::identity(3, Zpe), Zpe),
            Zpe,
        );
        let rhs = PlaintextCircuit::linear_transform(
            &[
                Coefficient::from_zn(b0, Zpe),
                Coefficient::from_zn(b1, Zpe),
                Coefficient::from_zn(Zpe.sub(b2, Zpe.mul_ref(&u, &u)), Zpe),
                Coefficient::One,
            ],
            Zpe,
        )
        .compose(
            PlaintextCircuit::one(Zpe).tensor(PlaintextCircuit::identity(3, Zpe), Zpe),
            Zpe,
        );
        circuit = PlaintextCircuit::mul(Zpe)
            .compose(lhs.tensor(rhs, Zpe), Zpe)
            .tensor(PlaintextCircuit::select(3, &[0, 1], Zpe), Zpe)
            .compose(circuit.output_times(3, Zpe), Zpe);
        circuit = PlaintextCircuit::linear_transform(
            &[
                Coefficient::One,
                Coefficient::from_zn(c1, Zpe),
                Coefficient::from_zn(c2, Zpe),
                Coefficient::from_zn(c0, Zpe),
            ],
            Zpe,
        )
        .compose(circuit.tensor(PlaintextCircuit::one(Zpe), Zpe), Zpe);
        circuit = PlaintextCircuit::linear_transform(&[Coefficient::from_zn(lc, Zpe)], Zpe).compose(circuit, Zpe);
        return Ok(circuit);
    }
}

#[cfg(test)]
use feanor_math::rings::finite::FiniteRingStore;
#[cfg(test)]
use feanor_math::rings::poly::dense_poly::DensePolyRing;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;

#[test]
#[ignore]
fn test_digit_extraction_p_2_complete() {
    feanor_tracing::DelayedLogger::init_test();
    let ring = Zn::new(1 << 23);
    let circuit = precomputed_p_2(ring);
    let hom = ring.can_hom(&ZZi64).unwrap();
    for x in 0..(1 << 23) {
        for (e, actual) in [1, 2, 4, 8, 16, 23]
            .into_iter()
            .zip(circuit.evaluate_no_galois(&[hom.map(x)], ring.identity()))
        {
            assert_eq!(x % 2, ring.smallest_positive_lift(actual) % (1 << e));
        }
    }
}

#[test]
fn test_digit_extraction_p_2() {
    feanor_tracing::DelayedLogger::init_test();
    let ring = Zn::new(1 << 17);
    let circuit = precomputed_p_2(ring);
    let hom = ring.can_hom(&ZZi64).unwrap();
    for x in 0..(1 << 17) {
        for (e, actual) in [1, 2, 4, 8, 16, 17]
            .into_iter()
            .zip(circuit.evaluate_no_galois(&[hom.map(x)], ring.identity()))
        {
            assert_eq!(x % 2, ring.smallest_positive_lift(actual) % (1 << e));
        }
    }
}

#[test]
fn test_degree_8_poly() {
    feanor_tracing::DelayedLogger::init_test();
    let Zpe = Zn::new(81);
    let ZpeX = DensePolyRing::new(Zpe, "X");
    let [f] = ZpeX.with_wrapped_indeterminate(|X| {
        [X.pow_ref(8) + 9 * X.pow_ref(7) + 5 * X.pow_ref(6) - 3 * X.pow_ref(4) + X.pow_ref(3) + X + 10]
    });
    let circuit = degree_8_poly_circuit(&ZpeX, ZpeX.clone_el(&f)).unwrap();
    for x in Zpe.elements() {
        assert_el_eq!(
            Zpe,
            ZpeX.evaluate(&f, &x, Zpe.identity()),
            circuit.evaluate_no_galois(&[x], Zpe.identity()).pop().unwrap()
        );
    }
}

#[test]
fn test_degree_8_poly_even_char() {
    feanor_tracing::DelayedLogger::init_test();
    let Zpe = Zn::new(256);
    let ZpeX = DensePolyRing::new(Zpe, "X");
    let [f1, f2, f3, f4] = ZpeX.with_wrapped_indeterminate(|X| {
        [
            X.pow_ref(8) + 2 * X.pow_ref(7) + 2 * X.pow_ref(6) + 4 * X.pow_ref(3) + 1,
            X.pow_ref(8) + 2 * X.pow_ref(7) + X.pow_ref(6) + 4 * X.pow_ref(3) + 1,
            X.pow_ref(8) + X.pow_ref(7) + X.pow_ref(6) + 4 * X.pow_ref(3) + 1,
            X.pow_ref(8) + 6 * X.pow_ref(7) + 3 * X.pow_ref(6) + 2 * X.pow_ref(5) + 7 * X.pow_ref(4) + 2 * X + 1,
        ]
    });
    let circuit = degree_8_poly_circuit(&ZpeX, ZpeX.clone_el(&f1)).unwrap();
    for x in Zpe.elements() {
        assert_el_eq!(
            Zpe,
            ZpeX.evaluate(&f1, &x, Zpe.identity()),
            circuit.evaluate_no_galois(&[x], Zpe.identity()).pop().unwrap()
        );
    }

    let circuit = degree_8_poly_circuit(&ZpeX, ZpeX.clone_el(&f2)).unwrap();
    for x in Zpe.elements() {
        assert_el_eq!(
            Zpe,
            ZpeX.evaluate(&f2, &x, Zpe.identity()),
            circuit.evaluate_no_galois(&[x], Zpe.identity()).pop().unwrap()
        );
    }

    assert_eq!(
        Deg8PolyEvalError::Char2OddCoeff7,
        degree_8_poly_circuit(&ZpeX, ZpeX.clone_el(&f3)).err().unwrap()
    );
    assert_eq!(
        Deg8PolyEvalError::Char2NotSolvable,
        degree_8_poly_circuit(&ZpeX, ZpeX.clone_el(&f4)).err().unwrap()
    );
}
