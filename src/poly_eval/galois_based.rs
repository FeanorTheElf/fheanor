use feanor_math::algorithms::int_factor::{factor, is_prime_power};
use feanor_math::algorithms::poly_factor::FactorPolyField;
use feanor_math::divisibility::{DivisibilityRing, DivisibilityRingStore};
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::{BigIntRing, IntegerRingStore, int_cast};
use feanor_math::iters::multiset_combinations;
use feanor_math::ring::*;
use feanor_math::rings::extension::{FreeAlgebra, FreeAlgebraStore};
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
use feanor_math::rings::field::AsField;
use feanor_math::rings::finite::{FiniteRing, FiniteRingStore};
use feanor_math::rings::poly::{PolyRing, PolyRingStore, derive_poly};
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::zn::{ZnReductionMap, ZnRing, ZnRingStore, zn_big};
use feanor_math::seq::{VectorFn, VectorViewMut};
use feanor_math::seq::sparse::SparseMapVector;
use tracing::instrument;

use crate::number_ring::*;
use crate::poly_eval::to_circuit::compute_powers_circuit;
use crate::{NiceZn, ZZbig, ZZi64};
use crate::circuit::{Coefficient, PlaintextCircuit};
use crate::lin_transform::trace::norm_circuit;
use crate::number_ring::galois::{CyclotomicGaloisGroup, CyclotomicGaloisGroupBase, CyclotomicGaloisGroupOps, GaloisGroupEl};
use crate::number_ring::hypercube::isomorphism::*;

fn divisors(n: i64) -> Vec<i64> {
    let (primes, max_exponents) = factor(&ZZi64, n as i64).into_iter().unzip::<_, _, Vec<_>, Vec<_>>();
    let mut result = Vec::new();
    fn multiply_product(exponents: &[usize], primes: &[i64]) -> i64 {
        ZZi64.prod(primes.iter().zip(exponents).map(|(p, e)| ZZi64.pow(*p, *e)))
    }
    for size in 0..=max_exponents.iter().copied().sum() {
        result.extend(multiset_combinations(&max_exponents, size, |exponents| multiply_product(exponents, &primes)));
    }
    return result;
}

///
/// Assuming `monic_poly + delta` is irreducible of degree `d` modulo `p`, and `d` divides the rank of the ring `S`,
/// then this constructs a circuit that evaluates `monic_poly` using the norm in a Galois subring of `S`.
/// 
/// The resulting circuit has the final evaluation as last output. Earlier outputs are `1, x, x^2, x^4, x^8, ...`.
/// 
#[instrument(skip_all)]
fn compute_circuit_from_irreducible_poly<P, R>(
    FpX: &DensePolyRing<AsField<zn_big::Zn<BigIntRing>>>, 
    ZpeX: P, 
    monic_poly: &El<P>, 
    delta: &El<P>, 
    S: R, 
    parent_galois_group: &CyclotomicGaloisGroup, 
    frobenius: GaloisGroupEl
) -> PlaintextCircuit<<R as RingStore>::Type>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        BaseRing<P>: ZnRing + DivisibilityRing,
        R: RingStore,
        R::Type: FreeAlgebra + FiniteRing + DivisibilityRing,
        BaseRing<R>: ZnRing
{
    let d = ZpeX.degree(monic_poly).unwrap();
    let Zpe = ZpeX.base_ring();
    let (_, e) = is_prime_power(Zpe.integer_ring(), Zpe.modulus()).unwrap();
    let Fp = FpX.base_ring();
    let Sbase_to_Fp = ZnReductionMap::new(S.base_ring(), Fp).unwrap();
    let Zpe_to_Sbase = ZnReductionMap::new(Zpe, S.base_ring()).unwrap();
    let Zpe_to_Fp = (&Sbase_to_Fp).compose(&Zpe_to_Sbase);
    let irred_poly = ZpeX.add_ref(monic_poly, delta);
    
    let mut modulus = SparseMapVector::new(S.rank(), Fp);
    for (c, i) in FpX.terms(&S.generating_poly(&FpX, &Sbase_to_Fp)) {
        if i < S.rank() {
            *modulus.at_mut(i) = Fp.negate(Fp.clone_el(c));
        }
    }
    let Fq = FreeAlgebraImpl::new(Fp, S.rank(), modulus).as_field().unwrap();
    let FqX = DensePolyRing::new(&Fq, "X");
    let (roots, _) = <_ as FactorPolyField>::factor_poly(&FqX, &FqX.lifted_hom(&ZpeX, Fq.inclusion().compose(&Zpe_to_Fp)).map_ref(&irred_poly));
    assert_eq!(1, FqX.degree(&roots[0].0).unwrap());
    assert!(Fq.is_one(FqX.lc(&roots[0].0).unwrap()));
    let root = Fq.negate(Fq.clone_el(FqX.coefficient_at(&roots[0].0, 0)));
    let mut root_in_S = S.from_canonical_basis(Fq.wrt_canonical_basis(&root).iter().map(|x| Sbase_to_Fp.smallest_lift(x)));
    let irred_poly_derivate = derive_poly(&ZpeX, &irred_poly);
    for _ in 0..ZZi64.abs_log2_ceil(&e.try_into().unwrap()).unwrap() {
        root_in_S = S.sub_ref_fst(&root_in_S, S.checked_div(&ZpeX.evaluate(&irred_poly, &root_in_S, S.inclusion().compose(&Zpe_to_Sbase)), &ZpeX.evaluate(&irred_poly_derivate, &root_in_S, S.inclusion().compose(&Zpe_to_Sbase))).unwrap());
    }
    debug_assert!(S.is_zero(&ZpeX.evaluate(&irred_poly, &root_in_S, S.inclusion().compose(&Zpe_to_Sbase))));

    let subring_galois_group = CyclotomicGaloisGroupBase::new(parent_galois_group.m() * d as u64 / S.rank() as u64);
    let subring_frobenius = subring_galois_group.from_representative(parent_galois_group.representative(&frobenius).try_into().unwrap());
    let relative_galois_group = subring_galois_group.into().subgroup([subring_frobenius]);
    let base_circuit = norm_circuit(&S, &relative_galois_group).compose(PlaintextCircuit::sub(&S), &S).compose(
        PlaintextCircuit::constant(root_in_S, &S).tensor(PlaintextCircuit::identity(1, &S), &S), &S
    );
    let k = ZZi64.abs_log2_ceil(&ZpeX.degree(&delta).unwrap().try_into().unwrap()).unwrap();
    assert_eq!(1 << k, ZpeX.degree(&delta).unwrap());
    let pows2_circuit = (0..k).fold(PlaintextCircuit::constant_i32(1, &S).tensor(PlaintextCircuit::identity(1, &S), &S), |current, _| 
        PlaintextCircuit::identity(current.output_count(), &S).tensor(PlaintextCircuit::square(&S).compose(PlaintextCircuit::select(current.output_count(), &[current.output_count() - 1], &S), &S), &S)
            .compose(current.output_twice(&S), &S)
    );
    let correction_circuit = PlaintextCircuit::linear_transform_ring(
        &[ZpeX.coefficient_at(&delta, 0)].into_iter().chain((0..=k).map(|i| ZpeX.coefficient_at(&delta, 1 << i)))
            .map(|x| S.inclusion().map(Zpe_to_Sbase.map_ref(x))).collect::<Vec<_>>(), 
        &S
    );
    let result = PlaintextCircuit::identity(pows2_circuit.output_count(), &S).tensor(
        PlaintextCircuit::linear_transform(&[Coefficient::NegOne, Coefficient::One], &S).compose(correction_circuit.tensor(base_circuit, &S), &S), &S
    ).compose(
        pows2_circuit.output_twice(&S).tensor(PlaintextCircuit::identity(1, &S), &S), &S
    ).compose(
        PlaintextCircuit::identity(1, &S).output_twice(&S), &S
    );
    return result;
}

///
/// Assuming that `monic_poly` is a monic polynomial of degree `d` dividing the rank of `S`, then this
/// constructs a circuit evaluating `monic_poly` using the norm in a Galois subring of `S`.
/// 
/// This may fail in rare cases if no suitable irreducible polynomials are found that suitably relate to `monic_poly`.
/// The resulting circuit has the final evaluation as last output. Earlier outputs are `1, x, x^2, x^4, x^8, ...`.
/// 
#[instrument(skip_all)]
fn find_irreducible_modification<P, R>(
    ZpeX: P, 
    monic_poly: &El<P>, 
    S: R, 
    parent_galois_group: &CyclotomicGaloisGroup, 
    frobenius: GaloisGroupEl
) -> Result<PlaintextCircuit<<R as RingStore>::Type>, ()>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        BaseRing<P>: ZnRing + DivisibilityRing,
        R: RingStore,
        R::Type: FreeAlgebra + FiniteRing + DivisibilityRing,
        BaseRing<R>: ZnRing
{
    let d = ZpeX.degree(monic_poly).unwrap();
    assert!(S.rank().checked_div(d).is_some());
    let Zpe = ZpeX.base_ring();
    assert!(Zpe.is_one(ZpeX.lc(monic_poly).unwrap()));
    let (p, _) = is_prime_power(Zpe.integer_ring(), Zpe.modulus()).unwrap();
    let FpX = DensePolyRing::new(zn_big::Zn::new(ZZbig, int_cast(p, ZZbig, Zpe.integer_ring())).as_field().unwrap(), "X");
    let Fp = FpX.base_ring();
    let Sbase_to_Fp = ZnReductionMap::new(S.base_ring(), Fp).unwrap();
    let Zpe_to_Sbase = ZnReductionMap::new(Zpe, S.base_ring()).unwrap();
    let Zpe_to_Fp = (&Sbase_to_Fp).compose(&Zpe_to_Sbase);
    let monic_poly_mod_p = FpX.lifted_hom(&ZpeX, &Zpe_to_Fp).map_ref(monic_poly);
    let mut rng = oorandom::Rand64::new(0);
    for k in 0..ZZi64.abs_log2_ceil(&d.try_into().unwrap()).unwrap() {
        for _ in 0..10 {
            let delta_constant = Zpe.random_element(|| rng.rand_u64());
            let delta = ZpeX.from_terms((0..=k).map(|i| (Zpe.random_element(|| rng.rand_u64()), 1 << i)).chain([(delta_constant, 0)]));
            let delta_mod_p = FpX.lifted_hom(&ZpeX, &Zpe_to_Fp).map_ref(&delta);
            if <_ as FactorPolyField>::is_irred(&FpX, &FpX.add_ref_fst(&monic_poly_mod_p, delta_mod_p)) {
                return Ok(compute_circuit_from_irreducible_poly(&FpX, ZpeX, monic_poly, &delta, S, parent_galois_group, frobenius));
            }
        }
    }
    return Err(());
}

///
/// Attempts to find a Galois-based circuit for evaluating the given polynomial, using the
/// algorithms of <https://ia.cr/2023/1304>.
/// 
/// This only supports the evaluation of a single polynomial, since for multiple polynomials,
/// the norm-based algorithm is usually not optimal.
/// 
#[instrument(skip_all)]
pub fn poly_circuit_via_norm<P, R>(hypercube_iso: &HypercubeIsomorphism<R>, poly_ring: P, poly: &El<P>) -> Result<PlaintextCircuit<R::Type>, ()>
    where P: RingStore,
        P::Type: PolyRing,
        BaseRing<P>: ZnRing + DivisibilityRing,
        R: RingStore,
        R::Type: NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let S = hypercube_iso.slot_ring();
    assert!(poly_ring.degree(poly).unwrap() <= S.rank());
    let mut subfield_rank = poly_ring.degree(poly).unwrap();
    let Zpe_to_S = S.inclusion().compose(ZnReductionMap::new(poly_ring.base_ring(), S.base_ring()).unwrap());
    let rank_divisors = divisors(S.rank().try_into().unwrap());

    let result = loop {
        subfield_rank = rank_divisors.iter().copied().map(|x| usize::try_from(x).unwrap()).filter(|new_d| *new_d >= subfield_rank).min().ok_or(())?;
        if poly_ring.degree(poly).unwrap() < subfield_rank {
            let new_poly = poly_ring.add_ref_fst(poly, poly_ring.from_terms([(poly_ring.base_ring().one(), subfield_rank)]));
            let main_circuit = find_irreducible_modification(&poly_ring, &new_poly, hypercube_iso.slot_ring(), hypercube_iso.galois_group().parent(), hypercube_iso.hypercube().frobenius(1))?;
            debug_assert!(main_circuit.output_count() >= 3);
            let k = main_circuit.output_count() - 3;
            let correction_circuit = compute_powers_circuit(S, &[0].into_iter().chain((0..=k).map(|i| 1 << i)).collect::<Vec<_>>(), &[subfield_rank]);
            break PlaintextCircuit::linear_transform(&[Coefficient::NegOne, Coefficient::One], S)
                .compose(correction_circuit.tensor(PlaintextCircuit::identity(1, S), S), S)
                .compose(main_circuit, S);
        } else if let Some(lc_inv) = poly_ring.base_ring().invert(poly_ring.lc(poly).unwrap()) {
            let new_poly = poly_ring.inclusion().mul_ref_map(poly, &lc_inv);
            let main_circuit = find_irreducible_modification(&poly_ring, &new_poly, hypercube_iso.slot_ring(), hypercube_iso.galois_group().parent(), hypercube_iso.hypercube().frobenius(1))?;
            break PlaintextCircuit::linear_transform_ring(&[Zpe_to_S.map_ref(poly_ring.lc(poly).unwrap())], S)
                .compose(PlaintextCircuit::select(main_circuit.output_count(), &[main_circuit.output_count() - 1], S), S)
                .compose(main_circuit, S);
        } else {
            subfield_rank += 1;
            continue;
        }
    };
    return Ok(result.change_ring_uniform(|x| match x {
        Coefficient::One => Coefficient::One,
        Coefficient::NegOne => Coefficient::NegOne,
        Coefficient::Zero => Coefficient::Zero,
        Coefficient::Integer(x) => Coefficient::Integer(x),
        Coefficient::Other(x) => Coefficient::Other(hypercube_iso.from_slot_values((0..hypercube_iso.slot_count()).map(|_| hypercube_iso.slot_ring().clone_el(&x))))
    }));
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;
#[cfg(test)]
use crate::number_ring::hypercube::structure::HypercubeStructure;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::quotient_by_int::*;

#[test]
fn test_poly_circuit_via_norm_pow2() {
    let ring = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(16), Zn::new(3));
    let hypercube = HypercubeIsomorphism::new::<false>(&ring, &HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(3, ZZbig, ZZi64)), None);
    assert_eq!(4, hypercube.slot_ring().rank());
    assert_eq!(2, hypercube.slot_count());
    let poly_ring = DensePolyRing::new(ring.base_ring(), "X");

    let [f] = poly_ring.with_wrapped_indeterminate(|X| [X.pow_ref(4) + 1]);
    let circuit = poly_circuit_via_norm(&hypercube, &poly_ring, &f).unwrap();
    assert_eq!(1, circuit.output_count());
    assert_eq!(2, circuit.multiplication_gate_count());
    assert_eq!(2, circuit.galois_gate_output_sum());
    assert_eq!(2, circuit.mul_depth(0));
    for x in ring.base_ring().elements() {
        assert_el_eq!(ring, ring.inclusion().map(poly_ring.evaluate(&f, &x, ring.base_ring().identity())), &circuit.evaluate(&[ring.inclusion().map(x)], ring.identity())[0]);
    }

    let [f] = poly_ring.with_wrapped_indeterminate(|X| [X.pow_ref(3) + 1]);
    let circuit = poly_circuit_via_norm(&hypercube, &poly_ring, &f).unwrap();
    assert_eq!(1, circuit.output_count());
    assert_eq!(4, circuit.multiplication_gate_count());
    assert_eq!(2, circuit.galois_gate_output_sum());
    assert_eq!(2, circuit.mul_depth(0));
    for x in ring.base_ring().elements() {
        assert_el_eq!(ring, ring.inclusion().map(poly_ring.evaluate(&f, &x, ring.base_ring().identity())), &circuit.evaluate(&[ring.inclusion().map(x)], ring.identity())[0]);
    }

    let ring = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(16), Zn::new(27));
    let hypercube = HypercubeIsomorphism::new::<false>(&ring, &HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(3, ZZbig, ZZi64)), None);
    assert_eq!(4, hypercube.slot_ring().rank());
    assert_eq!(2, hypercube.slot_count());
    let poly_ring = DensePolyRing::new(ring.base_ring(), "X");

    let [f] = poly_ring.with_wrapped_indeterminate(|X| [4 * X.pow_ref(4) + 7 * X.pow_ref(3) + 2 * X.pow_ref(2) + 9 * X + 3]);
    let circuit = poly_circuit_via_norm(&hypercube, &poly_ring, &f).unwrap();
    assert_eq!(1, circuit.output_count());
    assert_eq!(2, circuit.multiplication_gate_count());
    assert_eq!(2, circuit.galois_gate_output_sum());
    assert_eq!(2, circuit.mul_depth(0));
    for x in ring.base_ring().elements() {
        assert_el_eq!(ring, ring.inclusion().map(poly_ring.evaluate(&f, &x, ring.base_ring().identity())), &circuit.evaluate(&[ring.inclusion().map(x)], ring.identity())[0]);
    }

    let [f] = poly_ring.with_wrapped_indeterminate(|X| [7 * X.pow_ref(3) + 2 * X.pow_ref(2) + 9 * X + 3]);
    let circuit = poly_circuit_via_norm(&hypercube, &poly_ring, &f).unwrap();
    assert_eq!(1, circuit.output_count());
    assert_eq!(4, circuit.multiplication_gate_count());
    assert_eq!(2, circuit.galois_gate_output_sum());
    assert_eq!(2, circuit.mul_depth(0));
    for x in ring.base_ring().elements() {
        assert_el_eq!(ring, ring.inclusion().map(poly_ring.evaluate(&f, &x, ring.base_ring().identity())), &circuit.evaluate(&[ring.inclusion().map(x)], ring.identity())[0]);
    }

    let ring = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(64), Zn::new(27));
    let hypercube = HypercubeIsomorphism::new::<false>(&ring, &HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(3, ZZbig, ZZi64)), None);
    assert_eq!(16, hypercube.slot_ring().rank());
    assert_eq!(2, hypercube.slot_count());
    let poly_ring = DensePolyRing::new(ring.base_ring(), "X");

    let [f] = poly_ring.with_wrapped_indeterminate(|X| [X.pow_ref(8) + 21 * X.pow_ref(5) + X.pow_ref(2) + X]);
    let circuit = poly_circuit_via_norm(&hypercube, &poly_ring, &f).unwrap();
    assert_eq!(1, circuit.output_count());
    assert_eq!(3, circuit.multiplication_gate_count());
    assert_eq!(3, circuit.galois_gate_output_sum());
    assert_eq!(3, circuit.mul_depth(0));
    for x in ring.base_ring().elements() {
        assert_el_eq!(ring, ring.inclusion().map(poly_ring.evaluate(&f, &x, ring.base_ring().identity())), &circuit.evaluate(&[ring.inclusion().map(x)], ring.identity())[0]);
    }

    let [f] = poly_ring.with_wrapped_indeterminate(|X| [X.pow_ref(6) + 21 * X.pow_ref(5) + X.pow_ref(2) + X]);
    let circuit = poly_circuit_via_norm(&hypercube, &poly_ring, &f).unwrap();
    assert_eq!(1, circuit.output_count());
    assert_eq!(6, circuit.multiplication_gate_count());
    assert_eq!(3, circuit.galois_gate_output_sum());
    assert_eq!(3, circuit.mul_depth(0));
    for x in ring.base_ring().elements() {
        assert_el_eq!(ring, ring.inclusion().map(poly_ring.evaluate(&f, &x, ring.base_ring().identity())), &circuit.evaluate(&[ring.inclusion().map(x)], ring.identity())[0]);
    }

    let [f] = poly_ring.with_wrapped_indeterminate(|X| [4 * X.pow_ref(16) + X.pow_ref(15) - X.pow_ref(2)]);
    let circuit = poly_circuit_via_norm(&hypercube, &poly_ring, &f).unwrap();
    assert_eq!(1, circuit.output_count());
    assert_eq!(4, circuit.multiplication_gate_count());
    assert_eq!(4, circuit.galois_gate_output_sum());
    assert_eq!(4, circuit.mul_depth(0));
    for x in ring.base_ring().elements() {
        assert_el_eq!(ring, ring.inclusion().map(poly_ring.evaluate(&f, &x, ring.base_ring().identity())), &circuit.evaluate(&[ring.inclusion().map(x)], ring.identity())[0]);
    }
}