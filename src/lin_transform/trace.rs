use std::cell::RefCell;

use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::algorithms::sqr_mul::generic_pow_shortest_chain_table;
use feanor_math::computation::no_error;
use feanor_math::group::AbelianGroupStore;
use feanor_math::integer::int_cast;
use feanor_math::matrix::OwnedMatrix;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::*;
use feanor_math::algorithms::linsolve::LinSolveRingStore;

use crate::circuit::PlaintextCircuit;
use crate::number_ring::galois::*;
use crate::number_ring::hypercube::isomorphism::SlotRingOver;
use crate::{NiceZn, ZZbig, ZZi64};

///
/// Generates a circuit that computes a relative trace between two rings
/// with the given relative galois group.
/// 
/// More concretely, this creates a circuit that computes
/// ```text
///   x -> sum_σ σ(x)
/// ```
/// where `σ` ranges through `relative_galois_group`.
/// 
pub fn trace_circuit<R>(ring: R, relative_galois_group: &Subgroup<CyclotomicGaloisGroup>) -> PlaintextCircuit<R::Type>
    where R: RingStore + Copy
{
    fn cyclic_trace_circuit<R>(ring: R, galois_group: &Subgroup<CyclotomicGaloisGroup>, generator: &GaloisGroupEl, l: usize) -> PlaintextCircuit<R::Type>
        where R: RingStore + Copy
    {
        let mut circuit = PlaintextCircuit::identity(1, ring);
        let extend_circuit = RefCell::new(|l_idx: usize, r_idx: usize, l_num: i64| {
            take_mut::take(&mut circuit, |circuit| PlaintextCircuit::identity(circuit.output_count(), ring).tensor(PlaintextCircuit::add(ring).compose(
                PlaintextCircuit::identity(1, ring).tensor(PlaintextCircuit::gal(galois_group.pow(generator, &int_cast(l_num, ZZbig, ZZi64)), galois_group, ring), ring), ring
            ), ring).compose(
                PlaintextCircuit::select(circuit.output_count(), &(0..circuit.output_count()).chain([l_idx, r_idx].into_iter()).collect::<Vec<_>>(), ring), ring
            ).compose(
                circuit, ring
            ));
            return circuit.output_count() - 1;
        });

        let result_idx = generic_pow_shortest_chain_table(
            (Some(0), 1),
            &(l as i64),
            StaticRing::<i64>::RING,
            |(idx, num)| {
                if let Some(idx) = idx {
                    let result = extend_circuit.borrow_mut()(*idx, *idx, *num);
                    Ok((Some(result), num + num))
                } else {
                    Ok((None, 0))
                }
            },
            |(l_idx, l_num), (r_idx, r_num)| {
                if let Some(l_idx) = l_idx {
                    if let Some(r_idx) = r_idx {
                        let result = extend_circuit.borrow_mut()(*l_idx, *r_idx, *l_num);
                        Ok((Some(result), l_num + r_num))
                    } else {
                        Ok((Some(*l_idx), *l_num))
                    }
                } else {
                    Ok((*r_idx, *r_num))
                }
            },
            |x| *x,
            (None, 0)
        ).unwrap_or_else(no_error).0.unwrap();

        return PlaintextCircuit::select(circuit.output_count(), &[result_idx], ring).compose(circuit, ring);
    }

    relative_galois_group.get_group().rectangular_form().into_iter()
        .map(|(g, l)| cyclic_trace_circuit(ring, &relative_galois_group, &g, l))
        .fold(PlaintextCircuit::identity(1, ring), |current, next| current.compose(next, ring))
}

///
/// Computes `a` such that `y -> Tr(ay)` is the given `Fp`-linear map `GR(p, e, d) -> Z/p^eZ`.
/// 
/// We assume that the frobenius automorphism in the given ring is given by `X -> X^p`
/// where `X` is its canonical generator. At the moment this always true, since we currently
/// choose the canonical generator to be a root of unity.
/// 
/// If the given function `function` is not `Fp`-linear, results may be nonsensical.
/// 
pub fn extract_linear_map<G, R>(slot_ring: &SlotRingOver<R>, mut function: G) -> El<SlotRingOver<R>>
    where G: FnMut(El<SlotRingOver<R>>) -> El<R>,
        R: RingStore,
        R::Type: NiceZn
{
    let mut lhs = OwnedMatrix::zero(slot_ring.rank(), slot_ring.rank(), slot_ring.base_ring());
    let mut rhs = OwnedMatrix::zero(slot_ring.rank(), 1, slot_ring.base_ring());
    let mut sol = OwnedMatrix::zero(slot_ring.rank(), 1, slot_ring.base_ring());

    for i in 0..slot_ring.rank() {
        for j in 0..slot_ring.rank() {
            *lhs.at_mut(i, j) = slot_ring.trace(slot_ring.pow(slot_ring.canonical_gen(), i + j));
        }
    }
    for j in 0..slot_ring.rank() {
        *rhs.at_mut(j, 0) = function(slot_ring.pow(slot_ring.canonical_gen(), j));
    }

    slot_ring.base_ring().solve_right(lhs.data_mut(), rhs.data_mut(), sol.data_mut()).assert_solved();

    return slot_ring.from_canonical_basis((0..slot_ring.rank()).map(|i| slot_ring.base_ring().clone_el(sol.at(i, 0))));
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::local::*;
#[cfg(test)]
use feanor_math::algorithms::convolution::*;
#[cfg(test)]
use feanor_math::algorithms::unity_root::is_prim_root_of_unity;
#[cfg(test)]
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
#[cfg(test)]
use feanor_math::homomorphism::Homomorphism;
#[cfg(test)]
use feanor_math::rings::finite::FiniteRingStore;
#[cfg(test)]
use feanor_math::seq::VectorFn;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::*;
#[cfg(test)]
use crate::ntt::dyn_convolution::*;
#[cfg(test)]
use crate::number_ring::general_cyclotomic::OddSquarefreeCyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
#[cfg(test)]
use crate::number_ring::*;
#[cfg(test)]
use std::sync::Arc;
#[cfg(test)]
use std::alloc::Global;

#[test]
fn test_extract_coefficient_map() {
    let convolution = DynConvolutionAlgorithmConvolution::<ZnBase, Arc<dyn DynConvolutionAlgorithm<ZnBase>>>::new(Arc::new(STANDARD_CONVOLUTION));
    let base_ring = Zn::new(17 * 17);
    let modulus = (0..4).map(|_| base_ring.neg_one()).collect::<Vec<_>>();
    let slot_ring = FreeAlgebraImpl::new_with_convolution(base_ring, 4, modulus, "a", Global, convolution);
    let max_ideal_gen = slot_ring.int_hom().map(17);
    let slot_ring = AsLocalPIR::from(AsLocalPIRBase::promise_is_local_pir(slot_ring, max_ideal_gen, Some(2)));
    assert!(is_prim_root_of_unity(&slot_ring, &slot_ring.canonical_gen(), 5));

    let extract_constant_coeff = extract_linear_map(&slot_ring, |c| slot_ring.wrt_canonical_basis(&c).at(0));
    for i in 0..4 {
        let b = slot_ring.pow(slot_ring.canonical_gen(), i);
        let actual = slot_ring.trace(slot_ring.mul_ref(&b, &extract_constant_coeff));
        if i == 0 {
            assert_el_eq!(slot_ring.base_ring(), slot_ring.base_ring().one(), actual);
        } else {
            assert_el_eq!(slot_ring.base_ring(), slot_ring.base_ring().zero(), actual);
        }
    }
}

#[test]
fn test_trace_circuit() {
    let ring = NumberRingQuotientByIntBase::new(OddSquarefreeCyclotomicNumberRing::new(7), Zn::new(3));
    let full_galois_group = ring.number_ring().galois_group();
    let relative_galois_group = full_galois_group.get_group().clone().subgroup([full_galois_group.from_representative(3)]);
    let trace = trace_circuit(&ring, &relative_galois_group);
    for x in ring.elements() {
        let actual = trace.evaluate(std::slice::from_ref(&x), ring.identity()).pop().unwrap();
        assert_el_eq!(&ring, ring.inclusion().map(ring.trace(x)), actual);
    }

    let relative_galois_group = full_galois_group.get_group().clone().subgroup([full_galois_group.from_representative(2)]);
    let relative_trace = trace_circuit(&ring, &relative_galois_group);
    assert_eq!(1, relative_trace.output_count());
    let input = ring.canonical_gen();
    let actual = relative_trace.evaluate(std::slice::from_ref(&input), ring.identity()).pop().unwrap();
    let expected = ring.sum([ring.canonical_gen(), ring.pow(ring.canonical_gen(), 2), ring.pow(ring.canonical_gen(), 4)]);
    assert_el_eq!(&ring, expected, actual);

    let ring = NumberRingQuotientByIntBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(65537));
    let full_galois_group = ring.number_ring().galois_group();
    let trace = trace_circuit(&ring, &full_galois_group.get_group().clone().full_subgroup());
    for i in 0..24 {
        let actual = trace.evaluate(&[ring.pow(ring.canonical_gen(), i)], ring.identity()).pop().unwrap();
        assert_el_eq!(&ring, ring.inclusion().map(ring.trace(ring.pow(ring.canonical_gen(), i))), actual);
    }
}