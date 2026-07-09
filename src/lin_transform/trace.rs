use std::cell::RefCell;
use std::iter::repeat;

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

use crate::circuit::*;
use crate::number_ring::galois::*;
use crate::number_ring::hypercube::isomorphism::SlotRingOver;
use crate::{NiceZn, ZZbig, ZZi64};

fn cyclic_trace_norm_circuit<R>(ring: R, galois_group: &Subgroup<CyclotomicGaloisGroup>, generator: &GaloisGroupEl, l: usize, combiner: PlaintextCircuit<R::Type>) -> PlaintextCircuit<R::Type>
    where R: RingStore + Copy
{
    assert!(l >= 1);
    let mut circuit = PlaintextCircuit::identity(1, ring);
    let extend_circuit = RefCell::new(|l_idx: usize, r_idx: usize, l_num: i64| {
        take_mut::take(&mut circuit, |circuit| PlaintextCircuit::identity(circuit.output_count(), ring).tensor(combiner.clone(ring).compose(
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

fn cyclic_trace_circuit_window<R>(ring: R, galois_group: &Subgroup<CyclotomicGaloisGroup>, generator: &GaloisGroupEl, l: usize, window_size: usize) -> PlaintextCircuit<R::Type>
    where R: RingStore + Copy
{
    assert!(l >= 1);
    assert!(window_size >= 2);
    if l == 1 {
        return PlaintextCircuit::identity(1, ring);
    }

    let mut circuit = PlaintextCircuit::gal_many(
        &(0..window_size)
            .map(|i| galois_group.pow(generator, &int_cast(i as i64, ZZbig, ZZi64)))
            .collect::<Vec<_>>(), 
        galois_group, 
        ring
    );
    let l_decomp = repeat(()).scan(l, |current, ()| {
        if *current == 0 {
            return None;
        }
        let (quo, rem) = (*current / window_size, *current % window_size);
        *current = quo;
        return Some(rem);
    }).collect::<Vec<_>>();
    let mut l_decomp_it = l_decomp.iter().rev();

    let mut current_step;
    let start = *l_decomp_it.next().unwrap();
    debug_assert!(start != 0);
    if start == 1 {
        let next = *l_decomp_it.next().unwrap();
        let g = galois_group.pow(generator, &int_cast(next as i64, ZZbig, ZZi64));
        let multiplied = PlaintextCircuit::gal(g, galois_group, ring).compose(
            PlaintextCircuit::linear_transform(&(0..window_size).map(|_| Coefficient::One).collect::<Vec<_>>(), ring), 
            ring
        );
        circuit = PlaintextCircuit::add(ring).compose(
            PlaintextCircuit::linear_transform(
                &(0..window_size).map(|i| if i < next { Coefficient::One } else { Coefficient::Zero }).collect::<Vec<_>>(), 
                ring
            ).tensor(multiplied, ring),
            ring
        ).tensor(
            PlaintextCircuit::identity(window_size, ring), 
            ring
        ).compose(circuit.output_times(3, ring), ring);
        current_step = window_size + next;
    } else {
        circuit = PlaintextCircuit::linear_transform(
            &(0..window_size).map(|i| if i < start { Coefficient::One } else { Coefficient::Zero }).collect::<Vec<_>>(), 
            ring
        ).tensor(PlaintextCircuit::identity(window_size, ring), ring).compose(circuit.output_twice(ring), ring);
        current_step = start;
    }
    for digit in l_decomp_it {
        let gs = (0..window_size).map(|i| galois_group.pow(generator, &int_cast((i * current_step + digit) as i64, ZZbig, ZZi64))).collect::<Vec<_>>();
        let multiplied = PlaintextCircuit::linear_transform(
            &(0..window_size).map(|_| Coefficient::One).collect::<Vec<_>>(), 
            ring
        ).compose(
            PlaintextCircuit::gal_many(&gs, galois_group, ring), 
            ring
        );
        let additional = PlaintextCircuit::linear_transform(
            &(0..window_size).map(|i| if i < *digit { Coefficient::One } else { Coefficient::Zero }).collect::<Vec<_>>(), 
            ring
        );
        circuit = PlaintextCircuit::add(ring).compose(
            multiplied.tensor(additional, ring), 
            ring
        ).tensor(
            PlaintextCircuit::select(window_size + 1, &(1..=window_size).collect::<Vec<_>>(), ring), 
            ring
        ).compose(circuit.output_twice(ring), ring);
        current_step = current_step * window_size + digit;
    }
    return PlaintextCircuit::select(window_size + 1, &[0], ring).compose(circuit, ring);
}

///
/// Generates a circuit that computes a relative field trace between two rings
/// with the given relative galois group.
/// 
/// More concretely, this creates a circuit that computes
/// ```text
///   x -> sum_σ σ(x)
/// ```
/// where `σ` ranges through `relative_galois_group`.
/// 
pub fn trace_circuit<R>(ring: R, relative_galois_group: &Subgroup<CyclotomicGaloisGroup>, cost_model: &CircuitEvaluatorCosts) -> PlaintextCircuit<R::Type>
    where R: RingStore + Copy
{
    let cyclic_trace_circuit = |(g, l)| {
        if l == 1 {
            return PlaintextCircuit::identity(1, ring);
        }
        let (window_size, cost) = (2..=l).map(|w| (w, (cost_model.cost_setup_hoisted_gal + cost_model.cost_hoisted_gal * w as f64) / (w as f64).log2()))
            .min_by(|(_, lc), (_, rc)| f64::total_cmp(lc, rc)).unwrap();
        if cost <= cost_model.cost_single_gal * 2. {
            cyclic_trace_circuit_window(ring, relative_galois_group, &g, l, window_size)
        } else {
            cyclic_trace_norm_circuit(ring, &relative_galois_group, &g, l, PlaintextCircuit::add(ring))
        }
    };
    relative_galois_group.get_group().rectangular_form().into_iter()
        .map(cyclic_trace_circuit)
        .fold(PlaintextCircuit::identity(1, ring), |current, next| current.compose(next, ring))
}

///
/// Generates a circuit that computes a relative field norm between two rings
/// with the given relative galois group.
/// 
/// More concretely, this creates a circuit that computes
/// ```text
///   x -> prod_σ σ(x)
/// ```
/// where `σ` ranges through `relative_galois_group`.
/// 
pub fn norm_circuit<R>(ring: R, relative_galois_group: &Subgroup<CyclotomicGaloisGroup>) -> PlaintextCircuit<R::Type>
    where R: RingStore + Copy
{
    relative_galois_group.get_group().rectangular_form().into_iter()
        .map(|(g, l)| cyclic_trace_norm_circuit(ring, &relative_galois_group, &g, l, PlaintextCircuit::mul(ring)))
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
use crate::number_ring::tensor_ring::TensorProductNumberRing;
#[cfg(test)]
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
#[cfg(test)]
use crate::number_ring::*;
#[cfg(test)]
use std::sync::Arc;
#[cfg(test)]
use std::alloc::Global;
#[cfg(test)]
use fhe_ir::Program;

#[test]
fn test_extract_coefficient_map() {
    feanor_tracing::DelayedLogger::init_test();
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
    feanor_tracing::DelayedLogger::init_test();
    let ring = NumberRingQuotientByIntBase::new(OddSquarefreeCyclotomicNumberRing::new(7), Zn::new(3));
    let full_galois_group = ring.number_ring().galois_group();
    let relative_galois_group = full_galois_group.get_group().clone().subgroup([full_galois_group.from_representative(3)]);
    let trace = trace_circuit(&ring, &relative_galois_group, &DEFAULT_EVALUATOR_COSTS);
    for x in ring.elements() {
        let actual = trace.evaluate(std::slice::from_ref(&x), ring.identity()).pop().unwrap();
        assert_el_eq!(&ring, ring.inclusion().map(ring.trace(x)), actual);
    }

    let relative_galois_group = full_galois_group.get_group().clone().subgroup([full_galois_group.from_representative(2)]);
    let relative_trace = trace_circuit(&ring, &relative_galois_group, &DEFAULT_EVALUATOR_COSTS);
    assert_eq!(1, relative_trace.output_count());
    let input = ring.canonical_gen();
    let actual = relative_trace.evaluate(std::slice::from_ref(&input), ring.identity()).pop().unwrap();
    let expected = ring.sum([ring.canonical_gen(), ring.pow(ring.canonical_gen(), 2), ring.pow(ring.canonical_gen(), 4)]);
    assert_el_eq!(&ring, expected, actual);

    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(65537));
    let full_galois_group = ring.number_ring().galois_group();
    let trace = trace_circuit(&ring, &full_galois_group.get_group().clone().full_subgroup(), &DEFAULT_EVALUATOR_COSTS);
    for i in 0..24 {
        let actual = trace.evaluate(&[ring.pow(ring.canonical_gen(), i)], ring.identity()).pop().unwrap();
        assert_el_eq!(&ring, ring.inclusion().map(ring.trace(ring.pow(ring.canonical_gen(), i))), actual);
    }
}

#[test]
fn test_cyclic_trace_circuit_window() {
    feanor_tracing::DelayedLogger::init_test();
    let galois_group = CyclotomicGaloisGroupBase::new(1 << 6).into().full_subgroup();
    let generator = galois_group.parent().from_representative(5);
    let circuit = cyclic_trace_circuit_window(ZZi64, &galois_group, &generator, 16, 4);
    let expected: Program<i64> = Program::parse_check(r#"
        func(%in) {
            %x1, %x2, %x3 = galois %in, exponents = [5, 25, 61]
            %s1 = inner_prod %in, %x1, %x2, %x3, coefficients = [@1, @1, @1, @1]
            %x1, %x2, %x3 = galois %s1, exponents = [49, 33, 17]
            %s2 = inner_prod %s1, %x1, %x2, %x3, coefficients = [@1, @1, @1, @1]
            return %s2
        }
        @1: 1
    "#.as_bytes()).unwrap();
    assert!(circuit.eq(&PlaintextCircuit::from_ir(ZZi64, Some(&galois_group), &expected), ZZi64, Some(&galois_group)));

    let galois_group = CyclotomicGaloisGroupBase::new(1 << 6).into().full_subgroup();
    let generator = galois_group.parent().from_representative(5);
    let circuit = cyclic_trace_circuit_window(ZZi64, &galois_group, &generator, 16, 3);
    let expected: Program<i64> = Program::parse_check(r#"
        func(%in) {
            %x1, %x2 = galois %in, exponents = [5, 25]
            %s1 = inner_prod %in, %x1, %x2, coefficients = [@1, @1, @1]
            %c1 = galois %s1, exponents = [25]
            %s2 = inner_prod %in, %x1, %c1, coefficients = [@1, @1, @1]
            %x1, %x2, %x3 = galois %s2, exponents = [5, 9, 29]
            %s3 = inner_prod %in, %x1, %x2, %x3, coefficients = [@1, @1, @1, @1]
            return %s3
        }
        @1: 1
    "#.as_bytes()).unwrap();
    assert!(circuit.eq(&PlaintextCircuit::from_ir(ZZi64, Some(&galois_group), &expected), ZZi64, Some(&galois_group)));

    let galois_group = CyclotomicGaloisGroupBase::new(1 << 6).into().full_subgroup();
    let generator = galois_group.parent().from_representative(5);
    let circuit = cyclic_trace_circuit_window(ZZi64, &galois_group, &generator, 16, 16);
    let expected: Program<i64> = Program::parse_check(r#"
        func(%in) {
            %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10, %x11, %x12, %x13, %x14, %x15 = galois %in, exponents = [5, 25, 61, 49, 53, 9, 45, 33, 37, 57, 29, 17, 21, 41, 13]
            %s1 = inner_prod %in, %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10, %x11, %x12, %x13, %x14, %x15, coefficients = [@1, @1, @1, @1, @1, @1, @1, @1, @1, @1, @1, @1, @1, @1, @1, @1]
            return %s1
        }
        @1: 1
    "#.as_bytes()).unwrap();
    assert!(circuit.eq(&PlaintextCircuit::from_ir(ZZi64, Some(&galois_group), &expected), ZZi64, Some(&galois_group)));

    let galois_group = CyclotomicGaloisGroupBase::new(7).into().full_subgroup();
    let generator = galois_group.parent().from_representative(3);
    let circuit = cyclic_trace_circuit_window(ZZi64, &galois_group, &generator, 6, 5);
    let expected: Program<i64> = Program::parse_check(r#"
        func(%in) {
            %x1, %x2, %x3, %x4 = galois %in, exponents = [3, 2, 6, 4]
            %s1 = inner_prod %in, %x1, %x2, %x3, %x4, coefficients = [@1, @1, @1, @1, @1]
            %c1 = galois %s1, exponents = [3]
            %s2 = inner_prod %in, %c1, coefficients = [@1, @1]
            return %s2
        }
        @1: 1
    "#.as_bytes()).unwrap();
    assert!(circuit.eq(&PlaintextCircuit::from_ir(ZZi64, Some(&galois_group), &expected), ZZi64, Some(&galois_group)));

    let galois_group = CyclotomicGaloisGroupBase::new(7).into().full_subgroup();
    let generator = galois_group.parent().from_representative(2);
    let circuit = cyclic_trace_circuit_window(ZZi64, &galois_group, &generator, 3, 3);
    let expected: Program<i64> = Program::parse_check(r#"
        func(%in) {
            %x1, %x2 = galois %in, exponents = [2, 4]
            %s1 = inner_prod %in, %x1, %x2, coefficients = [@1, @1, @1]
            return %s1
        }
        @1: 1
    "#.as_bytes()).unwrap();
    assert!(circuit.eq(&PlaintextCircuit::from_ir(ZZi64, Some(&galois_group), &expected), ZZi64, Some(&galois_group)));
    
    let galois_group = CyclotomicGaloisGroupBase::new(29).into().full_subgroup();
    let generator = galois_group.parent().from_representative(16);
    let circuit = cyclic_trace_circuit_window(ZZi64, &galois_group, &generator, 7, 3);
    let expected: Program<i64> = Program::parse_check(r#"
        func(%in) {
            %1, %2 = galois %in, exponents = [-13, -5]
            %3 = inner_prod %in, %1, coefficients = [@1, @1]
            %4, %5, %6 = galois %3, exponents = [-13, 7, -6]
            %7 = inner_prod %in, %4, %5, %6, coefficients = [@1, @1, @1, @1]
            return %7
        }
        @1: 1
    "#.as_bytes()).unwrap();
    println!("{:?}", circuit.to_ir(ZZi64, Some(&galois_group)));
    assert!(circuit.eq(&PlaintextCircuit::from_ir(ZZi64, Some(&galois_group), &expected), ZZi64, Some(&galois_group)));
}