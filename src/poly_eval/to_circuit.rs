use std::cmp::min;

use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::finite::FiniteRing;
use feanor_math::divisibility::*;
use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnReductionMap;
use feanor_math::seq::*;
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use tracing::instrument;

use crate::circuit::CircuitEvaluatorCosts;
use crate::circuit::PlaintextCircuit;
use crate::number_ring::NumberRingQuotient;
use crate::number_ring::hypercube::isomorphism::BaseRing;
use crate::number_ring::hypercube::isomorphism::HypercubeIsomorphism;
use crate::poly_eval::addition_chains::addition_chain_for;
use crate::poly_eval::addition_chains::addition_chain_lengths;
use crate::poly_eval::galois_based::poly_circuit_via_norm;
use crate::poly_eval::paterson_stockmeyer::paterson_stockmeyer_circuit;
use crate::*;

const DEFAULT_COSTS: CircuitEvaluatorCosts = CircuitEvaluatorCosts {
    cost_mul: 1.,
    cost_sqr: 0.83,
    cost_hoisted_gal: 0.5,
    cost_single_gal: 0.5,
    cost_setup_hoisted_gal: 0.
};

///
/// Heuristically chooses a low-depth, low-complexity circuit that
/// evaluates all the given univariate polynomials.
/// 
#[instrument(skip_all)]
pub fn poly_to_circuit<P>(poly_ring: P, polys: &[El<P>]) -> PlaintextCircuit<BaseRing<P>>
    where P: RingStore,
        P::Type: PolyRing,
        BaseRing<P>: FiniteRing + DivisibilityRing,
{
    heuristic_functional_decomposition(
        &poly_ring, 
        polys.iter().map(|f| poly_ring.clone_el(f)).collect(), 
        &mut |poly_ring, polys, _| {
            let bsgs_option = low_depth_bsgs_circuit(&poly_ring, &polys);
            let paterson_stockmeyer_option = paterson_stockmeyer_circuit(&poly_ring, &polys);
            match paterson_stockmeyer_option {
                Err(()) => bsgs_option,
                Ok(circuit) if circuit.multiplication_gate_count() > bsgs_option.multiplication_gate_count() => bsgs_option,
                Ok(circuit) => circuit
            }
        },
        &poly_ring.base_ring().identity()
    )
}

///
/// Creates a circuit that takes as input the values `x^i` for `i` in `input_powers` and outputs
/// `x^i` for `i` in `output_powers`.
/// 
#[instrument(skip_all)]
pub fn compute_powers_circuit<R>(ring: R, input_powers: &[usize], output_powers: &[usize]) -> PlaintextCircuit<R::Type>
    where R: RingStore + Copy
{
    let mut current = input_powers.to_vec();
    assert!(current.is_sorted());
    assert!(current.array_windows::<2>().all(|[x, y]| x != y));
    assert!(current.get(0) == Some(&1) || current.get(1) == Some(&1));
    let mut circuit = PlaintextCircuit::identity(current.len(), ring);
    if current.get(0) == Some(&1) {
        current.insert(0, 0);
        circuit = PlaintextCircuit::constant_i32(1, ring).tensor(circuit, ring);
    }
    let get_idx = |k: usize, values: &[usize]| values.iter().enumerate().filter(|(_, v)| **v == k).next().unwrap().0;

    for k in output_powers {
        debug_assert_eq!(input_powers.len(), circuit.input_count());
        debug_assert_eq!(current.len(), circuit.output_count());
        let (_chain_lengths, chain_description) = addition_chain_lengths(k + 1, &current);
        let chain = addition_chain_for(*k, &chain_description);
        for (val, (left, right)) in chain {
            circuit = PlaintextCircuit::identity(current.len(), ring).tensor(
                PlaintextCircuit::mul(ring).compose(PlaintextCircuit::select(current.len(), &[get_idx(left, &current), get_idx(right, &current)], ring), ring), ring
            ).compose(circuit.output_twice(ring), ring);
            current.push(val);
        }
    }
    return PlaintextCircuit::select(current.len(), &output_powers.iter().map(|k| get_idx(*k, &current)).collect::<Vec<_>>(), ring).compose(circuit, ring);
}

///
/// Detects common kinds of structure in the given polynomial that can be exploited
/// for more efficient evaluation.
/// 
/// Currently, this is only a check if the polynomial is even or odd.
/// 
#[instrument(skip_all)]
pub fn heuristic_functional_decomposition<P, R, H, F>(poly_ring: P, to_evaluate: Vec<El<P>>, factors_to_circuit: &mut F, hom: H) -> PlaintextCircuit<R>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        BaseRing<P>: DivisibilityRing,
        F: FnMut(P, Vec<El<P>>, H) -> PlaintextCircuit<R>,
        R: ?Sized + RingBase,
        H: Copy + Homomorphism<BaseRing<P>, R>
{
    assert!(hom.domain().get_ring() == poly_ring.base_ring().get_ring());
    if to_evaluate.len() == 0 {
        return PlaintextCircuit::drop(1);
    }
    let circuit_ring = hom.codomain();

    let mut polys_in_x_sqr = Vec::new();
    let mut generic_polys = Vec::new();
    let mut outputs = Vec::new();

    enum Output<R: ?Sized + RingBase> {
        Compute(PlaintextCircuit<R>),
        OddPoly(usize),
        EvenPoly(usize),
        GenericPoly(usize)
    }

    let to_evaluate_len = to_evaluate.len();
    for f in to_evaluate {
        let d = poly_ring.degree(&f).unwrap_or(0);
        if d == 0 {
            outputs.push(Output::Compute(PlaintextCircuit::constant(hom.map_ref(poly_ring.coefficient_at(&f, 0)), circuit_ring).tensor(PlaintextCircuit::drop(1), circuit_ring)));
        } else if d == 1 {
            outputs.push(Output::Compute(PlaintextCircuit::add(circuit_ring).compose(
                PlaintextCircuit::constant(hom.map_ref(poly_ring.coefficient_at(&f, 0)), circuit_ring).tensor(
                    PlaintextCircuit::linear_transform_ring(&[hom.map_ref(poly_ring.coefficient_at(&f, 1))], circuit_ring), 
                    circuit_ring
                ),
                circuit_ring
            )));
        } else if (1..=d).step_by(2).all(|i| poly_ring.base_ring().is_zero(poly_ring.coefficient_at(&f, i))) {
            let factored_poly = poly_ring.from_terms(poly_ring.terms(&f).map(|(c, i)| (poly_ring.base_ring().clone_el(c), i.checked_div(2).unwrap())));
            let idx = polys_in_x_sqr.len();
            polys_in_x_sqr.push(factored_poly);
            outputs.push(Output::EvenPoly(idx));
        } else if (0..=d).step_by(2).all(|i| poly_ring.base_ring().is_zero(poly_ring.coefficient_at(&f, i))) {
            let factored_poly = poly_ring.from_terms(poly_ring.terms(&f).map(|(c, i)| (poly_ring.base_ring().clone_el(c), i.checked_sub(1).unwrap().checked_div(2).unwrap())));
            let idx = polys_in_x_sqr.len();
            polys_in_x_sqr.push(factored_poly);
            outputs.push(Output::OddPoly(idx));
        } else {
            let idx = generic_polys.len();
            generic_polys.push(f);
            outputs.push(Output::GenericPoly(idx));
        }
    }

    if !outputs.iter().all(|out| if let Output::GenericPoly(_) = out { true } else { false }) {
        let generic_circuit = heuristic_functional_decomposition(poly_ring, generic_polys, factors_to_circuit, hom);

        if polys_in_x_sqr.len() > 0 {
            let polys_in_x_sqr_offset = 2;
            let generic_polys_offset = 2 + polys_in_x_sqr.len();

            let polys_in_x_sqr_circuit = heuristic_functional_decomposition(poly_ring, polys_in_x_sqr, factors_to_circuit, hom);
            let sqr_circuit = PlaintextCircuit::identity(1, circuit_ring).tensor(PlaintextCircuit::square(circuit_ring), circuit_ring)
                .compose(PlaintextCircuit::identity(1, circuit_ring).output_twice(circuit_ring), circuit_ring);
            let first_part = PlaintextCircuit::identity(2, circuit_ring)
                .tensor(polys_in_x_sqr_circuit.compose(PlaintextCircuit::select(2, &[1], circuit_ring), circuit_ring), circuit_ring)
                .tensor(generic_circuit.compose(PlaintextCircuit::select(2, &[0], circuit_ring), circuit_ring), circuit_ring)
                .compose(sqr_circuit.output_times(3, circuit_ring), circuit_ring);
            let first_part_output_len = first_part.output_count();

            let second_part = outputs.into_iter().fold(PlaintextCircuit::drop(first_part_output_len), |current, next| match next {
                Output::Compute(part) => current.tensor(part, circuit_ring),
                Output::GenericPoly(idx) => current.tensor(PlaintextCircuit::select(first_part_output_len, &[idx + generic_polys_offset], circuit_ring), circuit_ring).compose(
                    PlaintextCircuit::identity(first_part_output_len, circuit_ring).output_twice(circuit_ring), circuit_ring
                ),
                Output::EvenPoly(idx) => current.tensor(PlaintextCircuit::select(first_part_output_len, &[idx + polys_in_x_sqr_offset], circuit_ring), circuit_ring).compose(
                    PlaintextCircuit::identity(first_part_output_len, circuit_ring).output_twice(circuit_ring), circuit_ring
                ),
                Output::OddPoly(idx) => current.tensor(
                    PlaintextCircuit::mul(circuit_ring)
                        .compose(PlaintextCircuit::select(first_part_output_len, &[0, idx + polys_in_x_sqr_offset], circuit_ring), circuit_ring), circuit_ring
                ).compose(PlaintextCircuit::identity(first_part_output_len, circuit_ring).output_twice(circuit_ring), circuit_ring)
            });
            let result = second_part.compose(first_part, circuit_ring);
            debug_assert_eq!(1, result.input_count());
            debug_assert_eq!(to_evaluate_len, result.output_count());
            return result;
        } else {
            let input_len = generic_circuit.output_count() + 1;
            let generic_polys_offset = 1;
            let result = outputs.into_iter().fold(
                PlaintextCircuit::drop(input_len), |current, next| match next {
                    Output::Compute(part) => current.tensor(part.compose(PlaintextCircuit::select(input_len, &[0], circuit_ring), circuit_ring), circuit_ring),
                    Output::GenericPoly(idx) => current.tensor(PlaintextCircuit::select(input_len, &[idx + generic_polys_offset], circuit_ring), circuit_ring),
                    _ => unreachable!()
                }.compose(PlaintextCircuit::identity(input_len, circuit_ring).output_twice(circuit_ring), circuit_ring)
            )
                .compose(PlaintextCircuit::identity(1, circuit_ring).tensor(generic_circuit, circuit_ring), circuit_ring)
                .compose(PlaintextCircuit::identity(1, circuit_ring).output_twice(circuit_ring), circuit_ring);
            debug_assert_eq!(1, result.input_count());
            debug_assert_eq!(to_evaluate_len, result.output_count());
            return result;
        }
    } else {
        let result = factors_to_circuit(poly_ring, generic_polys, hom);
        return result;
    }
}

///
/// Computes the cost of the circuit [`low_depth_bsgs_circuit()`] would return, without
/// actually building the circuit.
/// 
pub fn low_depth_bsgs_cost<V>(degrees: V, baby_steps: usize) -> (/* mul depths */ impl VectorFn<usize>, /* mul count */ usize)
    where V: VectorFn<usize>
{
    let max_deg = degrees.iter().max().unwrap();
    let giant_steps = max_deg / baby_steps + 1;
    let giant_steps_half = giant_steps / 2 + 1;

    let baby_steps_mul_count = baby_steps - 1;
    let giant_steps_mul_count = giant_steps_half - 2;
    let mut final_mul_count = 0;
    for d in degrees.iter() {
        final_mul_count += d / baby_steps;
        // in this case we need one multiplication to get x^(d - (d % baby_steps)) and one to multiply it with the block
        if d / baby_steps > 1 && (d / baby_steps) % 2 == 1 {
            final_mul_count += 1;
        }
    }
    let mul_count = baby_steps_mul_count + giant_steps_mul_count + final_mul_count;

    let mul_depths = degrees.map_fn(move |d| ZZi64.abs_log2_ceil(&min(baby_steps as i64, d as i64)).unwrap() as usize + ZZi64.abs_log2_ceil(&((d / baby_steps) as i64)).map(|x| x + 1).unwrap_or(0) as usize);

    return (mul_depths, mul_count);
}

///
/// A low-depth variant of Paterson-Stockmeyer evaluation of polynomials.
/// 
/// # Algorithm
/// 
/// Currently, the circuit is built according to the following strategy:
///  - First, the first consecutive `baby_steps` powers of the input are computed, i.e.
///    `1, x, x^2, ..., x^baby_steps`
///  - Then the powers `1, x^baby_steps, x^(2 baby_steps), ...` are computed (the "giant steps")
///  - For each giant step and desired polynomial, a suitable linear combination of the baby steps 
///    is taken, and then multiplied with the giant step
///  - The results are summed up
/// 
/// In other words, to compute a single polynomial, the required number of multiplications is `baby_steps + 2 * giant_steps`.
/// The multiplicative depth is minimal (except possibly `+ 1` if divisions are not exact).
/// 
#[instrument(skip_all)]
fn low_depth_bsgs_circuit<P>(poly_ring: P, polys: &[El<P>]) -> PlaintextCircuit<<<P::Type as RingExtension>::BaseRing as RingStore>::Type>
    where P: RingStore,
        P::Type: PolyRing
{
    let degrees = polys.iter().map(|f| poly_ring.degree(f).unwrap() as usize).collect::<Vec<_>>();
    let max_deg = degrees.iter().copied().max().unwrap();

    let optimal_depths = degrees.iter().copied().map(|d| ZZi64.abs_log2_ceil(&(d as i64)).unwrap()).collect::<Vec<_>>();
    
    let baby_steps = (1..max_deg).filter(|bs| {
            let (depths, _) = low_depth_bsgs_cost((&degrees).copy_els(), *bs);
            (0..optimal_depths.len()).all(|i| depths.at(i) <= optimal_depths[i] + 1)
        })
        .min_by_key(|bs| low_depth_bsgs_cost((&degrees).copy_els(), *bs).1)
        .unwrap();

    low_depth_bsgs_circuit_with_baby_steps(poly_ring, polys, baby_steps)
}

#[instrument(skip_all)]
pub fn low_depth_bsgs_circuit_with_baby_steps<P>(poly_ring: P, polys: &[El<P>], baby_steps: usize) -> PlaintextCircuit<<<P::Type as RingExtension>::BaseRing as RingStore>::Type>
    where P: RingStore,
        P::Type: PolyRing
{
    let degrees = polys.iter().map(|f| poly_ring.degree(f).unwrap() as usize).collect::<Vec<_>>();
    let max_deg = degrees.iter().copied().max().unwrap();
    let ring = poly_ring.base_ring();

    let giant_steps = max_deg / baby_steps + 1;
    let giant_steps_half = giant_steps / 2 + 1;
    assert!((giant_steps - 1) * baby_steps + baby_steps > max_deg);
    assert!((giant_steps - 1) * baby_steps <= max_deg);

    // now baby_step_circuit computes (1, x, x^2, ..., x^baby_steps)
    let baby_step_circuit = compute_powers_circuit(ring, &[1], &(0..=baby_steps).collect::<Vec<_>>());
    assert_eq!(baby_steps - 1, baby_step_circuit.multiplication_gate_count());
    assert_eq!(ZZi64.abs_log2_ceil(&(baby_steps as i64)).unwrap() as usize, baby_step_circuit.max_mul_depth());
    let baby_step_circuit_mul_depth = baby_step_circuit.max_mul_depth();

    // giant_step_circuit computes (1, x, ..., x^(baby_steps - 1), 1, x^baby_steps, x^(2 baby_steps), ..., x^(floor(giant_steps / 2) * baby_steps - baby_steps))
    let giant_step_circuit = PlaintextCircuit::identity(baby_steps, ring).tensor(compute_powers_circuit(ring, &[1], &(0..giant_steps_half).collect::<Vec<_>>()), ring).compose(baby_step_circuit, ring);
    assert_eq!(baby_steps - 1 + giant_steps_half - 2, giant_step_circuit.multiplication_gate_count());
    assert_eq!(ZZi64.abs_log2_ceil(&(giant_steps_half as i64 - 1)).unwrap() as usize, giant_step_circuit.max_mul_depth() - baby_step_circuit_mul_depth);
    assert_eq!(giant_step_circuit.input_count(), 1);
    assert_eq!(giant_step_circuit.output_count(), baby_steps + giant_steps_half);

    let all_poly_parts: Vec<Vec<PlaintextCircuit<_>>> = polys.iter().map(|f: &_| (0..(poly_ring.degree(f).unwrap() / baby_steps + 1)).map(|i| PlaintextCircuit::linear_transform_ring(&(0..baby_steps).map(|j|
        ring.clone_el(poly_ring.coefficient_at(f, i * baby_steps + j))
    ).collect::<Vec<_>>(), ring)).collect()).collect();

    let select_baby_steps = PlaintextCircuit::select(baby_steps + giant_steps_half, &(0..baby_steps).collect::<Vec<_>>(), ring);

    let mut result = PlaintextCircuit::empty();
    for (poly, poly_parts) in polys.iter().zip(all_poly_parts.iter()) {

        let mut compute_poly_circuit = poly_parts[0].clone(ring).compose(select_baby_steps.clone(ring), ring);
        let highest_block = poly_ring.degree(poly).unwrap() / baby_steps;
        
        for i in 1..=(highest_block / 2) {
            assert_eq!(baby_steps + giant_steps_half, compute_poly_circuit.input_count());
            assert_eq!(1, compute_poly_circuit.output_count());

            let low_part = poly_parts[i].clone(ring);
            let high_part = poly_parts[i + highest_block / 2].clone(ring);

            let compute_part = PlaintextCircuit::mul(ring).compose(
                PlaintextCircuit::add(ring).compose(
                    low_part.compose(select_baby_steps.clone(ring), ring).tensor(
                        PlaintextCircuit::mul(ring).compose(high_part.compose(select_baby_steps.clone(ring), ring).tensor(PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + highest_block / 2], ring), ring), ring), ring
                    ), ring
                ).tensor(PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + i], ring), ring), ring
            ).compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ring).output_times(4, ring), ring);

            compute_poly_circuit = PlaintextCircuit::add(ring).compose(compute_poly_circuit.tensor(compute_part, ring), ring)
                .compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ring).output_twice(ring), ring);
        }

        if highest_block == 1 {
            let compute_part = PlaintextCircuit::mul(ring).compose(
                poly_parts[highest_block].clone(ring).compose(select_baby_steps.clone(ring), ring).tensor(
                    PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + 1], ring), ring
                ), ring
            ).compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ring).output_times(2, ring), ring);  
            compute_poly_circuit = PlaintextCircuit::add(ring).compose(compute_poly_circuit.tensor(compute_part, ring), ring)
                .compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ring).output_twice(ring), ring);
        } else if highest_block % 2 == 1 {
            let highest_block_power = PlaintextCircuit::mul(ring).compose(PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + highest_block / 2], ring).tensor(
                PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + highest_block / 2 + 1], ring), ring
            ), ring).compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ring).output_twice(ring), ring);
            let compute_part = PlaintextCircuit::mul(ring).compose(
                poly_parts[highest_block].clone(ring).compose(select_baby_steps.clone(ring), ring).tensor(highest_block_power, ring), ring
            ).compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ring).output_twice(ring), ring);
            compute_poly_circuit = PlaintextCircuit::add(ring).compose(compute_poly_circuit.tensor(compute_part, ring), ring)
                .compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ring).output_twice(ring), ring);
        }

        result = result.tensor(compute_poly_circuit, ring);
    }
    let result = result.compose(giant_step_circuit.output_times(polys.len(), ring), ring);

    let (expected_mul_depths, expected_mul_count) = low_depth_bsgs_cost(polys.as_fn().map_fn(|f| poly_ring.degree(f).unwrap() as usize), baby_steps);
    for i in 0..polys.len() {
        assert_eq!(expected_mul_depths.at(i), result.mul_depth(i));
    }
    assert_eq!(expected_mul_count, result.multiplication_gate_count());
    return result;
}

#[instrument(skip_all)]
pub fn poly_to_circuit_with_galois<P, R>(hypercube_iso: &HypercubeIsomorphism<R>, poly_ring: P, polys: &[El<P>]) -> PlaintextCircuit<R::Type>
    where P: RingStore,
        P::Type: PolyRing,
        BaseRing<P>: ZnRing + DivisibilityRing,
        R: RingStore,
        R::Type: NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    heuristic_functional_decomposition::<_, _, &ComposedHom<_, _, _, _, _>, _>(&poly_ring, polys.iter().map(|f| poly_ring.clone_el(f)).collect(), &mut |poly_ring, factors, hom| {
        let norm_based = if factors.len() == 1 && poly_ring.degree(&factors[0]).unwrap() <= hypercube_iso.slot_ring().rank() {
            poly_circuit_via_norm(hypercube_iso, poly_ring, &factors[0]).ok()
        } else {
            None
        };
        let standard = poly_to_circuit(&poly_ring, &factors).change_ring_uniform(|x| x.change_ring(|x| hom.map(x)));
        if norm_based.is_some() && norm_based.as_ref().unwrap().cost(&DEFAULT_COSTS) < standard.cost(&DEFAULT_COSTS) {
            norm_based.unwrap()
        } else {
            standard
        }
    }, &hypercube_iso.ring().inclusion().compose(ZnReductionMap::new(poly_ring.base_ring(), hypercube_iso.ring().base_ring()).unwrap()))
}

#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;
#[cfg(test)]
use feanor_math::rings::poly::dense_poly::DensePolyRing;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::feanor_math::rings::finite::FiniteRingStore;
#[cfg(test)]
use crate::feanor_math::seq::VectorView;

#[test]
fn test_compute_powers_circuit() {
    let circuit = compute_powers_circuit(ZZi64, &[0, 1, 2], &[1]);
    assert!(circuit.eq(&PlaintextCircuit::select(3, &[1], ZZi64), ZZi64, None));

    let circuit = compute_powers_circuit(ZZi64, &[0, 1, 2], &[3]);
    assert!(circuit.eq(&PlaintextCircuit::mul(ZZi64).compose(PlaintextCircuit::select(3, &[1, 2], ZZi64), ZZi64), ZZi64, None));

    let circuit = compute_powers_circuit(ZZi64, &[0, 1, 2], &[5, 7]);
    assert_eq!(2, circuit.output_count());
    assert_eq!(2, circuit.mul_depth(0));
    assert_eq!(2, circuit.mul_depth(1));
    for x in -20..=20 {
        assert_eq!(vec![ZZi64.pow(x, 5), ZZi64.pow(x, 7)], circuit.evaluate_no_galois(&[1, x, x * x], ZZi64.identity()));
    }
    
    let circuit = compute_powers_circuit(ZZi64, &[1], &[0, 1, 2, 3]);
    assert_eq!(4, circuit.output_count());
    assert_eq!(0, circuit.mul_depth(0));
    assert_eq!(0, circuit.mul_depth(1));
    assert_eq!(1, circuit.mul_depth(2));
    assert_eq!(2, circuit.mul_depth(3));
    for x in -20..=20 {
        assert_eq!(vec![1, x, x * x, x * x * x], circuit.evaluate_no_galois(&[x], ZZi64.identity()));
    }
}

#[test]
fn test_bsgs() {
    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    // 1 + 2 X^3 + 3 X^4 + 4 X^5 + 8 X^7
    let poly = P.from_terms([(1, 0), (2, 3), (3, 4), (4, 5), (8, 7)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = low_depth_bsgs_circuit_with_baby_steps(&P, &[P.clone_el(&poly)], 3);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(4, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        assert_el_eq!(Zn, P.evaluate(&poly, &x, &P.base_ring().identity()), circuit.evaluate_no_galois(&[x], P.base_ring().identity()).into_iter().next().unwrap());
    }
}

#[test]
fn test_bsgs_multiple_polys() {
    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    // 1 + 2 X^3 + 3 X^4 + 4 X^5 + 8 X^7
    let f = P.from_terms([(1, 0), (2, 3), (3, 4), (4, 5), (8, 7)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    // 2 + X + 2 X^2 + 3 X^3 + 4 X^4 + 5 X^5 + 6 X^6 + 7 X^7 + 8 X^8 + 9 X^9
    let g = P.from_terms([(2, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = low_depth_bsgs_circuit_with_baby_steps(&P, &[P.clone_el(&f), P.clone_el(&g)], 4);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(6, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().identity()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }

    // 1 + X^12
    let h = P.from_terms([(1, 0), (3, 6), (7, 9), (1, 12)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = low_depth_bsgs_circuit_with_baby_steps(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h)], 4);
    assert_eq!(5, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(5, circuit.mul_depth(2));
    assert_eq!(11, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().identity()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }

    // 1 + X + X^2 + ... + X^15 + X^16
    let l = P.from_terms((0..=16).map(|i| (Zn.one(), i)));
    let circuit = low_depth_bsgs_circuit_with_baby_steps(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h), P.clone_el(&l)], 4);
    assert_eq!(5, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(5, circuit.mul_depth(2));
    assert_eq!(5, circuit.mul_depth(3));
    assert_eq!(5 + 1 + 2 + 3 + 4, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().identity()).into_iter();
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
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().identity()).into_iter();
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
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().identity()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&l, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }
}

#[test]
fn test_heuristic_functional_decomposition() {
    let FpX = DensePolyRing::new(Zn::new(65537), "X");
    let Fp = FpX.base_ring();

    let [f] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(4)]);
    let actual = heuristic_functional_decomposition(&FpX, vec![f], &mut |_, _, _| unreachable!(), Fp.identity());
    let expected = PlaintextCircuit::square(Fp).compose(PlaintextCircuit::square(Fp), Fp);
    assert!(expected.eq(&actual, Fp, None));

    let [f] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(5)]);
    let actual = heuristic_functional_decomposition(&FpX, vec![f], &mut |_, _, _| unreachable!(), Fp.identity());
    let expected = PlaintextCircuit::mul(Fp).compose(
        PlaintextCircuit::identity(1, Fp).tensor(
            PlaintextCircuit::square(Fp).compose(PlaintextCircuit::square(Fp), Fp), 
            Fp
        ), 
        Fp
    ).compose(
        PlaintextCircuit::identity(1, Fp).output_twice(Fp), 
        Fp
    );
    assert!(expected.eq(&actual, Fp, None));

    let [f, g] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + 2 * X.pow_ref(3) - X, X.pow_ref(2) + 2 * X - 1]);
    let mut dense_part_mults = 0;
    let actual = heuristic_functional_decomposition(&FpX, vec![FpX.clone_el(&f)], &mut |FpX, polys, _| {
        assert_eq!(1, polys.len());
        assert_el_eq!(FpX, g, &polys[0]);
        let result = poly_to_circuit(FpX, &polys);
        dense_part_mults = result.multiplication_gate_count();
        return result;
    }, Fp.identity());
    assert_eq!(dense_part_mults + 2, actual.multiplication_gate_count());
    for x in -10..10 {
        let x = Fp.coerce(&ZZi64, x);
        assert_el_eq!(Fp, FpX.evaluate(&f, &x, Fp.identity()), &actual.evaluate_no_galois(&[x], Fp.identity())[0]);
    }

    let [f1, f2] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + 2 * X.pow_ref(3) - X, X.pow_ref(4) + 2 * X.pow_ref(2) - 1]);
    let mut dense_part_mults = 0;
    let actual = heuristic_functional_decomposition(&FpX, vec![FpX.clone_el(&f1), FpX.clone_el(&f2)], &mut |FpX, polys, _| {
        assert_eq!(2, polys.len());
        let result = poly_to_circuit(FpX, &polys);
        dense_part_mults = result.multiplication_gate_count();
        return result;
    }, Fp.identity());
    assert_eq!(dense_part_mults + 2, actual.multiplication_gate_count());
    for x in -10..10 {
        let x = Fp.coerce(&ZZi64, x);
        assert_el_eq!(Fp, FpX.evaluate(&f1, &x, Fp.identity()), &actual.evaluate_no_galois(&[x], Fp.identity())[0]);
        assert_el_eq!(Fp, FpX.evaluate(&f2, &x, Fp.identity()), &actual.evaluate_no_galois(&[x], Fp.identity())[1]);
    }

    let [f1, f2] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + 2 * X.pow_ref(3) - X, X.pow_ref(4) - X.pow_ref(3) + 2 * X.pow_ref(2) - 1]);
    let mut dense_part_mults = 0;
    let actual = heuristic_functional_decomposition(&FpX, vec![FpX.clone_el(&f1), FpX.clone_el(&f2)], &mut |FpX, polys, _| {
        assert_eq!(1, polys.len());
        let result = poly_to_circuit(FpX, &polys);
        dense_part_mults += result.multiplication_gate_count();
        return result;
    }, Fp.identity());
    assert_eq!(dense_part_mults + 2, actual.multiplication_gate_count());
    for x in -10..10 {
        let x = Fp.coerce(&ZZi64, x);
        assert_el_eq!(Fp, FpX.evaluate(&f1, &x, Fp.identity()), &actual.evaluate_no_galois(&[x], Fp.identity())[0]);
        assert_el_eq!(Fp, FpX.evaluate(&f2, &x, Fp.identity()), &actual.evaluate_no_galois(&[x], Fp.identity())[1]);
    }

    let Z81X = DensePolyRing::new(Zn::new(65537), "X");
    let Z81 = Z81X.base_ring();

    let [f1, f2] = Z81X.with_wrapped_indeterminate(|X| [X.pow_ref(3), 55 * X.pow_ref(9) + 9 * X.pow_ref(7) + 18 * X.pow_ref(5)]);
    let mut dense_part_mults = 0;
    let actual = heuristic_functional_decomposition(&Z81X, vec![Z81X.clone_el(&f1), Z81X.clone_el(&f2)], &mut |Z81X, polys, _| {
        assert_eq!(1, polys.len());
        let result = poly_to_circuit(Z81X, &polys);
        dense_part_mults = result.multiplication_gate_count();
        return result;
    }, Fp.identity());
    assert_eq!(dense_part_mults + 3, actual.multiplication_gate_count());
    for x in -10..10 {
        let x = Z81.coerce(&ZZi64, x);
        assert_el_eq!(Z81, FpX.evaluate(&f1, &x, Z81.identity()), &actual.evaluate_no_galois(&[x], Z81.identity())[0]);
        assert_el_eq!(Z81, FpX.evaluate(&f2, &x, Z81.identity()), &actual.evaluate_no_galois(&[x], Z81.identity())[1]);
    }
}