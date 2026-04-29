use std::cmp::min;

use feanor_math::rings::finite::FiniteRing;
use feanor_math::divisibility::*;
use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::seq::*;
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use tracing::instrument;

use crate::circuit::Coefficient;
use crate::circuit::PlaintextCircuit;
use crate::number_ring::NumberRingQuotient;
use crate::number_ring::hypercube::isomorphism::BaseRing;
use crate::number_ring::hypercube::isomorphism::HypercubeIsomorphism;
use crate::number_ring::hypercube::isomorphism::SlotRingOf;
use crate::poly_eval::paterson_stockmeyer::paterson_stockmeyer_circuit;
use crate::*;

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
    heuristic_decomposition(
        &poly_ring, 
        polys.iter().map(|f| poly_ring.clone_el(f)).collect(), 
        |poly_ring, polys, _| {
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
/// Detects common kinds of structure in the given polynomial that can be exploited
/// for more efficient evaluation.
/// 
/// Currently, this is only a check if the polynomial is even or odd.
/// 
#[instrument(skip_all)]
pub fn heuristic_decomposition<P, R, H, F>(poly_ring: P, to_evaluate: Vec<El<P>>, mut factors_to_circuit: F, hom: H) -> PlaintextCircuit<R>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        BaseRing<P>: DivisibilityRing,
        F: FnMut(P, Vec<El<P>>, H) -> PlaintextCircuit<R>,
        R: ?Sized + RingBase,
        H: Copy + Homomorphism<BaseRing<P>, R>
{
    assert!(hom.domain().get_ring() == poly_ring.base_ring().get_ring());
    if to_evaluate.len() == 0 {
        return PlaintextCircuit::empty();
    }
    let circuit_ring = hom.codomain();

    let mut nontrivial_operation = false;
    let mut precompute_square = false;
    let mut polynomials = Vec::new();
    let mut pre_circuits = Vec::new();
    let mut post_circuits = Vec::new();

    for f in to_evaluate {
        let d = poly_ring.degree(&f).unwrap();
        let current_output_idx = polynomials.len() + 1;
        if d == 0 {
            nontrivial_operation = true;
            post_circuits.push(PlaintextCircuit::constant(hom.map_ref(poly_ring.coefficient_at(&f, 0)), circuit_ring));
        } else if d == 1 {
            nontrivial_operation = true;
            post_circuits.push(PlaintextCircuit::add(circuit_ring).compose(
                PlaintextCircuit::constant(hom.map_ref(poly_ring.coefficient_at(&f, 0)), circuit_ring).tensor(
                    PlaintextCircuit::linear_transform_ring(&[hom.map_ref(poly_ring.coefficient_at(&f, 1))], circuit_ring), 
                    circuit_ring
                ),
                circuit_ring
            ));
        } else if (1..=d).step_by(2).all(|i| poly_ring.base_ring().is_zero(poly_ring.coefficient_at(&f, i))) {
            nontrivial_operation = true;
            precompute_square = true;
            let factored_poly = poly_ring.from_terms(poly_ring.terms(&f).map(|(c, i)| (poly_ring.base_ring().clone_el(c), i.checked_div(2).unwrap())));
            polynomials.push(factored_poly);
            pre_circuits.push(PlaintextCircuit::select(2, &[1], circuit_ring));
            post_circuits.push(PlaintextCircuit::select(current_output_idx + 1, &[current_output_idx], circuit_ring))
        } else if (0..=d).step_by(2).all(|i| poly_ring.base_ring().is_zero(poly_ring.coefficient_at(&f, i))) {
            nontrivial_operation = true;
            precompute_square = true;
            let factored_poly = poly_ring.from_terms(poly_ring.terms(&f).map(|(c, i)| (poly_ring.base_ring().clone_el(c), i.checked_sub(1).unwrap().checked_div(2).unwrap())));
            polynomials.push(factored_poly);
            pre_circuits.push(PlaintextCircuit::select(2, &[1], circuit_ring));
            post_circuits.push(PlaintextCircuit::mul(circuit_ring).compose(PlaintextCircuit::select(current_output_idx + 1, &[0, current_output_idx], circuit_ring), circuit_ring));
        } else {
            polynomials.push(f);
            pre_circuits.push(PlaintextCircuit::select(1, &[0], circuit_ring));
            post_circuits.push(PlaintextCircuit::select(current_output_idx + 1, &[current_output_idx], circuit_ring));
        }
    }

    if nontrivial_operation {
        let polynomials_len = polynomials.len();
        let main_circuit = heuristic_decomposition::<P, R, H, F>(poly_ring, polynomials, factors_to_circuit, hom);
        assert_eq!(main_circuit.output_count(), polynomials_len);

        let pre_stage_inputs = if precompute_square { 2 } else { 1 };
        let mut pre_circuit = pre_circuits.into_iter().fold(
            PlaintextCircuit::drop(pre_stage_inputs), 
            |current: PlaintextCircuit<_>, pre_circuit| {
                let pad_count = pre_stage_inputs - pre_circuit.input_count();
                current.tensor(
                    pre_circuit.tensor(
                        PlaintextCircuit::drop(pad_count),
                        circuit_ring
                    ),
                    circuit_ring
                ).compose(
                    PlaintextCircuit::identity(pre_stage_inputs, circuit_ring).output_twice(circuit_ring),
                    circuit_ring
                )
            }
        );
        if precompute_square {
            pre_circuit = pre_circuit.compose(
                PlaintextCircuit::identity(1, circuit_ring).tensor(
                    PlaintextCircuit::square(circuit_ring), 
                    circuit_ring
                ).compose(
                    PlaintextCircuit::identity(1, circuit_ring).output_times(pre_stage_inputs, circuit_ring), 
                    circuit_ring
                ), 
                circuit_ring
            );
        }
        assert_eq!(1, pre_circuit.input_count());
        assert_eq!(polynomials_len, pre_circuit.output_count());

        let main_stage_outputs = polynomials_len + 1;
        let post_circuit = post_circuits.into_iter().fold(
            PlaintextCircuit::drop(main_stage_outputs),
            |current: PlaintextCircuit<_>, post_circuit| {
                let pad_count = main_stage_outputs - post_circuit.input_count();
                current.tensor(
                    post_circuit.tensor(
                        PlaintextCircuit::drop(pad_count),
                        circuit_ring
                    ),
                    circuit_ring
                ).compose(
                    PlaintextCircuit::identity(main_stage_outputs, circuit_ring).output_twice(circuit_ring),
                    circuit_ring
                )
            }
        );
        return post_circuit.compose(
            PlaintextCircuit::identity(1, circuit_ring).tensor(
                main_circuit.compose(pre_circuit, circuit_ring), 
                circuit_ring
            ).compose(
                PlaintextCircuit::identity(1, circuit_ring).output_twice(circuit_ring), 
                circuit_ring
            ),
            circuit_ring
        );
    } else {
        return factors_to_circuit(poly_ring, polynomials, hom);
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

fn compute_power_circuit<R>(ring: R, deg_exclusive: usize) -> PlaintextCircuit<R::Type>
    where R: RingStore + Copy
{
    let mut result = PlaintextCircuit::constant(ring.one(), ring).tensor(PlaintextCircuit::identity(1, ring), ring);
    while result.output_count() < deg_exclusive {
        let l = result.output_count();
        if l % 2 == 0 {
            result = PlaintextCircuit::identity(l, ring).tensor(
                PlaintextCircuit::square(ring).compose(PlaintextCircuit::select(l, &[l / 2], ring), ring), ring
            ).compose(
                result.output_twice(ring), ring
            );
        } else {
            result = PlaintextCircuit::identity(l, ring).tensor(
                PlaintextCircuit::mul(ring).compose(PlaintextCircuit::select(l, &[l / 2, l - (l / 2)], ring), ring), ring
            ).compose(
                result.output_twice(ring), ring
            );
        }
        assert_eq!(l + 1, result.output_count());
    }
    assert!(result.output_count() == deg_exclusive);
    return result;
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
    let baby_step_circuit = compute_power_circuit(ring, baby_steps + 1);
    assert_eq!(baby_steps - 1, baby_step_circuit.multiplication_gate_count());
    assert_eq!(ZZi64.abs_log2_ceil(&(baby_steps as i64)).unwrap() as usize, baby_step_circuit.max_mul_depth());
    let baby_step_circuit_mul_depth = baby_step_circuit.max_mul_depth();

    // giant_step_circuit computes (1, x, ..., x^(baby_steps - 1), 1, x^baby_steps, x^(2 baby_steps), ..., x^(floor(giant_steps / 2) * baby_steps - baby_steps))
    let giant_step_circuit = PlaintextCircuit::identity(baby_steps, ring).tensor(compute_power_circuit(ring, giant_steps_half), ring).compose(baby_step_circuit, ring);
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
pub fn poly_to_circuit_with_galois<P, R, H>(hypercube_iso: &HypercubeIsomorphism<R>, poly_ring: P, polys: &[El<P>], hom: H) -> PlaintextCircuit<R::Type>
    where P: RingStore,
        P::Type: PolyRing,
        BaseRing<P>: FiniteRing + DivisibilityRing,
        R: RingStore,
        R::Type: NumberRingQuotient,
        BaseRing<R>: NiceZn,
        H: Homomorphism<BaseRing<P>, <SlotRingOf<R> as RingStore>::Type>
{
    heuristic_decomposition(&poly_ring, polys.iter().map(|f| poly_ring.clone_el(f)).collect(), |poly_ring, factors, hom| {
        unimplemented!()
    }, &hom).change_ring_uniform(|x| match x {
        Coefficient::One => Coefficient::One,
        Coefficient::NegOne => Coefficient::NegOne,
        Coefficient::Zero => Coefficient::Zero,
        Coefficient::Integer(x) => Coefficient::Integer(x),
        Coefficient::Other(x) => Coefficient::Other(hypercube_iso.from_slot_values((0..hypercube_iso.slot_count()).map(|_| hypercube_iso.slot_ring().clone_el(&x))))
    })
}


#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::finite::FiniteRingStore;
#[cfg(test)]
use feanor_math::rings::poly::dense_poly::DensePolyRing;

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
