use std::cmp::{min, max};
use std::slice::from_ref;

use feanor_math::divisibility::{DivisibilityRing, DivisibilityRingStore};
use feanor_math::integer::IntegerRingStore;
use feanor_math::ring::*;
use feanor_math::rings::poly::{PolyRing, PolyRingStore};

use crate::circuit::PlaintextCircuit;
use crate::*;

///
/// The evaluation strategy is as follows:
///  - compute powers `x^i` for `i` in `precomputed_powers`; this always
///    includes `1, 2, ..., k`, and usually many powers of two
///  - for a polynomial `f` of degree `d`, recursively write it as `f = q X^l + r`
///    and `r = c q + s`, where `l = split_at_monomial[d]`. Then `f = q (X^l + c) + s`,
///    and we evaluate it by combining `x^l` and `q(x), c(x), s(x)`, which are evaluated
///    recursively 
/// 
struct PatersonStockmeyerPlan {
    split_at_monomial: Vec<Vec<usize>>,
    k: usize,
    precomputed_powers: Vec<usize>,
    addition_chains: Vec<usize>,
    total_mult_count: usize
}

fn addition_chain_lengths(k: usize, available: &[usize]) -> (Vec<usize>, Vec<usize>) {
    let mut costs = Vec::new();
    let mut next = Vec::new();
    let mut available_i = 0;
    for i in 0..=k {
        if available_i < available.len() && i == available[available_i] {
            costs.push(0);
            next.push(i);
            available_i += 1;
        } else {
            let j = (1..i).min_by_key(|j| costs[*j] + costs[i - j] + 1).unwrap();
            costs.push(costs[j] + costs[i - j] + 1);
            next.push(j);
        }
    }
    return (costs, next);
}

///
/// This function accurately estimates the cost for our variant of Paterson-Stockmeyer
/// evaluation of generic polynomials of the given degrees (as explained in [`PatersonStockmeyerPlan`]), 
/// and picks the choice leading to the smallest number of multiplications, under the restriction of
/// having optimal multiplicative depth.
/// 
/// However, the heuristic is in general not optimal. Also, we assume that the underlying
/// ring is a field. If there are zero-divisors, the plan cannot be used as-is. Nevertheless,
/// we currently base the evaluation on the plan, and if we encounter a leading coefficient
/// that is a zero divisor, we improvise later. 
/// 
fn plan_paterson_stockmeyer_circuit(ds: &[usize]) -> PatersonStockmeyerPlan {
    let max_d = *ds.iter().max().unwrap();
    let max_log2_d = ZZi64.abs_log2_floor(&(max_d as i64)).unwrap_or(0);
    let max_k = max(20, 2 * (max_d as f64).sqrt().ceil() as usize);
    let min_k = max(1, ((max_d as f64).sqrt().floor() as usize / 2).saturating_sub(10));

    fn compute_cost_split(d: usize, l: usize, power_costs: &[usize], prev_costs: &[usize]) -> usize {
        let deg_q = d.saturating_sub(l);
        let deg_c = l.saturating_sub(deg_q + 1);
        let deg_s = min(deg_q.saturating_sub(1), l - 1);
        let max_degree_mult_depth = 1 << ZZi64.abs_log2_ceil(&(d as i64)).unwrap().saturating_sub(1);
        if deg_q > max_degree_mult_depth || deg_c > max_degree_mult_depth || l > max_degree_mult_depth  {
            usize::MAX
        } else {
            prev_costs[deg_q] + prev_costs[deg_c] + prev_costs[deg_s] + power_costs[l] + 1
        }
    }

    fn get_mult_number(d: usize, k: usize, power_costs: &[usize]) -> usize {
        assert!(k >= 1);
        let mut result = Vec::with_capacity(d + 1);
        result.extend((0..=k).map(|_| 0));
        for i in (k + 1)..(d + 1) {
            result.push((1..(i + 1)).map(|l| 
                compute_cost_split(i, l, power_costs, &result)
            ).min().unwrap());
        }
        return result[d];
    }

    // iterate through the k in backwards order; while in the ideal case, it does not
    // matter how large k is, larger available k often make modifications to the ideal
    // circuit (e.g. when we improvise later) more efficient
    let rough_k = (min_k..(max_k + 1)).step_by(4).rev().min_by_key(|k| {
        let mut precomputed_powers = (0..=*k).chain((0..max_log2_d).map(|i| 1 << i)).collect::<Vec<_>>();
        precomputed_powers.sort();
        precomputed_powers.dedup();
        let (power_costs, _) = addition_chain_lengths(max_d, &precomputed_powers);
        return ds.iter().map(|d| get_mult_number(*d, *k, &power_costs)).sum::<usize>() + precomputed_powers.len() - 2;
    }).unwrap();

    let (exact_k, precomputed_powers) = (max(rough_k.saturating_sub(4), 1)..(rough_k + 9)).rev().flat_map(|k| (0..5).map(move |skipped_pow2s| (k, skipped_pow2s)))
        .map(|(k, skipped_pow2s)| {
            let mut precomputed_powers = (0..=k).chain((0..max_log2_d.saturating_sub(skipped_pow2s)).map(|i| 1 << i)).collect::<Vec<_>>();
            precomputed_powers.sort();
            precomputed_powers.dedup();
            return (k, precomputed_powers);
        })
        .min_by_key(|(k, precomputed_powers)| {
            let (power_costs, _) = addition_chain_lengths(max_d, &precomputed_powers);
        return ds.iter().map(|d| get_mult_number(*d, *k, &power_costs)).sum::<usize>() + precomputed_powers.len() - 2;
        }).unwrap();

    let (power_costs, addition_chains) = addition_chain_lengths(max_d, &precomputed_powers);
    let mut costs: Vec<usize> = Vec::with_capacity(max_d + 1);
    costs.extend((0..=exact_k).map(|_| 0));
    let mut split_at_monomial = Vec::with_capacity(max_d + 1);
    split_at_monomial.extend((0..=exact_k).map(|_| Vec::new()));
    for i in (exact_k + 1)..(max_d + 1) {
        let mut possible_ls = Vec::new();
        let mut min_cost = usize::MAX;
        for l in 1..=i {
            let cost = compute_cost_split(i, l, &power_costs, &costs);
            if cost < min_cost {
                min_cost = cost;
                possible_ls.clear();
                possible_ls.push(l);
            } else if cost == min_cost {
                possible_ls.push(l);
            }
        }
        costs.push(min_cost);
        split_at_monomial.push(possible_ls);
    }

    return PatersonStockmeyerPlan {
        k: exact_k,
        total_mult_count: ds.iter().map(|d| costs[*d]).sum::<usize>() + precomputed_powers.len() - 2,
        precomputed_powers: precomputed_powers,
        addition_chains: addition_chains,
        split_at_monomial: split_at_monomial,
    };
}

///
/// Computes a circuit to evaluate the given list of polynomials, using a variant
/// of Paterson-Stockmeyer.
/// 
/// The polynomials are required to have invertible leading coefficients, since
/// polynomial division is part of Paterson-Stockmeyer. The used variant is
/// depth-aware, and each circuit output will have a low multiplicative depth.
/// Parameters are optimized according to a heuristic, which usually results in
/// very efficient circuits.
/// 
pub fn paterson_stockmeyer_circuit<R>(poly_ring: R, polynomials: &[El<R>]) -> PlaintextCircuit<<<R::Type as RingExtension>::BaseRing as RingStore>::Type>
    where R: RingStore,
        R::Type: PolyRing,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: DivisibilityRing
{
    let degrees = polynomials.iter().map(|f| poly_ring.degree(f).expect("all polynomials must be nonzero")).collect::<Vec<_>>();
    let plan = plan_paterson_stockmeyer_circuit(&degrees);
    assert!(plan.k >= 1);

    let mut precomputed_powers_circuit = PlaintextCircuit::constant(poly_ring.base_ring().one(), poly_ring.base_ring())
        .tensor(PlaintextCircuit::identity(1, poly_ring.base_ring()), poly_ring.base_ring());
    for i in 2..=plan.k {
        precomputed_powers_circuit = PlaintextCircuit::identity(i, poly_ring.base_ring()).tensor(
            PlaintextCircuit::mul(poly_ring.base_ring()).compose(PlaintextCircuit::select(i, &[i/2, i - i/2], poly_ring.base_ring()), poly_ring.base_ring()), 
            poly_ring.base_ring()
        ).compose(precomputed_powers_circuit.output_twice(poly_ring.base_ring()), poly_ring.base_ring());
        debug_assert_eq!(i + 1, precomputed_powers_circuit.output_count());
    }
    let k = plan.k;
    assert_eq!(k, plan.precomputed_powers[k]);
    if plan.precomputed_powers.len() > k + 1 {
        let power = plan.precomputed_powers[k + 1];
        assert!(power % 2 == 0);
        precomputed_powers_circuit = PlaintextCircuit::identity(k + 1, poly_ring.base_ring()).tensor(
            PlaintextCircuit::square(poly_ring.base_ring()).compose(PlaintextCircuit::select(k + 1, &[power / 2], poly_ring.base_ring()), poly_ring.base_ring()), 
            poly_ring.base_ring()
        ).compose(precomputed_powers_circuit.output_twice(poly_ring.base_ring()), poly_ring.base_ring());
    }
    for i in (k + 2)..plan.precomputed_powers.len() {
        assert_eq!(2 * plan.precomputed_powers[i - 1], plan.precomputed_powers[i]);
        precomputed_powers_circuit = PlaintextCircuit::identity(i, poly_ring.base_ring()).tensor(
            PlaintextCircuit::square(poly_ring.base_ring()).compose(PlaintextCircuit::select(i, &[i - 1], poly_ring.base_ring()), poly_ring.base_ring()), 
            poly_ring.base_ring()
        ).compose(precomputed_powers_circuit.output_twice(poly_ring.base_ring()), poly_ring.base_ring());
    }
    assert_eq!(plan.precomputed_powers.len(), precomputed_powers_circuit.output_count());

    fn compute_monomial_recursive<R>(ring: R, power: usize, plan: &PatersonStockmeyerPlan) -> PlaintextCircuit<R::Type>
        where R: RingStore + Copy
    {
        if power == plan.addition_chains[power] {
            let idx = plan.precomputed_powers.iter().enumerate().filter(|(_, x)| **x == power).next().unwrap().0;
            PlaintextCircuit::select(plan.precomputed_powers.len(), &[idx], ring)
        } else {
            let prev = plan.addition_chains[power];
            PlaintextCircuit::mul(ring).compose(
                compute_monomial_recursive(ring, prev, plan).tensor(compute_monomial_recursive(ring, power - prev, plan), ring), 
                ring
            ).compose(PlaintextCircuit::identity(plan.precomputed_powers.len(), ring).output_twice(ring), ring)
        }
    }

    fn poly_circuit_recursive<R>(poly_ring: R, mut f: El<R>, plan: &PatersonStockmeyerPlan) -> PlaintextCircuit<<<R::Type as RingExtension>::BaseRing as RingStore>::Type>
        where R: RingStore + Copy,
            R::Type: PolyRing,
            <<R::Type as RingExtension>::BaseRing as RingStore>::Type: DivisibilityRing
    {
        let d = poly_ring.degree(&f).unwrap_or(0);
        if d <= plan.k {
            PlaintextCircuit::linear_transform_ring(
                &(0..=plan.k).map(|i| poly_ring.base_ring().clone_el(poly_ring.coefficient_at(&f, i))).collect::<Vec<_>>(),
                poly_ring.base_ring()
            ).compose(PlaintextCircuit::select(plan.precomputed_powers.len(), &(0..=plan.k).collect::<Vec<_>>(), poly_ring.base_ring()), poly_ring.base_ring())
        } else {
            let f_lc = poly_ring.base_ring().clone_el(poly_ring.lc(&f).unwrap());
            let f_lc_inv = poly_ring.base_ring().invert(&f_lc).expect("polynomial must have invertible lc");
            poly_ring.inclusion().mul_assign_map(&mut f, f_lc_inv);

            for l in &plan.split_at_monomial[d] {
                let X_l = poly_ring.from_terms([(poly_ring.base_ring().one(), *l)]);
                let (q, r) = poly_ring.div_rem_monic(poly_ring.clone_el(&f), &X_l);
                let (c, s) = poly_ring.div_rem_monic(r, &q);
                if (poly_ring.degree(&c).unwrap_or(0) <= plan.k || poly_ring.base_ring().is_unit(poly_ring.lc(&c).unwrap())) &&
                    (poly_ring.degree(&s).unwrap_or(0) <= plan.k || poly_ring.base_ring().is_unit(poly_ring.lc(&s).unwrap()))
                {
                    let c_Xl = PlaintextCircuit::add(poly_ring.base_ring()).compose(
                        poly_circuit_recursive(poly_ring, c, plan).tensor(compute_monomial_recursive(poly_ring.base_ring(), *l, plan), poly_ring.base_ring()),
                        poly_ring.base_ring()
                    ).compose(PlaintextCircuit::identity(plan.precomputed_powers.len(), poly_ring.base_ring()).output_twice(poly_ring.base_ring()), poly_ring.base_ring());
                    let q_c_Xl = PlaintextCircuit::mul(poly_ring.base_ring()).compose(
                        poly_circuit_recursive(poly_ring, q, plan).tensor(c_Xl, poly_ring.base_ring()),
                        poly_ring.base_ring()
                    ).compose(PlaintextCircuit::identity(plan.precomputed_powers.len(), poly_ring.base_ring()).output_twice(poly_ring.base_ring()), poly_ring.base_ring());
                    
                    return PlaintextCircuit::vec_mul_scalar(from_ref(&f_lc), poly_ring.base_ring())
                        .compose(PlaintextCircuit::add(poly_ring.base_ring()), poly_ring.base_ring())
                        .compose(
                            q_c_Xl.tensor(poly_circuit_recursive(poly_ring, s, plan), poly_ring.base_ring()),
                            poly_ring.base_ring()
                        ).compose(PlaintextCircuit::identity(plan.precomputed_powers.len(), poly_ring.base_ring()).output_twice(poly_ring.base_ring()), poly_ring.base_ring());
                }
            }
            unimplemented!("in this special case, Paterson-Stockmeyer fails, and no fix is currently implemented")
        }
    }

    let mut result = PlaintextCircuit::empty();
    for f in polynomials {
        result = result.tensor(poly_circuit_recursive(&poly_ring, poly_ring.clone_el(f), &plan), poly_ring.base_ring());
    }

    result = result.compose(precomputed_powers_circuit.output_times(degrees.len(), poly_ring.base_ring()), poly_ring.base_ring());
    assert_eq!(plan.total_mult_count, result.multiplication_gate_count());
    assert_eq!(degrees.len(), result.output_count());
    for i in 0..degrees.len() {
        assert_eq!(ZZi64.abs_log2_ceil(&(degrees[i] as i64)).unwrap_or(0), result.mul_depth(i));
    }
    return result;
}

#[cfg(test)]
use feanor_math::homomorphism::Homomorphism;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::poly::dense_poly::DensePolyRing;
#[cfg(test)]
use feanor_math::rings::rational::RationalField;

#[test]
fn print() {
    println!("{}", plan_paterson_stockmeyer_circuit(&[17, 17, 33]).total_mult_count + plan_paterson_stockmeyer_circuit(&[17]).total_mult_count);
}

#[test]
fn test_plan() {
    for d in 1..11 {
        assert_eq!(
            [0, 0, 1, 2, 2, 3, 3, 4, 4, 4, 5][d], 
            plan_paterson_stockmeyer_circuit(&[d]).total_mult_count
        );
    }
}

#[test]
fn test_plan_multiple() {
    assert_eq!(
        12,
        plan_paterson_stockmeyer_circuit(&[17, 34]).total_mult_count
    )
}

#[test]
fn test_evaluation_circuit() {
    let QQX = DensePolyRing::new(RationalField::new(ZZbig), "X");
    let QQ = QQX.base_ring();
    let [f] = QQX.with_wrapped_indeterminate(|X| [X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1]);
    let circuit = paterson_stockmeyer_circuit(&QQX, from_ref(&f));
    for i in 0..10 {
        assert_el_eq!(QQ, QQX.evaluate(&f, &QQ.int_hom().map(i), QQ.identity()), circuit.evaluate_no_galois(&[QQ.int_hom().map(i)], QQ.identity())[0]);
    }

    let [f] = QQX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1]);
    let circuit = paterson_stockmeyer_circuit(&QQX, from_ref(&f));
    for i in 0..10 {
        assert_el_eq!(QQ, QQX.evaluate(&f, &QQ.int_hom().map(i), QQ.identity()), circuit.evaluate_no_galois(&[QQ.int_hom().map(i)], QQ.identity())[0]);
    }

    let f = QQX.from_terms((0..=17).map(|i| (QQ.int_hom().map(1 << i), i)));
    let circuit = paterson_stockmeyer_circuit(&QQX, from_ref(&f));
    for i in 0..20 {
        assert_el_eq!(QQ, QQX.evaluate(&f, &QQ.int_hom().map(i), QQ.identity()), circuit.evaluate_no_galois(&[QQ.int_hom().map(i)], QQ.identity())[0]);
    }
}

#[test]
fn test_evaluation_circuit_multiple() {
    let QQX = DensePolyRing::new(RationalField::new(ZZbig), "X");
    let QQ = QQX.base_ring();
    let polys = QQX.with_wrapped_indeterminate(|X| [X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(2) - 1]);
    let circuit = paterson_stockmeyer_circuit(&QQX, &polys);
    for i in 0..10 {
        assert_el_eq!(QQ, QQX.evaluate(&polys[0], &QQ.int_hom().map(i), QQ.identity()), circuit.evaluate_no_galois(&[QQ.int_hom().map(i)], QQ.identity())[0]);
        assert_el_eq!(QQ, QQX.evaluate(&polys[1], &QQ.int_hom().map(i), QQ.identity()), circuit.evaluate_no_galois(&[QQ.int_hom().map(i)], QQ.identity())[1]);
    }

    let polys = QQX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(2) - 1]);
    let circuit = paterson_stockmeyer_circuit(&QQX, &polys);
    for i in 0..10 {
        assert_el_eq!(QQ, QQX.evaluate(&polys[0], &QQ.int_hom().map(i), QQ.identity()), circuit.evaluate_no_galois(&[QQ.int_hom().map(i)], QQ.identity())[0]);
        assert_el_eq!(QQ, QQX.evaluate(&polys[1], &QQ.int_hom().map(i), QQ.identity()), circuit.evaluate_no_galois(&[QQ.int_hom().map(i)], QQ.identity())[1]);
        assert_el_eq!(QQ, QQX.evaluate(&polys[2], &QQ.int_hom().map(i), QQ.identity()), circuit.evaluate_no_galois(&[QQ.int_hom().map(i)], QQ.identity())[2]);
    }
}