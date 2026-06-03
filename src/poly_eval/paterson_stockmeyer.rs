use std::cmp::{min, max};
use std::collections::{BTreeSet, HashMap};
use std::ops::RangeInclusive;

use feanor_math::divisibility::{DivisibilityRing, DivisibilityRingStore};
use feanor_math::integer::IntegerRingStore;
use feanor_math::ring::*;
use feanor_math::rings::finite::{FiniteRing, FiniteRingStore};
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use tracing::{Level, event, instrument};

use crate::circuit::{Coefficient, PlaintextCircuit};
use crate::number_ring::hypercube::isomorphism::BaseRing;
use crate::poly_eval::addition_chains::addition_chain_lengths;
use crate::poly_eval::to_circuit::compute_powers_circuit;
use crate::*;

fn minimum_somewhat_continuous_function<F>(range: RangeInclusive<usize>, mut f: F, steps: usize) -> usize
    where F: FnMut(usize) -> i64
{
    assert!(steps >= 1);
    let len = (range.end() - range.start() + 1) as usize;
    assert!(len > 0);
    if len == 1 {
        return *range.start();
    }
    let delta = max(1, len / steps);
    let approx = (*range.start()..*range.end()).step_by(delta).chain([*range.end()]).min_by_key(|x| f(*x)).unwrap();
    if delta > 1 {
        debug_assert!(2 * (len / 3) + 1 < len);
        return minimum_somewhat_continuous_function(max(*range.start(), approx.saturating_sub(len as usize / 3))..=min(*range.end(), approx + len as usize / 3), f, steps);
    } else {
        return approx;
    }
}

///
/// The evaluation strategy is as follows:
///  - compute powers `x^i` for `i` in `precomputed_powers`; this always
///    includes `1, 2, ..., k`, and usually many powers of two
///  - for a polynomial `f` of degree `d`, recursively write it as `f = q X^l + r`
///    and `r = c q + s`, where `l in split_at_monomial[d].0`. Then `f = q (X^l + c) + s`,
///    and we evaluate it by combining `x^l` and `q(x), c(x), s(x)`, which are evaluated
///    recursively;
///    "monic augmentation": as fallback, we also consider the splitting as `f + X^m = q X^l + r`
///    and `r = c q + s` with `(l, m) = split_at_monomial[d].1` and `m > deg(f)` - 
///    this might be necessary if the leading coefficient of `f` is not a unit. In that case,
///    we evaluate by combining `x^l, x^m` and `q(x), c(x), s(x)` as `f(x) = q(x) (x^l + c(x)) + s(x) - x^m`;
///  - asymptotically, we would choose l = (d + k) / 2 so that deg(c) < k and we 
///    can derive `c(x)`` from the precomputed powers; this leads to a reduction
///    `d -> 2 x (d - k)/2` on each recursive step, with means we need `log2(d/k) - 1`
///    recursive steps until we reach degree `k` and can continue with precomputed powers.
///    Thus, the total cost is `2^(log2(d/k) - 1) + k = d/(2k) + k`, which is optimized
///    at `k = sqrt(d/2)`, leading to `sqrt(2d)`. In practice, we will optimize the 
///    concrete choice of `l` using dynamic programming. 
/// 
struct PatersonStockmeyerPlan {
    split_at_monomial: Vec<(Vec<usize>, (usize, usize))>,
    k: usize,
    /// these do not necessarily include the numbers 0..=k (but may include some)
    extra_precomputed_powers: Vec<usize>,
    #[allow(unused)]
    mul_count: usize
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
#[instrument(skip_all)]
fn plan_paterson_stockmeyer_circuit(ds: &[usize]) -> PatersonStockmeyerPlan {
    let max_d = ds.iter().copied().max().unwrap();
    let max_log2_d = ZZi64.abs_log2_floor(&(max_d as i64)).unwrap_or(0);

    /// Computes the cost of evaluating a polynomial of degree `d` with splitting parameter `l`
    /// by splitting it according to the Paterson-Stockmeyer method; `power_costs[i]` should be the
    /// cost of evaluating `x^i`, excluding costs for unconditionally precomputed values. `prev_costs[i]`
    /// for `i < d` should be the cost of recursively evaluating a polynomial of degree `i`.
    fn compute_cost_for_degree(d: usize, l: usize, power_costs: &[usize], prev_costs: &[usize]) -> usize {
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

    fn compute_costs(d: usize, k: usize, power_costs: &[usize]) -> usize {
        assert!(k >= 1);
        let mut result = Vec::with_capacity(d + 1);
        result.extend((0..=k).map(|_| 0));
        for i in (k + 1)..(d + 1) {
            result.push((1..(i + 1)).map(|l| 
                compute_cost_for_degree(i, l, power_costs, &result)
            ).min().unwrap());
        }
        return result[d];
    }

    // since the general optimization problem is NP-hard, we use the following, heuristic approach:
    //  - get a rough value for the number of consecutive precomputed powers `k`
    //  - get a more precise (still heuristic) value for the set of precomputed powers, currently consisting
    //    of `k` consecutive powers, followed by powers to powers of two
    //  - get values for the splitting points `l` for each degree; this step may overestimate the actual cost,
    //    since it assumes that only the powers `precomputed_powers` are available for free for every degree,
    //    even if additional powers have been computed for lower degrees (but of course we don't know if those
    //    lower degree computations will actually be used for the final polynomial)

    // compute the rough `k`
    let max_k = max(20, 2 * (max_d as f64).sqrt().ceil() as usize);
    let min_k = max(1, ((max_d as f64).sqrt().floor() as usize / 2).saturating_sub(10));
    let mut cache = HashMap::new();
    let rough_k = minimum_somewhat_continuous_function(min_k..=max_k, |k| if let Some(res) = cache.get(&k) {
        *res
    } else {
        let mut precomputed_powers = (0..=k).chain((0..max_log2_d).map(|i| 1 << i)).collect::<Vec<_>>();
        precomputed_powers.sort();
        precomputed_powers.dedup();
        let (power_costs, _) = addition_chain_lengths(max_d, &precomputed_powers);
        let cost = ds.iter().map(|d| compute_costs(*d, k, &power_costs)).sum::<usize>() + precomputed_powers.len() - 2;
        cache.insert(k, cost as i64);
        return cost as i64;
    }, 4);

    // compute the more precise `k` and `precomputed_powers`
    let (exact_k, precomputed_powers, precomputed_powers_pow2) = (max(rough_k.saturating_sub(4), 1)..(rough_k + 9)).rev().flat_map(|k| (0..5).map(move |skipped_pow2s| (k, skipped_pow2s)))
        .map(|(k, skipped_pow2s)| {
            let precomputed_powers_pow2 = (0..max_log2_d.saturating_sub(skipped_pow2s)).map(|i| 1 << i).collect::<Vec<_>>();
            let mut precomputed_powers = (0..=k).chain((0..max_log2_d.saturating_sub(skipped_pow2s)).map(|i| 1 << i)).collect::<Vec<_>>();
            precomputed_powers.sort();
            precomputed_powers.dedup();
            return (k, precomputed_powers, precomputed_powers_pow2);
        })
        .min_by_key(|(k, precomputed_powers, _)| {
            let (power_costs, _) = addition_chain_lengths(max_d, &precomputed_powers);
            let cost = ds.iter().map(|d| compute_costs(*d, (*k).try_into().unwrap(), &power_costs)).sum::<usize>() + precomputed_powers.len() - 2;
            return cost;
        }).unwrap();
    event!(Level::INFO, "paterson_stockmeyere_k({})", exact_k);

    // compute the splitting points `l`

    /// if we split `f = f(x) = q(x) (x^l + c(x)) + s(x)`, the multiplicative depth of the result will
    /// be `max(dpt(x^l), log2(q)) + 1`; thus we cannot split to asymmetrically. The idea is that
    /// we restrict to splitting points that satisfy `log2(l), log2(d - l) <= log2(deg(f) * (1 + 2 * DEPTH_RELAX))`.
    /// In that case, the multiplicative depth increases at most by `log2(1 + 2 * DEPTH_RELAX)` on every
    /// recursion step, and also behaves very controllably in practice.
    const DEPTH_RELAX: f64 = 0.1;

    let (power_costs, _) = addition_chain_lengths(max_d, &precomputed_powers);
    let mut min_costs: Vec<usize> = Vec::new();
    min_costs.extend((0..=exact_k).map(|_| 0));
    let mut split_at_monomial = Vec::new();
    split_at_monomial.extend((0..=exact_k).map(|_| (Vec::new(), (0, 0))));
    for d in (exact_k + 1)..(max_d + 1) {
        let standard_split_possible_l = {
            let next_pow2 = 1 << ZZi64.abs_log2_ceil(&(d as i64)).unwrap();
            let min_possible_l = min(d - next_pow2 / 2, (d as f64 * (0.5 - DEPTH_RELAX)).ceil() as usize);
            let max_possible_l = max(next_pow2 / 2, (d as f64 * (0.5 + DEPTH_RELAX)).floor() as usize);
            let mut possible_l = (min_possible_l..=max_possible_l)
                .map(|l| (l, compute_cost_for_degree(d, l, &power_costs, &min_costs))).collect::<Vec<_>>();
            let min_cost = possible_l.iter().map(|(_, cost)| *cost).min().unwrap();
            possible_l.retain(|(_, cost)| *cost <= min_cost);
            min_costs.push(min_cost);
            possible_l.into_iter().map(|(l, _)| l).collect::<Vec<_>>()
        };
        let (monic_augment_l, monic_augment_m, _) = {
            let min_m = d + 1;
            let next_pow2 = 1 << ZZi64.abs_log2_ceil(&(d as i64 + 1)).unwrap();
            let max_m = next_pow2;
            (min_m..=max_m).map(|m| {
                let min_possible_l = min(m - next_pow2 / 2, (d as f64 * (0.5 - DEPTH_RELAX)).ceil() as usize);
                let max_possible_l = max(next_pow2 / 2, (d as f64 * (0.5 + DEPTH_RELAX)).floor() as usize);
                let (l, cost) = (min_possible_l..=max_possible_l)
                    .map(|l| (l, compute_cost_for_degree(d, l, &power_costs, &min_costs)))
                    .min_by_key(|(_, cost)| *cost).unwrap();
                return (l, m, cost);
            }).min_by_key(|(_, _, cost)| *cost).unwrap()
        };
        
        debug_assert!(standard_split_possible_l.len() > 0);
        split_at_monomial.push((standard_split_possible_l, (monic_augment_l, monic_augment_m)));
    }

    return PatersonStockmeyerPlan {
        k: exact_k,
        mul_count: ds.iter().map(|d| min_costs[*d]).sum::<usize>() + precomputed_powers.len() - 2,
        extra_precomputed_powers: precomputed_powers_pow2,
        split_at_monomial: split_at_monomial,
    };
}

enum PatersonStockmeyerSplit<R>
    where R: RingStore,
        R::Type: PolyRing,
        BaseRing<R>: DivisibilityRing
{
    Precomputed {
        f: El<R>
    },
    StandardSplit {
        q: Box<PatersonStockmeyerSplit<R>>,
        c: Box<PatersonStockmeyerSplit<R>>,
        s: Box<PatersonStockmeyerSplit<R>>,
        factor: El<<R::Type as RingExtension>::BaseRing>,
        l: usize
    },
    FallbackSplit {
        q: Box<PatersonStockmeyerSplit<R>>,
        c: Box<PatersonStockmeyerSplit<R>>,
        s: Box<PatersonStockmeyerSplit<R>>,
        l: usize,
        m: usize
    }
}

impl<R> PatersonStockmeyerSplit<R>
    where R: RingStore + Copy,
        R::Type: PolyRing,
        BaseRing<R>: DivisibilityRing
{
    fn is_fallback_split(&self) -> bool {
        if let PatersonStockmeyerSplit::FallbackSplit { q: _, c: _, s: _, l: _, m: _ } = self {
            true
        } else {
            false
        }
    }

    #[instrument(skip_all)]
    fn create_recursive(poly_ring: R, mut f: El<R>, plan: &PatersonStockmeyerPlan, rec_depth: usize) -> Self {
        const MAX_ATTEMPTS: usize = 3;
        let d = poly_ring.degree(&f).unwrap_or(0);
        let (splitting_points, (monic_augment_l, monic_augment_m)) = &plan.split_at_monomial[d];
        if d <= plan.k {
            return Self::Precomputed { f: f };
        } else if let Some(f_lc_inv) = poly_ring.base_ring().invert(poly_ring.lc(&f).unwrap()) {
            let lc_f = poly_ring.base_ring().clone_el(poly_ring.lc(&f).unwrap());
            poly_ring.inclusion().mul_assign_map(&mut f, f_lc_inv);

            for l in splitting_points.iter().skip(1).take(MAX_ATTEMPTS) {
                let X_l = poly_ring.from_terms([(poly_ring.base_ring().one(), *l)]);
                let (q, r) = poly_ring.div_rem_monic(poly_ring.clone_el(&f), &X_l);
                let (c, s) = poly_ring.div_rem_monic(r, &q);

                let q = PatersonStockmeyerSplit::create_recursive(poly_ring, q, plan, rec_depth + 1);
                let c = PatersonStockmeyerSplit::create_recursive(poly_ring, c, plan, rec_depth + 1);
                let s = PatersonStockmeyerSplit::create_recursive(poly_ring, s, plan, rec_depth + 1);
                if !q.is_fallback_split() && !c.is_fallback_split() && !s.is_fallback_split() {
                    return PatersonStockmeyerSplit::StandardSplit { q: Box::new(q), c: Box::new(c), s: Box::new(s), factor: lc_f, l: *l }
                }
            }
            let l = splitting_points[0];
            let X_l = poly_ring.from_terms([(poly_ring.base_ring().one(), l)]);
            let (q, r) = poly_ring.div_rem_monic(f, &X_l);
            let (c, s) = poly_ring.div_rem_monic(r, &q);
            let q = PatersonStockmeyerSplit::create_recursive(poly_ring, q, plan, rec_depth + 1);
            let c = PatersonStockmeyerSplit::create_recursive(poly_ring, c, plan, rec_depth + 1);
            let s = PatersonStockmeyerSplit::create_recursive(poly_ring, s, plan, rec_depth + 1);
            return PatersonStockmeyerSplit::StandardSplit { q: Box::new(q), c: Box::new(c), s: Box::new(s), factor: lc_f, l: l };
        } else {
            let X_l = poly_ring.from_terms([(poly_ring.base_ring().one(), *monic_augment_l)]);
            let X_m = poly_ring.from_terms([(poly_ring.base_ring().one(), *monic_augment_m)]);
            let f_ = poly_ring.add(f, X_m);
            let (q, r) = poly_ring.div_rem_monic(f_, &X_l);
            let (c, s) = poly_ring.div_rem_monic(r, &q);
            let q = PatersonStockmeyerSplit::create_recursive(poly_ring, q, plan, rec_depth + 1);
            let c = PatersonStockmeyerSplit::create_recursive(poly_ring, c, plan, rec_depth + 1);
            let s = PatersonStockmeyerSplit::create_recursive(poly_ring, s, plan, rec_depth + 1);
            return PatersonStockmeyerSplit::FallbackSplit { q: Box::new(q), c: Box::new(c), s: Box::new(s), l: *monic_augment_l, m: *monic_augment_m };
        }
    }

    #[instrument(skip_all)]
    fn required_monomials(&self, poly_ring: R, monomials: &mut BTreeSet<usize>) {
        match self {
            PatersonStockmeyerSplit::Precomputed { f } => {
                for (_, i) in poly_ring.terms(&f) {
                    if i > 0 {
                        monomials.insert(i);
                    }
                }
            },
            PatersonStockmeyerSplit::StandardSplit { q, c, s, l, factor: _ } => {
                debug_assert!(*l > 0);
                monomials.insert(*l);
                q.required_monomials(poly_ring, monomials);
                c.required_monomials(poly_ring, monomials);
                s.required_monomials(poly_ring, monomials);
            },
            PatersonStockmeyerSplit::FallbackSplit { q, c, s, l, m } => {
                debug_assert!(*l > 0);
                monomials.insert(*l);
                monomials.insert(*m);
                q.required_monomials(poly_ring, monomials);
                c.required_monomials(poly_ring, monomials);
                s.required_monomials(poly_ring, monomials);
            }
        }
    }

    #[instrument(skip_all)]
    fn to_circuit_recursive(self, poly_ring: R, input_powers: &[usize], rec_depth: usize) -> (El<R>, PlaintextCircuit<BaseRing<R>>) {
        let base_ring = poly_ring.base_ring();
        let get_power_idx = |power: usize| input_powers.iter().enumerate().filter(|(_, val)| **val == power).next().unwrap().0;
        match self {
            PatersonStockmeyerSplit::Precomputed { f } => {
                let circuit = PlaintextCircuit::add(base_ring).compose(
                    PlaintextCircuit::linear_transform_ring(
                        &input_powers.iter().copied().map(|k| base_ring.clone_el(poly_ring.coefficient_at(&f, k))).collect::<Vec<_>>(), 
                        base_ring
                    ).tensor(PlaintextCircuit::constant(base_ring.clone_el(poly_ring.coefficient_at(&f, 0)), base_ring), base_ring),
                    base_ring
                );
                return (f, circuit);
            },
            PatersonStockmeyerSplit::StandardSplit { q, c, s, l, factor } => {
                let Xl = PlaintextCircuit::select(input_powers.len(), &[get_power_idx(l)], base_ring);
                let (q, q_circuit) = q.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let (c, c_circuit) = c.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let (s, s_circuit) = s.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let f_circuit = PlaintextCircuit::linear_transform_ring(&[base_ring.clone_el(&factor)], base_ring).compose(
                    PlaintextCircuit::add(base_ring).compose(
                        PlaintextCircuit::mul(base_ring).compose(
                            PlaintextCircuit::add(base_ring).compose(Xl.tensor(c_circuit, base_ring), base_ring)
                                .tensor(q_circuit, base_ring),
                            base_ring
                        ).tensor(s_circuit, base_ring),
                        base_ring
                    ).compose(
                        PlaintextCircuit::identity(input_powers.len(), base_ring).output_times(4, base_ring),
                        base_ring
                    ),
                    base_ring
                );
                debug_assert_eq!(input_powers.len(), f_circuit.input_count());
                debug_assert_eq!(1, f_circuit.output_count());
                let Xl = poly_ring.from_terms([(base_ring.one(), l)]);
                let f = poly_ring.inclusion().mul_map(poly_ring.add(poly_ring.mul(poly_ring.add(c, Xl), q), s), factor);
                return (f, f_circuit);
            },
            PatersonStockmeyerSplit::FallbackSplit { q, c, s, l, m } => {
                let Xl = PlaintextCircuit::select(input_powers.len(), &[get_power_idx(l)], base_ring);
                let Xm = PlaintextCircuit::select(input_powers.len(), &[get_power_idx(m)], base_ring);
                let (q, q_circuit) = q.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let (c, c_circuit) = c.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let (s, s_circuit) = s.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let f_circuit = PlaintextCircuit::linear_transform(&[Coefficient::One, Coefficient::One, Coefficient::NegOne], base_ring).compose(
                    PlaintextCircuit::mul(base_ring).compose(
                        PlaintextCircuit::add(base_ring).compose(Xl.tensor(c_circuit, base_ring), base_ring)
                            .tensor(q_circuit, base_ring),
                        base_ring
                    )
                    .tensor(s_circuit, base_ring)
                    .tensor(Xm, base_ring),
                    base_ring
                ).compose(
                    PlaintextCircuit::identity(input_powers.len(), base_ring).output_times(5, base_ring),
                    base_ring
                );
                debug_assert_eq!(input_powers.len(), f_circuit.input_count());
                debug_assert_eq!(1, f_circuit.output_count());
                let Xl = poly_ring.from_terms([(poly_ring.base_ring().one(), l)]);
                let Xm = poly_ring.from_terms([(poly_ring.base_ring().one(), m)]);
                let f = poly_ring.sub(poly_ring.add(poly_ring.mul(poly_ring.add(c, Xl), q), s), Xm);
                return (f, f_circuit);
            }
        }
    }
}

///
/// Computes a circuit to evaluate the given list of polynomials, using a low-depth
/// variant of Paterson-Stockmeyer.
/// 
/// Note that Paterson-Stockmeyer requires certain intermediate polynomials to have
/// invertible coefficients.
/// 
#[instrument(skip_all)]
pub fn paterson_stockmeyer_circuit<R>(poly_ring: R, polynomials: &[El<R>]) -> PlaintextCircuit<BaseRing<R>>
    where R: RingStore,
        R::Type: PolyRing,
        BaseRing<R>: DivisibilityRing + FiniteRing
{
    let degrees = polynomials.iter().map(|f| poly_ring.degree(f).expect("all polynomials must be nonzero")).collect::<Vec<_>>();
    let plan = plan_paterson_stockmeyer_circuit(&degrees);
    assert!(plan.k >= 1);

    let mut rng = oorandom::Rand64::new(0);
    (0..10).map(|_| {
        let random_value = poly_ring.base_ring().random_element(|| rng.rand_u64());
        let mut splits = Vec::new();
        for poly in polynomials {
            let randomized_poly = poly_ring.evaluate(poly, &poly_ring.from_terms([(poly_ring.base_ring().one(), 1), (poly_ring.base_ring().clone_el(&random_value), 0)]), poly_ring.inclusion());
            splits.push(PatersonStockmeyerSplit::create_recursive(&poly_ring, randomized_poly, &plan, 0));
        }
        
        let mut precomputed_powers = BTreeSet::new();
        precomputed_powers.extend(plan.extra_precomputed_powers.iter().copied());
        for split in &splits {
            split.required_monomials(&poly_ring, &mut precomputed_powers);
        }
        debug_assert!(!precomputed_powers.contains(&0));
        let precomputed_powers = precomputed_powers.into_iter().collect::<Vec<_>>();
        let main_circuit = splits.into_iter().fold(
            PlaintextCircuit::drop(precomputed_powers.len()),
            |current, next| current.tensor(next.to_circuit_recursive(&poly_ring, &precomputed_powers, 0).1, poly_ring.base_ring())
                    .compose(PlaintextCircuit::identity(precomputed_powers.len(), poly_ring.base_ring()).output_twice(poly_ring.base_ring()), poly_ring.base_ring())
        );
        debug_assert_eq!(precomputed_powers.len(), main_circuit.input_count());
        debug_assert_eq!(polynomials.len(), main_circuit.output_count());
        
        let precompute_powers_circuit = compute_powers_circuit(poly_ring.base_ring(), &[1], &precomputed_powers);
        let de_randomize_circuit = PlaintextCircuit::add(poly_ring.base_ring()).compose(
            PlaintextCircuit::identity(1, poly_ring.base_ring()).tensor(
                PlaintextCircuit::constant(poly_ring.base_ring().negate(random_value), poly_ring.base_ring()), 
                poly_ring.base_ring()
            ), 
            poly_ring.base_ring()
        );
        return main_circuit.compose(precompute_powers_circuit, poly_ring.base_ring()).compose(de_randomize_circuit, poly_ring.base_ring());
    }).min_by_key(|circuit| circuit.multiplication_gate_count()).unwrap()
}

#[cfg(test)]
use feanor_math::homomorphism::Homomorphism;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::poly::dense_poly::DensePolyRing;
#[cfg(test)]
use crate::poly_eval::to_circuit::*;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;
#[cfg(test)]
use std::slice::from_ref;

#[test]
fn test_plan_single() {
    assert_eq!(0, plan_paterson_stockmeyer_circuit(&[1]).mul_count);
    assert_eq!(1, plan_paterson_stockmeyer_circuit(&[2]).mul_count);
    assert_eq!(2, plan_paterson_stockmeyer_circuit(&[3]).mul_count);
    assert_eq!(2, plan_paterson_stockmeyer_circuit(&[4]).mul_count);
    assert_eq!(3, plan_paterson_stockmeyer_circuit(&[5]).mul_count);
    assert_eq!(3, plan_paterson_stockmeyer_circuit(&[6]).mul_count);
    assert_eq!(4, plan_paterson_stockmeyer_circuit(&[7]).mul_count);
    assert_eq!(4, plan_paterson_stockmeyer_circuit(&[8]).mul_count);
    assert_eq!(4, plan_paterson_stockmeyer_circuit(&[9]).mul_count);
    assert_eq!(5, plan_paterson_stockmeyer_circuit(&[10]).mul_count);
}

#[test]
fn test_plan_multiple() {
    assert_eq!(
        12,
        plan_paterson_stockmeyer_circuit(&[17, 34]).mul_count
    )
}

#[test]
fn test_evaluation_circuit() {
    let FpX = DensePolyRing::new(Zn::new(65537), "X");
    let Fp = FpX.base_ring();
    let [f] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, from_ref(&f));
    assert_eq!(2, circuit.multiplication_gate_count());
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&f, &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
    }

    let [f] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, from_ref(&f));
    assert_eq!(3, circuit.multiplication_gate_count());
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&f, &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
    }

    let f = FpX.from_terms((0..=17).map(|i| (Fp.int_hom().map(1 << i), i)));
    let circuit = paterson_stockmeyer_circuit(&FpX, from_ref(&f));
    assert_eq!(7, circuit.multiplication_gate_count());
    for i in 0..20 {
        assert_el_eq!(Fp, FpX.evaluate(&f, &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
    }
}

#[test]
fn test_evaluation_circuit_multiple() {
    let FpX = DensePolyRing::new(Zn::new(65537), "X");
    let Fp = FpX.base_ring();
    let polys = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(2) - 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, &polys);
    assert_eq!(2, circuit.multiplication_gate_count());
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&polys[0], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
        assert_el_eq!(Fp, FpX.evaluate(&polys[1], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[1]);
    }

    let polys = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(4) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(2) - 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, &polys);
    assert_eq!(4, circuit.multiplication_gate_count());
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&polys[0], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
        assert_el_eq!(Fp, FpX.evaluate(&polys[1], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[1]);
        assert_el_eq!(Fp, FpX.evaluate(&polys[2], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[2]);
    }
}

#[test]
fn test_paterson_stockmeyer_monic_augmentation() {
    // no monic augmentation
    let FpX = DensePolyRing::new(Zn::new(65537 * 65537), "X");
    let Fp = FpX.base_ring();
    let [f] = FpX.with_wrapped_indeterminate(|X| [65536 * X.pow_ref(5) + 2 * X.pow_ref(4) - 4 * X + 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, from_ref(&f));
    assert_eq!(3, circuit.multiplication_gate_count());
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&f, &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
    }

    // monic augmentation
    let FpX = DensePolyRing::new(Zn::new(65537 * 65537), "X");
    let Fp = FpX.base_ring();
    let [f] = FpX.with_wrapped_indeterminate(|X| [65537 * X.pow_ref(5) + 2 * X.pow_ref(4) - 4 * X + 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, from_ref(&f));
    assert_eq!(5, circuit.multiplication_gate_count());
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&f, &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
    }
}
