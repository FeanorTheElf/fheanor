use std::cmp::{min, max};
use std::collections::{BTreeSet, HashMap};
use std::ops::RangeInclusive;

use feanor_math::divisibility::{DivisibilityRing, DivisibilityRingStore};
use feanor_math::integer::IntegerRingStore;
use feanor_math::ring::*;
use feanor_math::rings::finite::{FiniteRing, FiniteRingStore};
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use tracing::{Level, event, instrument};

use crate::circuit::PlaintextCircuit;
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
///    and `r = c q + s`, where `l = split_at_monomial[d]`. Then `f = q (X^l + c) + s`,
///    and we evaluate it by combining `x^l` and `q(x), c(x), s(x)`, which are evaluated
///    recursively 
///  - asymptotically, we would choose l = (d + k) / 2 so that deg(c) < k and we 
///    can derive `c(x)`` from the precomputed powers; this leads to a reduction
///    `d -> 2 x (d - k)/2` on each recursive step, with means we need `log2(d/k) - 1`
///    recursive steps until we reach degree `k` and can continue with precomputed powers.
///    Thus, the total cost is `2^(log2(d/k) - 1) + k = d/(2k) + k`, which is optimized
///    at `k = sqrt(d/2)`, leading to `sqrt(2d)`. In practice, we will optimize the 
///    concrete choice of `l` using dynamic programming. 
/// 
struct PatersonStockmeyerPlan {
    split_at_monomial: Vec<Vec<usize>>,
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
        let cost = ds.iter().map(|d| get_mult_number(*d, k, &power_costs)).sum::<usize>() + precomputed_powers.len() - 2;
        cache.insert(k, cost as i64);
        return cost as i64;
    }, 4);

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
            let cost = ds.iter().map(|d| get_mult_number(*d, (*k).try_into().unwrap(), &power_costs)).sum::<usize>() + precomputed_powers.len() - 2;
            return cost;
        }).unwrap();
    event!(Level::INFO, "paterson_stockmeyere_k({})", exact_k);

    const DEPTH_RELAX: f64 = 0.1;
    const MUL_COUNT_RELAX: usize = 0;

    let (power_costs, _) = addition_chain_lengths(max_d, &precomputed_powers);
    let mut min_costs: Vec<usize> = Vec::new();
    min_costs.extend((0..=exact_k).map(|_| 0));
    let mut split_at_monomial = Vec::new();
    split_at_monomial.extend((0..=exact_k).map(|_| Vec::new()));
    for d in (exact_k + 1)..(max_d + 1) {
        let next_pow2 = 1 << ZZi64.abs_log2_ceil(&(d as i64)).unwrap();
        let min_possible_l = min(d - next_pow2 / 2, (d as f64 * (0.5 - DEPTH_RELAX)).floor() as usize);
        let max_possible_l = max(next_pow2 / 2, (d as f64 * (0.5 + DEPTH_RELAX)).ceil() as usize);
        let mut possible_l = (min_possible_l..=max_possible_l)
            .map(|l| (l, compute_cost_split(d, l, &power_costs, &min_costs))).collect::<Vec<_>>();
        let min_cost = possible_l.iter().map(|(_, cost)| *cost).min().unwrap();
        possible_l.retain(|(_, cost)| *cost <= min_cost + MUL_COUNT_RELAX);
        min_costs.push(min_cost);
        split_at_monomial.push(possible_l.into_iter().map(|(l, _)| l).collect());
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
    InnerNode {
        q: Box<PatersonStockmeyerSplit<R>>,
        c: Box<PatersonStockmeyerSplit<R>>,
        s: Box<PatersonStockmeyerSplit<R>>,
        factor: El<<R::Type as RingExtension>::BaseRing>,
        l: usize
    }
}

impl<R> PatersonStockmeyerSplit<R>
    where R: RingStore + Copy,
        R::Type: PolyRing,
        BaseRing<R>: DivisibilityRing
{
    fn create_recursive(poly_ring: R, mut f: El<R>, plan: &PatersonStockmeyerPlan, rec_depth: usize) -> Result<Self, ()> {
        const MAX_ATTEMPTS: usize = 3;
        let d = poly_ring.degree(&f).unwrap_or(0);
        if d <= plan.k {
            return Ok(Self::Precomputed { f: f });
        } else if let Some(f_lc_inv) = poly_ring.base_ring().invert(poly_ring.lc(&f).unwrap()) {
            let lc_f = poly_ring.base_ring().clone_el(poly_ring.lc(&f).unwrap());
            poly_ring.inclusion().mul_assign_map(&mut f, f_lc_inv);

            for l in plan.split_at_monomial[d].iter().take(MAX_ATTEMPTS) {
                // println!("{}[{}] trying split at {}", "  ".repeat(rec_depth), d, l);
                let X_l = poly_ring.from_terms([(poly_ring.base_ring().one(), *l)]);
                let (q, r) = poly_ring.div_rem_monic(poly_ring.clone_el(&f), &X_l);
                let (c, s) = poly_ring.div_rem_monic(r, &q);

                match (
                    PatersonStockmeyerSplit::create_recursive(poly_ring, q, plan, rec_depth + 1),
                    PatersonStockmeyerSplit::create_recursive(poly_ring, c, plan, rec_depth + 1),
                    PatersonStockmeyerSplit::create_recursive(poly_ring, s, plan, rec_depth + 1)
                ) {
                    (Ok(q), Ok(c), Ok(s)) => return Ok(Self::InnerNode { q: Box::new(q), c: Box::new(c), s: Box::new(s), l: *l, factor: lc_f }),
                    _ => {}
                }
            }
            return Err(());
        } else {
            return Err(());
        }
    }

    fn requried_monomials(&self, poly_ring: R, monomials: &mut BTreeSet<usize>) {
        match self {
            PatersonStockmeyerSplit::Precomputed { f } => {
                for (_, i) in poly_ring.terms(&f) {
                    if i > 0 {
                        monomials.insert(i);
                    }
                }
            },
            PatersonStockmeyerSplit::InnerNode { q, c, s, l, factor: _ } => {
                assert!(*l > 0);
                monomials.insert(*l);
                q.requried_monomials(poly_ring, monomials);
                c.requried_monomials(poly_ring, monomials);
                s.requried_monomials(poly_ring, monomials);
            }
        }
    }

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
            PatersonStockmeyerSplit::InnerNode { q, c, s, l, factor } => {
                let Xl = PlaintextCircuit::select(input_powers.len(), &[get_power_idx(l)], base_ring);
                let (q, q_circuit) = q.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let (c, c_circuit) = c.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let (s, s_circuit) = s.to_circuit_recursive(poly_ring, input_powers, rec_depth + 1);
                let f_circuit = PlaintextCircuit::linear_transform_ring(&[factor], base_ring).compose(
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
                let mut Xl = poly_ring.one();
                poly_ring.mul_assign_monomial(&mut Xl, l);
                let f = poly_ring.add(poly_ring.mul(poly_ring.add(c, Xl), q), s);
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
pub fn paterson_stockmeyer_circuit<R>(poly_ring: R, polynomials: &[El<R>]) -> Result<PlaintextCircuit<BaseRing<R>>, ()>
    where R: RingStore,
        R::Type: PolyRing,
        BaseRing<R>: DivisibilityRing + FiniteRing
{
    let degrees = polynomials.iter().map(|f| poly_ring.degree(f).expect("all polynomials must be nonzero")).collect::<Vec<_>>();
    let plan = plan_paterson_stockmeyer_circuit(&degrees);
    assert!(plan.k >= 1);

    let mut rng = oorandom::Rand64::new(0);
    for _ in 0..10 {
        let random_value = poly_ring.base_ring().random_element(|| rng.rand_u64());
        let mut splits = Vec::new();
        for poly in polynomials {
            let randomized_poly = poly_ring.evaluate(poly, &poly_ring.from_terms([(poly_ring.base_ring().one(), 1), (poly_ring.base_ring().clone_el(&random_value), 0)]), poly_ring.inclusion());
            if let Ok(split) = PatersonStockmeyerSplit::create_recursive(&poly_ring, randomized_poly, &plan, 0) {
                splits.push(split);
            } else {
                break;
            }
        }
        if splits.len() == polynomials.len() {
            let mut precomputed_powers = BTreeSet::new();
            precomputed_powers.extend(plan.extra_precomputed_powers.iter().copied());
            drop(plan);
            for split in &splits {
                split.requried_monomials(&poly_ring, &mut precomputed_powers);
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
            return Ok(main_circuit.compose(precompute_powers_circuit, poly_ring.base_ring()).compose(de_randomize_circuit, poly_ring.base_ring()));
        }
    }
    return Err(());
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
    let circuit = paterson_stockmeyer_circuit(&FpX, from_ref(&f)).unwrap();
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&f, &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
    }

    let [f] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, from_ref(&f)).unwrap();
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&f, &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
    }

    let f = FpX.from_terms((0..=17).map(|i| (Fp.int_hom().map(1 << i), i)));
    let circuit = paterson_stockmeyer_circuit(&FpX, from_ref(&f)).unwrap();
    for i in 0..20 {
        assert_el_eq!(Fp, FpX.evaluate(&f, &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
    }
}

#[test]
fn test_evaluation_circuit_multiple() {
    let FpX = DensePolyRing::new(Zn::new(65537), "X");
    let Fp = FpX.base_ring();
    let polys = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(2) - 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, &polys).unwrap();
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&polys[0], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
        assert_el_eq!(Fp, FpX.evaluate(&polys[1], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[1]);
    }

    let polys = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(5) + X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(3) + 2 * X.pow_ref(2) - 4 * X + 1, X.pow_ref(2) - 1]);
    let circuit = paterson_stockmeyer_circuit(&FpX, &polys).unwrap();
    for i in 0..10 {
        assert_el_eq!(Fp, FpX.evaluate(&polys[0], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[0]);
        assert_el_eq!(Fp, FpX.evaluate(&polys[1], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[1]);
        assert_el_eq!(Fp, FpX.evaluate(&polys[2], &Fp.int_hom().map(i), Fp.identity()), circuit.evaluate_no_galois(&[Fp.int_hom().map(i)], Fp.identity())[2]);
    }
}

#[test]
#[ignore]
fn circuit_for_65537() {
    use std::fs::File;
    use std::io::BufWriter;
    use std::io::Write;
    use feanor_math::rings::zn::zn_64::Zn;
    use crate::cache::*;
    use crate::number_ring::galois::*;
    use crate::poly_eval::digit_extract::{centered_digit_extract_poly, cmod};

    let Zp2X = DensePolyRing::new(Zn::new(65537 * 65537), "X");
    let Zp2 = Zp2X.base_ring();
    let poly = create_cached::<_, _, _, true>(
        &Zp2X,
        || RingElSerializeDeserializeWithRing::from(centered_digit_extract_poly(&Zp2X, 2)), 
        &filename_keys!(digit_retain_poly, p: 65537, e: 2), 
        Some("."), 
        cache::StoreAs::AlwaysJson
    ).into();
    let circuit: PlaintextCircuit<feanor_math::rings::zn::zn_64::ZnBase> = create_cached::<_, _, _, true>(
        (Zp2X.base_ring(), &CyclotomicGaloisGroupBase::new(2).into().full_subgroup()),
        || heuristic_functional_decomposition(&Zp2X, vec![Zp2X.clone_el(&poly)], &mut |Zp2X, polys, _| paterson_stockmeyer_circuit(&Zp2X, &polys).unwrap(), Zp2.identity()),
        &filename_keys!(digit_extract, p: 65537, e: 2),
        Some("."),
        StoreAs::AlwaysJson
    );
    println!("p-s mults  {}", circuit.multiplication_gate_count());
    write!(BufWriter::new(File::create("./digit_extract_p65537_e2.fheir").unwrap()), "{}", circuit.to_ir(Zp2, None)).unwrap();

    for x in 0..(65537 * 65537) {
        assert_el_eq!(Zp2X.base_ring(), Zp2X.base_ring().coerce(&ZZi64, cmod(x, 65537)), circuit.evaluate_no_galois(&[Zp2X.base_ring().coerce(&ZZi64, x)], Zp2X.base_ring().identity()).pop().unwrap());
        if x % 100 == 0 {
            println!("{}", x);
        }
    }

    let circuit = heuristic_functional_decomposition(&Zp2X, vec![Zp2X.clone_el(&poly)], &mut |Zp2X, polys, _| poly_to_circuit(&Zp2X, &polys), Zp2.identity());
    println!("bsgs mults {}", circuit.multiplication_gate_count());
}