use core::f64;
use std::cmp::min;
use std::ops::Range;

#[cfg(test)]
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::*;
use feanor_math::group::*;
use feanor_math::ring::*;
use feanor_math::seq::*;

use crate::circuit::evaluator::CircuitEvaluator;
use crate::circuit::*;
use crate::number_ring::galois::*;
use crate::gadget_product::digits::*;
use crate::number_ring::galois::CyclotomicGaloisGroupOps;
#[cfg(test)]
use crate::ZZi64;

use super::eval::*;
use super::noise_estimator::*;
use super::noise_estimator::AlwaysZeroNoiseEstimator;
use super::*;

///
/// Given vectors `a` and `b` such that `b <= a`, finds vectors `c <= b` and `d` such
/// that `sum_i c_i = k` and `a, sum_i d_i >= b - c + d` which minimize the number of
/// nonzero entries of `b - c + d`.
///
/// Note that this function implements a very good heuristic, which will be optimal in
/// most cases. In general, it will not give the optimal solution, however.
///
/// Clearly this requires that `sum_i b_i >= k`.
///
pub fn level_digits(a: &[usize], b: &[usize], k: usize) -> Option<(Vec<usize>, Vec<usize>)> {
    let len = a.len();
    assert!(len > 0);
    assert_eq!(len, b.len());
    assert!(a.iter().zip(b.iter()).all(|(a, b)| b <= a));
    assert!(b.iter().sum::<usize>() >= k);

    (0..=*a.iter().max().unwrap()).filter_map(|max_result| {
        // first find `c` such that `b - c` is `<= max_result` and has the least nonzero entries
        let mut c = (0..len).map(|_| 0).collect::<Vec<_>>();
        let mut current_sum_c = 0;
        for i in 0..len {
            let to_remove = b[i].saturating_sub(max_result);
            if to_remove + current_sum_c > k {
                return None;
            }
            c[i] += to_remove;
            current_sum_c += to_remove;
        }
        // now use the remaining `k - current_sum_c` to zero as many entries of `b - c` as possible
        while current_sum_c < k {
            let entry_to_decrease = (0..len).filter(|i| b[*i] - c[*i] != 0).min_by_key(|i| b[*i] - c[*i]).unwrap();
            let decrease_by = min(b[entry_to_decrease] - c[entry_to_decrease], k - current_sum_c);
            c[entry_to_decrease] += decrease_by;
            current_sum_c += decrease_by;
        }
        return Some((max_result, c));
    }).filter_map(|(max_result, c)| {
        // now find `d` of sum at least `max_result` that introduces as few nonzero entries as possible
        let mut d = (0..len).map(|_| 0).collect::<Vec<_>>();
        let mut current_sum_d = 0;
        for i in 0..len {
            if b[i] - c[i] == 0 {
                // don't introduce new nonzero factors until necessary
                continue;
            }
            let max_d = min(a[i] + c[i] - b[i], max_result + c[i] - b[i]);
            d[i] = max_d;
            current_sum_d += max_d;
            if current_sum_d >= max_result {
                return Some((c, d));
            }
        }
        // now add new nonzero entries until we reach `current_sum_d >= max_result`
        while current_sum_d < max_result {
            let i = (0..len).max_by_key(|i| min(a[*i] + c[*i] - b[*i] - d[*i], max_result + c[*i] - b[*i] - d[*i])).unwrap();
            let add_d = min(a[i] + c[i] - b[i] - d[i], max_result + c[i] - b[i] - d[i]);
            if add_d == 0 {
                return None;
            }
            d[i] += add_d;
            current_sum_d += add_d;
        }
        return Some((c, d));
    }).min_by_key(|(c, d)| (0..len).filter(|i| b[*i] + d[*i] - c[*i] != 0).count())
}

///
/// A (possibly un-relinearized) [`Ciphertext`] which additionally stores w.r.t. which ciphertext
/// modulus it is defined, and which noise level (as measured by some [`BGVModswitchStrategy`]) it
/// is estimated to have.
///
pub struct ModulusAwareCiphertext<Params: BGVInstantiation, Strategy: ?Sized + BGVModswitchStrategy<Params>> {
    /// The stored raw ciphertext, which may or may not have been relinearized
    pub data: CiphertextOrNoRelin<Params>,
    /// The indices of those RNS components w.r.t. a "master RNS base" (specified by the context)
    /// that are not used for this ciphertext; in other words, the ciphertext modulus of this ciphertext
    /// is the product of all RNS factors of the master RNS base that are not mentioned in this list
    pub dropped_rns_factor_indices: Box<RNSFactorIndexList>,
    /// Additional information required by the modulus-switching strategy. For
    /// [`DefaultModswitchStrategy`] this is the [`super::noise_estimator::CiphertextDescriptor`]
    /// corresponding to the noise estimator, which also tracks the implicit scale and the
    /// secret-key distribution of the ciphertext.
    pub info: Strategy::CiphertextInfo
}

///
/// Trait for different modulus-switching strategies in BGV, currently WIP.
///
/// Basically, a [`BGVModswitchStrategy`] should be able to determine when (and
/// how) to modulus-switch during the evaluation of an arithmetic circuit.
/// The most powerful way to do this is by delegating the evaluation of the
/// circuit completely to the [`BGVModswitchStrategy`], which is our current
/// approach.
///
pub trait BGVModswitchStrategy<Params: BGVInstantiation> {

    ///
    /// Additional information that is associated to a ciphertext and is used
    /// to determine when and how to modulus-switch. This will most likely be
    /// some form of estimate of the noise in the ciphertext.
    ///
    type CiphertextInfo;

    ///
    /// Evaluates the given circuit homomorphically on the given encrypted inputs.
    /// This includes performing modulus-switches at suitable times.
    ///
    /// The parameters are as follows:
    ///  - `circuit` is the circuit to evaluate, with constants in a ring that supports
    ///    plaintext-ciphertext operations, as specified by [`AsBGVPlaintext`]
    ///  - `ring` is the ring that contains the constants of `circuit`
    ///  - `P` is the plaintext ring w.r.t. which the inputs are encrypted; `evaluate_circuit()`
    ///    does not support mixing different plaintext moduli
    ///  - `C_master` is the ciphertext ring with the largest relevant RNS base, i.e. its RNS
    ///    base should contain all RNS factors that are referenced by any ciphertext, and may
    ///    have additional unused RNS factors
    ///  - `inputs` contains all inputs to the circuit, i.e. must be of the same length as the
    ///    circuit has input wires. Each entry should be of the form `(drop_rns_factors, info, ctxt)`
    ///    where `ctxt` is the ciphertext w.r.t. the RNS base that contains all RNS factors of `C_master`
    ///    except those mentioned in `drop_rns_fctors`, and `info` should store the additional information
    ///    associated to the ciphertext that is required to determine modulus-switching times.
    ///  - `rk` should be the relinearization key w.r.t. `C_master`, can be `None` if the circuit
    ///    contains no multiplication gates.
    ///  - `gks` should contain all Galois keys used by the circuit (may also contain unused ones);
    ///    if the circuit has no Galois gates, this may be an empty slice
    ///
    fn evaluate_circuit<R>(
        &self,
        circuit: &PlaintextCircuit<R::Type>,
        ring: R,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        inputs: &[ModulusAwareCiphertext<Params, Self>],
        rk: Option<&RelinKey<Params>>,
        gks: &[(GaloisGroupEl, KeySwitchKey<Params>)],
        debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<ModulusAwareCiphertext<Params, Self>>
        where R: RingStore,
            R::Type: AsBGVPlaintext<Params>;

    ///
    /// Returns the info that describes a freshly encrypted ciphertext, w.r.t. a secret
    /// key of hamming weight `sk_hwt`, or a uniformly ternary secret key if `sk_hwt = None`.
    ///
    /// In other words, this describes the output of [`BGVInstantiation::enc_sym()`].
    ///
    fn fresh_encryption(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> Self::CiphertextInfo;

    fn clone_info(&self, info: &Self::CiphertextInfo) -> Self::CiphertextInfo;

    fn print_info(&self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ct: &ModulusAwareCiphertext<Params, Self>);

    fn clone_ct(&self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ct: &ModulusAwareCiphertext<Params, Self>) -> ModulusAwareCiphertext<Params, Self> {
        let C = Params::mod_switch_down_C(C_master, &ct.dropped_rns_factor_indices);
        ModulusAwareCiphertext {
            data: ct.data.clone_ct(P, &C),
            info: self.clone_info(&ct.info),
            dropped_rns_factor_indices: ct.dropped_rns_factor_indices.clone()
        }
    }
}

///
/// Chooses `drop_prime_count` indices from `0..rns_base_len`. These indices are chosen in a way
/// that minimizes the size of the given digits after we drop the corresponding RNS factors.
///
/// Note that this function assumes that all RNS factors have approximately the same size. If this
/// is not the case, their individual size should be considered when choosing which factors to drop.
///
/// # The standard use case
///
/// This hopefully becomes clearer once we consider the main use case:
/// When we do modulus-switching (e.g. during BGV), we remove RNS factors from the ciphertext modulus.
/// For the ciphertexts itself, it is (almost) irrelevant which of these RNS factors are removed, but it makes
/// a huge difference when mod-switching key-switching keys (e.g. relinearization keys). This is because
/// the used gadget vector relies is based on a decomposition of RNS factors into groups, and removing a single
/// RNS factor from every group will give a very different behavior from removing a single, whole group and
/// leaving the other groups unchanged.
///
/// This function will choose the RNS factors to drop with the goal of minimizing noise growth. In particular,
/// as long as the RNS factor groups (the digits) are larger than the special modulus, this function will remove
/// RNS factors from each group in a balanced manner.
///
/// This is probably the desired behavior in most cases, but other behaviors might as well be reasonable in
/// certain scenarios.
///
/// # Example
/// ```rust
/// # use feanor_math::seq::*;
/// # use fheanor::gadget_product::*;
/// # use fheanor::bgv::modswitch::drop_rns_factors_balanced;
/// # use fheanor::gadget_product::digits::*;
/// let digits = RNSGadgetVectorDigitIndices::from([0..3, 3..5].clone_els());
/// // remove the first two indices from 0..3, and the first index from 3..5 - the resulting ranges both have length 1
/// assert_eq!(&[0usize, 1, 3][..] as &[usize], &*drop_rns_factors_balanced(&digits, 3) as &[usize]);
/// ```
///
pub fn drop_rns_factors_balanced(key_digits: &RNSGadgetVectorDigitIndices, drop_prime_count: usize) -> Box<RNSFactorIndexList> {
    assert!(drop_prime_count < key_digits.rns_base_len());

    let mut drop_from_digit = (0..key_digits.len()).map(|_| 0).collect::<Vec<_>>();

    let effective_len = |range: Range<usize>| range.end - range.start;
    for _ in 0..drop_prime_count {
        let largest_digit_idx = (0..key_digits.len()).max_by_key(|i| effective_len(key_digits.at(*i)) - drop_from_digit[*i]).unwrap();
        drop_from_digit[largest_digit_idx] += 1;
    }

    let result = RNSFactorIndexList::from((0..key_digits.len()).flat_map(|i| key_digits.at(i).start..(key_digits.at(i).start + drop_from_digit[i])), key_digits.rns_base_len());
    return result;
}

///
/// Default modulus-switch strategy for BGV, which performs a certain number of modulus-switches
/// before each multiplication.
///
/// The general strategy is as follows:
///  - only mod-switch before multiplications
///  - never introduce new RNS factors, only remove current ones
///  - use the provided [`BGVNoiseEstimator`] to determine when and by how much
///    we should reduce the ciphertext modulus
///  - use lazy relinearization: a multiplication or squaring whose result is used by exactly one
///    subsequent gate or output is left un-relinearized (i.e. returns a [`CiphertextNoRelin`]),
///    and is only relinearized when consumed. This is beneficial when un-relinearized products
///    are summed up, since the (expensive) relinearization can then be performed once on the sum.
///
/// These points lead to a relatively simple and generally well-performing modulus switching strategy.
/// However, there may be situations where deviating from 1. could lead to a lower number of mod-switches
/// (and thus better performance), and deviating from 2. could be used for a finer-tuned mod-switching,
/// and thus less noise growth.
///
pub struct DefaultModswitchStrategy<Params: BGVInstantiation, N: BGVNoiseEstimator<Params>, const LOG: bool> {
    params: PhantomData<Params>,
    noise_estimator: N
}

impl<Params: BGVInstantiation> DefaultModswitchStrategy<Params, AlwaysZeroNoiseEstimator, false> {

    ///
    /// Create a [`DefaultModswitchStrategy`] that never performs modulus switching,
    /// except when necessary because operands are defined modulo different RNS bases.
    ///
    /// Using this is not recommended, except for linear circuits, or circuits with
    /// very low multiplicative depth.
    ///
    pub fn never_modswitch() -> Self {
        Self {
            params: PhantomData,
            noise_estimator: AlwaysZeroNoiseEstimator
        }
    }
}

///
/// Computes the sum of two (possibly un-relinearized) ciphertexts; the result is
/// un-relinearized as soon as one of the summands is.
///
fn add_ct<Params: BGVInstantiation>(P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, lhs: CiphertextOrNoRelin<Params>, rhs: CiphertextOrNoRelin<Params>, policy: ImplicitScalePolicy) -> CiphertextOrNoRelin<Params> {
    match (lhs, rhs) {
        (CiphertextOrNoRelin::Relin(l), CiphertextOrNoRelin::Relin(r)) => CiphertextOrNoRelin::Relin(Params::hom_add(P, C, l, r, policy)),
        (l, r) => CiphertextOrNoRelin::NoRelin(Params::hom_add_norelin(P, C, l.into_norelin(C), r.into_norelin(C), policy))
    }
}

///
/// Modulus-switches a (possibly un-relinearized) ciphertext from `Cold` to `Cnew`.
///
fn mod_switch_data<Params: BGVInstantiation>(P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, data: CiphertextOrNoRelin<Params>) -> CiphertextOrNoRelin<Params> {
    match data {
        CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Params::mod_switch_ct(P, Cnew, Cold, ct)),
        CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(Params::mod_switch_norelin(P, Cnew, Cold, ct))
    }
}

///
/// Returns a string describing the actual (i.e. measured, not estimated) noise budget of a
/// ciphertext; used only for debug logging. Un-relinearized ciphertexts cannot be decrypted
/// directly, so for those no actual noise budget is available.
///
fn actual_noise_budget_str<Params: BGVInstantiation>(P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, data: &CiphertextOrNoRelin<Params>, sk: &SecretKey<Params>) -> String {
    match data {
        CiphertextOrNoRelin::Relin(ct) => format!("{}", Params::noise_budget(P, C, ct, sk)),
        CiphertextOrNoRelin::NoRelin(_) => "n/a (un-relinearized)".to_owned()
    }
}

///
/// Finds `drop_additional_count` RNS factors outside of `dropped_factors_input` and
/// a set `special_modulus` of RNS factors, which optimize performance and noise growth
/// for a key-switch.
///
/// More concretely, removing the the `drop_additional` RNS factors (together with
/// `dropped_factors_input`) and adding the `special_modulus` RNS factors results in the
/// smallest number of digits in `key_switch_key_digits`, under the constraint that
/// `len(special_modulus)` is larger or equal to the size of the largest digit.
///
/// The function returns `(drop_additional, special_modulus)`.
///
/// # The use case
///
/// Consider the following situation: We have a ciphertext `ct`, which is
/// defined modulo a set of RNS factors `X \ B_ct`. We also have a key-switch-key
/// with digits `D_0, ..., D_r`. Now we want to find a superset `B_final' >= B_ct`
/// of size `|B_ct| + k`, and a set `B_special <= B_final` such that we get minimial
/// noise and minimal error, if we mod-switch the ciphertext to `X \ B_final`, the
/// key to `(X \ B_final) u B_special` and then do a key-switch on these values.
///
#[instrument(skip_all)]
pub fn compute_optimal_special_modulus<C: NumberRingRNSQuotient>(
    C_master: &C,
    dropped_factors_input: &RNSFactorIndexList,
    drop_additional_count: usize,
    key_switch_key_digits: &RNSGadgetVectorDigitIndices
) -> (Box<RNSFactorIndexList>, Box<RNSFactorIndexList>) {
    let a = key_switch_key_digits.iter().map(|digit| digit.end - digit.start).collect::<Vec<_>>();
    let b = key_switch_key_digits.iter().map(|digit| digit.end - digit.start - dropped_factors_input.num_within(&digit)).collect::<Vec<_>>();
    if let Some((c, d)) = level_digits(&a, &b, drop_additional_count) {
        let B_additional = key_switch_key_digits.iter().enumerate().flat_map(|(digit_idx, digit)| digit.filter(|i| !dropped_factors_input.contains(*i)).take(c[digit_idx]));
        let B_final = RNSFactorIndexList::from(dropped_factors_input.iter().copied().chain(B_additional).collect::<Vec<_>>(), C_master.base_ring().len());
        let B_special = RNSFactorIndexList::from(key_switch_key_digits.iter().enumerate().flat_map(|(digit_idx, digit)| digit.filter(|i| B_final.contains(*i)).take(d[digit_idx])).collect::<Vec<_>>(), C_master.base_ring().len());
        assert_eq!(B_final.len(), dropped_factors_input.len() + drop_additional_count);
        return (B_final, B_special);
    } else {
        let additional_drop = drop_rns_factors_balanced(&key_switch_key_digits.remove_indices(dropped_factors_input), drop_additional_count);
        let B_final = additional_drop.pullback(dropped_factors_input);
        let B_special = B_final.clone();
        assert_eq!(B_final.len(), dropped_factors_input.len() + drop_additional_count);
        return (B_final, B_special);
    }
}

impl<Params: BGVInstantiation, N: BGVNoiseEstimator<Params>, const LOG: bool> DefaultModswitchStrategy<Params, N, LOG>
    where N::CiphertextDescriptor: Clone,
        <Params::PlaintextZnRing as RingBase>::Element: Clone
{

    pub fn new(noise_estimator: N) -> Self {
        Self {
            params: PhantomData,
            noise_estimator: noise_estimator
        }
    }

    ///
    /// Mod-switches the given ciphertext from its current ciphertext ring
    /// to `C_target`, and adjusts the noise information.
    ///
    fn mod_switch_down(
        &self,
        P: &PlaintextRing<Params>,
        C_target: &CiphertextRing<Params>,
        C_master: &CiphertextRing<Params>,
        dropped_factors_target: &RNSFactorIndexList,
        x: ModulusAwareCiphertext<Params, Self>,
        context: &str,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Self> {
        let Cx = Params::mod_switch_down_C(C_master, &x.dropped_rns_factor_indices);
        let drop_x = dropped_factors_target.pushforward(&x.dropped_rns_factor_indices);
        if drop_x.len() == 0 {
            return x;
        }
        let before_estimate = self.noise_estimator.estimate_log2_relative_noise_level(P, &Cx, &x.info);
        let before_actual = debug_sk.map(|sk| {
            let sk_x = Params::mod_switch_sk(&Cx, C_master, sk);
            actual_noise_budget_str::<Params>(P, &Cx, &x.data, &sk_x)
        });
        let ModulusAwareCiphertext { data, info, dropped_rns_factor_indices: _ } = x;
        let result = ModulusAwareCiphertext {
            data: mod_switch_data::<Params>(P, C_target, &Cx, data),
            info: self.noise_estimator.mod_switch_ct(P, C_target, &Cx, &info),
            dropped_rns_factor_indices: dropped_factors_target.to_owned()
        };
        if LOG {
            println!("{}: Dropping RNS factors {} of operand, estimated noise budget {}/{} -> {}/{}",
                context,
                drop_x,
                -before_estimate.round(),
                ZZbig.abs_log2_ceil(Cx.base_ring().modulus()).unwrap(),
                -self.noise_estimator.estimate_log2_relative_noise_level(P, C_target, &result.info).round(),
                ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap(),
            );
            if let Some(sk) = debug_sk {
                let sk_target = Params::mod_switch_sk(C_target, C_master, sk);
                println!("  actual noise budget: {} -> {}", before_actual.unwrap(), actual_noise_budget_str::<Params>(P, C_target, &result.data, &sk_target));
            }
        }
        return result;
    }

    ///
    /// Mod-switches a clone of the given ciphertext from its current ciphertext ring
    /// to `C_target`, and adjusts the noise information.
    ///
    fn mod_switch_down_cloned(
        &self,
        P: &PlaintextRing<Params>,
        C_target: &CiphertextRing<Params>,
        C_master: &CiphertextRing<Params>,
        dropped_factors_target: &RNSFactorIndexList,
        x: &ModulusAwareCiphertext<Params, Self>,
        context: &str,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Self> {
        let Cx = Params::mod_switch_down_C(C_master, &x.dropped_rns_factor_indices);
        let cloned = ModulusAwareCiphertext {
            data: x.data.clone_ct(P, &Cx),
            info: self.noise_estimator.clone_ct(P, &Cx, &x.info),
            dropped_rns_factor_indices: x.dropped_rns_factor_indices.clone()
        };
        self.mod_switch_down(P, C_target, C_master, dropped_factors_target, cloned, context, debug_sk)
    }

    ///
    /// Relinearizes the given ciphertext if it is un-relinearized, and otherwise returns it
    /// unchanged. The ciphertext is relinearized w.r.t. its current ciphertext modulus, choosing
    /// a special modulus among its already-dropped RNS factors (no additional modulus-switching).
    ///
    fn relinearize_if_needed(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: ModulusAwareCiphertext<Params, Self>,
        rk: &RelinKey<Params>,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Self> {
        if !x.data.is_norelin() {
            return x;
        }
        let ModulusAwareCiphertext { data, info, dropped_rns_factor_indices } = x;
        let ct = match data {
            CiphertextOrNoRelin::NoRelin(ct) => ct,
            CiphertextOrNoRelin::Relin(_) => unreachable!()
        };
        let used_sk = info.sk;
        let (total_drop, special_modulus) = compute_optimal_special_modulus(C_master.get_ring(), &dropped_rns_factor_indices, 0, rk.gadget_vector_digits());
        let total_drop_without_special = total_drop.subtract(&special_modulus);
        let C_special = Params::mod_switch_down_C(C_master, &total_drop_without_special);
        let C_target = Params::mod_switch_down_C(C_master, &total_drop);
        let rk_modswitch = Params::mod_switch_down_rk(&C_special, C_master, rk);
        let result = ModulusAwareCiphertext {
            data: CiphertextOrNoRelin::Relin(Params::relinearize(P, &C_target, &C_special, ct, &rk_modswitch)),
            info: self.noise_estimator.relinearize(P, &C_target, &C_special, &info, KeySwitchKeyDescriptor {
                digits: rk_modswitch.gadget_vector_digits(),
                new_sk: used_sk,
                sigma: 3.2
            }),
            dropped_rns_factor_indices: total_drop
        };
        if LOG {
            println!("Relinearize: Result has estimated noise budget {}/{}",
                -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &result.info).round(),
                ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
            );
            if let Some(sk) = debug_sk {
                let sk_target = Params::mod_switch_sk(&C_target, C_master, sk);
                println!("  actual noise budget: {}", actual_noise_budget_str::<Params>(P, &C_target, &result.data, &sk_target));
            }
        }
        return result;
    }

    ///
    /// Computes the RNS base we should switch to before multiplication to
    /// minimize the result noise. The result is returned as the list of RNS
    /// factors of `C_master` that we want to drop. This list corresponds to
    /// the RNS factors to drop from the ciphertexts..
    ///
    #[instrument(skip_all)]
    fn compute_optimal_mul_modswitch(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        noise_x: &CiphertextDescriptor<Params, N>,
        dropped_factors_x: &RNSFactorIndexList,
        noise_y: &CiphertextDescriptor<Params, N>,
        dropped_factors_y: &RNSFactorIndexList,
        rk_digits: &RNSGadgetVectorDigitIndices,
        used_sk: SecretKeyDistribution
    ) -> (/* total_drop = */ Box<RNSFactorIndexList>, /* special_modulus = */ Box<RNSFactorIndexList>) {
        let Cx = Params::mod_switch_down_C(C_master, dropped_factors_x);
        let Cy = Params::mod_switch_down_C(C_master, dropped_factors_y);

        // first, we drop all the RNS factors that are required to make the product well-defined;
        // these are exactly the RNS factors that are missing in either input
        let base_drop = dropped_factors_x.union(&dropped_factors_y);

        // now try every number of additional RNS factors to drop
        let compute_result_noise = |num_to_drop: usize| {
            let (total_drop, special_modulus) = compute_optimal_special_modulus(C_master.get_ring(), &base_drop, num_to_drop, rk_digits);
            let total_drop_without_special = total_drop.subtract(&special_modulus);
            let C_target = Params::mod_switch_down_C(C_master, &total_drop);
            let C_special = Params::mod_switch_down_C(C_master, &total_drop_without_special);
            let rk_digits_after_total_drop = rk_digits.remove_indices(&total_drop_without_special);

            let expected_noise = self.noise_estimator.estimate_log2_relative_noise_level(
                P,
                &C_target,
                &self.noise_estimator.hom_mul(
                    P,
                    &C_target,
                    &C_special,
                    &self.noise_estimator.mod_switch_ct(P, &C_target, &Cx, noise_x),
                    &self.noise_estimator.mod_switch_ct(P, &C_target, &Cy, noise_y),
                    KeySwitchKeyDescriptor {
                        digits: &rk_digits_after_total_drop,
                        new_sk: used_sk,
                        sigma: 3.2
                    }
                )
            );
            return ((total_drop, special_modulus), expected_noise);
        };
        return (0..(C_master.base_ring().len() - base_drop.len())).map(compute_result_noise).min_by(|(_, l), (_, r)| f64::total_cmp(l, r)).unwrap().0;
    }

    ///
    /// Computes the value `x + sum_i cs[i] * y[i]`, by mod-switching all involved
    /// ciphertexts to the RNS base of all shared RNS factors. In particular, if the
    /// input ciphertexts are all defined w.r.t. the same RNS base, no modulus-switching
    /// is performed at all.
    ///
    /// As described for [`DefaultModswitchStrategy`], un-relinearized summands are kept
    /// un-relinearized: if any of the summands is un-relinearized, the result is
    /// un-relinearized as well (so that the eventual relinearization happens only once,
    /// on the sum).
    ///
    #[instrument(skip_all)]
    fn inner_prod<R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        coeffs: &[&Coefficient<R::Type>],
        ys: &[&ModulusAwareCiphertext<Params, Self>],
        ring: R,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Self>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        assert_eq!(coeffs.len(), ys.len());

        // We separate the inner product into two parts:
        //  - the integer part, which is of the form `sum_i c[i] * ct[i]` with `c[i]` being integers
        //    (this includes the `0, 1, -1` coefficients), handled via `BigIntRingBase`
        //  - the main part, which is of the form `sum_i c[i] * ct[i]` with `c[i]` being elements of `R`
        let mut int_part: Vec<(El<BigIntRing>, usize)> = Vec::new();
        let mut main_part: Vec<(&El<R>, usize)> = Vec::new();
        // while separating the different summands, we also keep track of the result modulus
        let mut total_drop = RNSFactorIndexList::empty();
        for (i, (lhs, rhs)) in coeffs.iter().copied().zip(ys.iter().copied()).enumerate() {
            if lhs.is_zero() {
                continue;
            }
            total_drop = total_drop.union(&rhs.dropped_rns_factor_indices);
            match lhs {
                Coefficient::Zero => unreachable!(),
                Coefficient::One => int_part.push((ZZbig.one(), i)),
                Coefficient::NegOne => int_part.push((ZZbig.neg_one(), i)),
                Coefficient::Integer(c) => int_part.push((ZZbig.clone_el(c), i)),
                Coefficient::Other(c) => main_part.push((c, i)),
            }
        }
        if int_part.is_empty() && main_part.is_empty() {
            // everything is just zero
            return ModulusAwareCiphertext {
                data: CiphertextOrNoRelin::Relin(Params::transparent_zero(P, C_master)),
                info: self.noise_estimator.transparent_zero(P, C_master),
                dropped_rns_factor_indices: RNSFactorIndexList::empty()
            };
        }

        let C_target = Params::mod_switch_down_C(C_master, &total_drop);

        // mod-switch (clones of) all referenced ciphertexts down to the common base
        let int_switched: Vec<(El<BigIntRing>, ModulusAwareCiphertext<Params, Self>)> = int_part.into_iter()
            .map(|(c, i)| (c, self.mod_switch_down_cloned(P, &C_target, C_master, &total_drop, ys[i], "HomInnerProduct", debug_sk)))
            .collect();
        let main_switched: Vec<(El<R>, ModulusAwareCiphertext<Params, Self>)> = main_part.into_iter()
            .map(|(c, i)| (ring.clone_el(c), self.mod_switch_down_cloned(P, &C_target, C_master, &total_drop, ys[i], "HomInnerProduct", debug_sk)))
            .collect();

        // compute the noise estimate (borrowing the descriptors) before consuming the data
        let int_noise = ZZbig.get_ring().hom_inner_product_noise(&self.noise_estimator, P, &C_target, int_switched.iter().map(|(c, ct)| (c, &ct.info)));
        let main_noise = ring.get_ring().hom_inner_product_noise(&self.noise_estimator, P, &C_target, main_switched.iter().map(|(c, ct)| (c, &ct.info)));
        // both parts have implicit scale 1 (merging the implicit scale into the plaintext is free),
        // so the addition does not increase noise; use `Merge` to be robust regardless
        let result_info = self.noise_estimator.hom_add(P, &C_target, &int_noise, &main_noise, ImplicitScalePolicy::Merge);

        let int_data = ZZbig.get_ring().hom_inner_product(P, &C_target, int_switched.into_iter().map(|(c, ct)| (c, ct.data)));
        let main_data = ring.get_ring().hom_inner_product(P, &C_target, main_switched.into_iter().map(|(c, ct)| (c, ct.data)));
        let result_data = add_ct::<Params>(P, &C_target, int_data, main_data, ImplicitScalePolicy::Merge);

        return ModulusAwareCiphertext {
            data: result_data,
            info: result_info,
            dropped_rns_factor_indices: total_drop
        };
    }

    #[instrument(skip_all)]
    fn mul<R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: ModulusAwareCiphertext<Params, Self>,
        y: ModulusAwareCiphertext<Params, Self>,
        _ring: R,
        rk: Option<&RelinKey<Params>>,
        fan_out: usize,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Self>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        let rk = rk.unwrap();
        // a ciphertext-ciphertext multiplication operates on relinearized operands; relinearize first
        let x = self.relinearize_if_needed(P, C_master, x, rk, debug_sk);
        let y = self.relinearize_if_needed(P, C_master, y, rk, debug_sk);
        let used_sk = assert_sk_distr_match(x.info.sk, y.info.sk);
        assert!(x.dropped_rns_factor_indices.len() < C_master.base_ring().len());
        assert!(y.dropped_rns_factor_indices.len() < C_master.base_ring().len());

        let (total_drop, special_modulus) = self.compute_optimal_mul_modswitch(P, C_master, &x.info, &x.dropped_rns_factor_indices, &y.info, &y.dropped_rns_factor_indices, rk.gadget_vector_digits(), used_sk);
        let C_target = Params::mod_switch_down_C(C_master, &total_drop);
        let x_modswitched = self.mod_switch_down(P, &C_target, C_master, &total_drop, x, "HomMul", debug_sk);
        let y_modswitched = self.mod_switch_down(P, &C_target, C_master, &total_drop, y, "HomMul", debug_sk);

        let x_ct = x_modswitched.data.unwrap_relin();
        let y_ct = y_modswitched.data.unwrap_relin();
        let norelin_data = Params::hom_mul_norelin(P, &C_target, &x_ct, &y_ct);
        let norelin_info = self.noise_estimator.hom_mul_norelin(P, &C_target, &x_modswitched.info, &y_modswitched.info);

        if fan_out == 1 {
            // lazy relinearization: the result is consumed by exactly one gate/output, so we leave it
            // un-relinearized; it will be relinearized when it is consumed (possibly after being summed up)
            if LOG {
                println!("HomMul (lazy): Result is un-relinearized, estimated noise budget {}/{}",
                    -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &norelin_info).round(),
                    ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
                );
            }
            return ModulusAwareCiphertext {
                data: CiphertextOrNoRelin::NoRelin(norelin_data),
                info: norelin_info,
                dropped_rns_factor_indices: total_drop
            };
        } else {
            // eager relinearization
            let total_drop_without_special = total_drop.subtract(&special_modulus);
            let C_special = Params::mod_switch_down_C(C_master, &total_drop_without_special);
            let rk_modswitch = Params::mod_switch_down_rk(&C_special, C_master, rk);
            if LOG {
                println!(
                    "Using a special modulus of {} RNS factors and a gadget vector of {} digits (largest has {} RNS factors) for relinearization",
                    special_modulus.len(),
                    rk_modswitch.gadget_vector_digits().len(),
                    rk_modswitch.gadget_vector_digits().iter().map(|digit| digit.end - digit.start).max().unwrap()
                );
            }
            let res_data = Params::relinearize(P, &C_target, &C_special, norelin_data, &rk_modswitch);
            let res_info = self.noise_estimator.relinearize(P, &C_target, &C_special, &norelin_info, KeySwitchKeyDescriptor {
                digits: rk_modswitch.gadget_vector_digits(),
                new_sk: used_sk,
                sigma: 3.2
            });
            if LOG {
                println!("HomMul: Result has estimated noise budget {}/{}",
                    -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &res_info).round(),
                    ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
                );
                if let Some(sk) = debug_sk {
                    let sk_target = Params::mod_switch_sk(&C_target, C_master, sk);
                    println!("  actual noise budget: {}", Params::noise_budget(P, &C_target, &res_data, &sk_target));
                }
            }
            return ModulusAwareCiphertext {
                dropped_rns_factor_indices: total_drop,
                info: res_info,
                data: CiphertextOrNoRelin::Relin(res_data)
            };
        }
    }

    #[instrument(skip_all)]
    fn square<R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: ModulusAwareCiphertext<Params, Self>,
        _ring: R,
        rk: Option<&RelinKey<Params>>,
        fan_out: usize,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Self>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        let rk = rk.unwrap();
        let x = self.relinearize_if_needed(P, C_master, x, rk, debug_sk);
        let used_sk = x.info.sk;
        assert!(x.dropped_rns_factor_indices.len() < C_master.base_ring().len());

        let (total_drop, special_modulus) = self.compute_optimal_mul_modswitch(P, C_master, &x.info, &x.dropped_rns_factor_indices, &x.info, &x.dropped_rns_factor_indices, rk.gadget_vector_digits(), used_sk);
        let C_target = Params::mod_switch_down_C(C_master, &total_drop);
        let x_modswitched = self.mod_switch_down(P, &C_target, C_master, &total_drop, x, "HomSquare", debug_sk);

        let x_ct = x_modswitched.data.unwrap_relin();
        let norelin_data = Params::hom_square_norelin(P, &C_target, &x_ct);
        let norelin_info = self.noise_estimator.hom_square_norelin(P, &C_target, &x_modswitched.info);

        if fan_out == 1 {
            if LOG {
                println!("HomSquare (lazy): Result is un-relinearized, estimated noise budget {}/{}",
                    -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &norelin_info).round(),
                    ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
                );
            }
            return ModulusAwareCiphertext {
                data: CiphertextOrNoRelin::NoRelin(norelin_data),
                info: norelin_info,
                dropped_rns_factor_indices: total_drop
            };
        } else {
            let total_drop_without_special = total_drop.subtract(&special_modulus);
            let C_special = Params::mod_switch_down_C(C_master, &total_drop_without_special);
            let rk_modswitch = Params::mod_switch_down_rk(&C_special, C_master, rk);
            if LOG {
                println!(
                    "Using a special modulus of {} RNS factors and a gadget vector of {} digits (largest has {} RNS factors) for relinearization",
                    special_modulus.len(),
                    rk_modswitch.gadget_vector_digits().len(),
                    rk_modswitch.gadget_vector_digits().iter().map(|digit| digit.end - digit.start).max().unwrap()
                );
            }
            let res_data = Params::relinearize(P, &C_target, &C_special, norelin_data, &rk_modswitch);
            let res_info = self.noise_estimator.relinearize(P, &C_target, &C_special, &norelin_info, KeySwitchKeyDescriptor {
                digits: rk_modswitch.gadget_vector_digits(),
                new_sk: used_sk,
                sigma: 3.2
            });
            if LOG {
                println!("HomSquare: Result has estimated noise budget {}/{}",
                    -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &res_info).round(),
                    ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
                );
                if let Some(sk) = debug_sk {
                    let sk_target = Params::mod_switch_sk(&C_target, C_master, sk);
                    println!("  actual noise budget: {}", Params::noise_budget(P, &C_target, &res_data, &sk_target));
                }
            }
            return ModulusAwareCiphertext {
                dropped_rns_factor_indices: total_drop,
                info: res_info,
                data: CiphertextOrNoRelin::Relin(res_data)
            };
        }
    }

    #[instrument(skip_all)]
    fn gal_many<R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: ModulusAwareCiphertext<Params, Self>,
        _ring: R,
        gs: &[GaloisGroupEl],
        gks: &[(GaloisGroupEl, KeySwitchKey<Params>)],
        rk: Option<&RelinKey<Params>>,
        debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<ModulusAwareCiphertext<Params, Self>>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        // a Galois automorphism operates on a relinearized ciphertext; relinearize first if needed
        let x = self.relinearize_if_needed(P, C_master, x, rk.expect("relinearizing before a Galois automorphism requires a relinearization key"), debug_sk);
        let used_sk = x.info.sk;
        assert!(x.dropped_rns_factor_indices.len() < C_master.base_ring().len());

        let get_gk = |g| if let Some(res) = gks.iter().filter(|(provided_g, _)| C_master.acting_galois_group().eq_el(g, provided_g)).next() {
            res
        } else {
            panic!("Galois key for {} not found", C_master.acting_galois_group().representative(g))
        };
        let gk_digits = get_gk(&gs[0]).1.gadget_vector_digits();
        assert!(gs.iter().all(|g| get_gk(g).1.gadget_vector_digits() == gk_digits), "when using `gal_many()`, all Galois keys must have the same digits");
        let (total_drop, special_modulus) = compute_optimal_special_modulus(C_master.get_ring(), &x.dropped_rns_factor_indices, 0, gk_digits);
        assert!(total_drop.len() < C_master.base_ring().len());
        let C_target = Params::mod_switch_down_C(C_master, &total_drop);
        let total_drop_without_special = total_drop.subtract(&special_modulus);
        let C_special = Params::mod_switch_down_C(&C_master, &total_drop_without_special);
        let gks_mod_switched = gs.iter().map(|g| Params::mod_switch_down_gk(&C_special, C_master, &get_gk(g).1)).collect::<Vec<_>>();

        if LOG {
            println!(
                "Using a special modulus of {} RNS factors and a gadget vector of {} digits (largest has {} RNS factors) for Galois key switching",
                special_modulus.len(),
                gk_digits.remove_indices(&total_drop_without_special).len(),
                gk_digits.remove_indices(&total_drop_without_special).iter().map(|digit| digit.end - digit.start).max().unwrap()
            );
        }
        let ModulusAwareCiphertext { data, info: x_info, dropped_rns_factor_indices: _ } = x;
        let x_ct = data.unwrap_relin();
        let result = if gs.len() == 1 {
            vec![Params::hom_galois(P, &C_target, &C_special, x_ct, &gs[0], gks_mod_switched.at(0))]
        } else {
            Params::hom_galois_many(P, &C_target, &C_special, x_ct, gs, gks_mod_switched.as_fn())
        };
        return result.into_iter().zip(gs.into_iter()).zip(gks_mod_switched.iter()).map(|((res, g), gk)| ModulusAwareCiphertext {
            dropped_rns_factor_indices: total_drop.clone(),
            info: self.noise_estimator.hom_galois(
                &P,
                &C_target,
                &C_special,
                &x_info,
                g,
                KeySwitchKeyDescriptor {
                    digits: gk.gadget_vector_digits(),
                    new_sk: used_sk,
                    sigma: 3.2
                }
            ),
            data: CiphertextOrNoRelin::Relin(res)
        }).collect();
    }
}

struct BGVEvaluator<'a, R, Inst, N, const LOG: bool>
    where R: ?Sized + AsBGVPlaintext<Inst>, Inst: BGVInstantiation, N: BGVNoiseEstimator<Inst>
{
    ring: &'a R,
    P: &'a PlaintextRing<Inst>,
    C_master: &'a CiphertextRing<Inst>,
    rk: Option<&'a RelinKey<Inst>>,
    gks: &'a [(GaloisGroupEl, KeySwitchKey<Inst>)],
    strategy: &'a DefaultModswitchStrategy<Inst, N, LOG>,
    debug_sk: Option<&'a SecretKey<Inst>>
}

impl<'a, 'b, R, Inst, N, const LOG: bool> CircuitEvaluator<'b, ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, R> for BGVEvaluator<'a, R, Inst, N, LOG>
    where R: ?Sized + AsBGVPlaintext<Inst>, Inst: BGVInstantiation, N: BGVNoiseEstimator<Inst>,
        N::CiphertextDescriptor: Clone,
        <Inst::PlaintextZnRing as RingBase>::Element: Clone
{
    fn supports_gal(&self) -> bool {
        self.gks.len() > 0
    }

    fn supports_mul(&self) -> bool {
        self.rk.is_some()
    }

    #[instrument(skip_all)]
    fn add_constant(&mut self, val: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, constant: &'b Coefficient<R>) -> ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>> {
        let current_C = Inst::mod_switch_down_C(self.C_master, &val.dropped_rns_factor_indices);
        let ModulusAwareCiphertext { data, info, dropped_rns_factor_indices } = val;
        if let Some(int) = constant.as_integer() {
            let new_info = ZZbig.get_ring().hom_add_to_noise(&self.strategy.noise_estimator, self.P, &current_C, &int, &info);
            let new_data = ZZbig.get_ring().hom_add_to(self.P, &current_C, &int, data);
            ModulusAwareCiphertext {
                info: new_info,
                data: new_data,
                dropped_rns_factor_indices
            }
        } else {
            let ring = RingRef::new(self.ring);
            let constant = constant.clone(ring).to_ring_el(ring);
            let new_info = self.ring.hom_add_to_noise(&self.strategy.noise_estimator, self.P, &current_C, &constant, &info);
            let new_data = self.ring.hom_add_to(self.P, &current_C, &constant, data);
            ModulusAwareCiphertext {
                info: new_info,
                data: new_data,
                dropped_rns_factor_indices
            }
        }
    }

    fn gal(&mut self, val: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, gs: &'b [GaloisGroupEl]) -> Vec<ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>> {
        self.strategy.gal_many(self.P, self.C_master, val, RingRef::new(self.ring), gs, self.gks, self.rk, self.debug_sk)
    }

    fn inner_prod<'c, I>(&mut self, data: I) -> ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>
        where I: Iterator<Item = (&'b Coefficient<R>, &'c ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>)>,
            R: 'b,
            ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>: 'c
    {
        let mut coeffs = Vec::new();
        let mut ys = Vec::new();
        for (coeff, y) in data {
            coeffs.push(coeff);
            ys.push(y)
        }
        self.strategy.inner_prod(self.P, self.C_master, &coeffs, &ys, RingRef::new(self.ring), self.debug_sk)
    }

    fn mul(&mut self, lhs: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, rhs: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, fan_out: usize) -> ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>> {
        self.strategy.mul(self.P, self.C_master, lhs, rhs, RingRef::new(self.ring), self.rk, fan_out, self.debug_sk)
    }

    fn square(&mut self, val: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, fan_out: usize) -> ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>> {
        self.strategy.square(self.P, self.C_master, val, RingRef::new(self.ring), self.rk, fan_out, self.debug_sk)
    }
}

impl<Params: BGVInstantiation, N: BGVNoiseEstimator<Params>, const LOG: bool> BGVModswitchStrategy<Params> for DefaultModswitchStrategy<Params, N, LOG>
    where N::CiphertextDescriptor: Clone,
        <Params::PlaintextZnRing as RingBase>::Element: Clone
{

    type CiphertextInfo = CiphertextDescriptor<Params, N>;

    #[instrument(skip_all)]
    fn evaluate_circuit<R>(
        &self,
        circuit: &PlaintextCircuit<R::Type>,
        ring: R,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        inputs: &[ModulusAwareCiphertext<Params, Self>],
        rk: Option<&RelinKey<Params>>,
        gks: &[(GaloisGroupEl, KeySwitchKey<Params>)],
        mut debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<ModulusAwareCiphertext<Params, Self>>
        where R: RingStore,
            R::Type: AsBGVPlaintext<Params>
    {
        if !LOG {
            debug_sk = None;
        }
        let result = circuit.evaluate_generic(
            inputs,
            BGVEvaluator::<R::Type, Params, N, LOG> {
                C_master: C_master,
                P: P,
                debug_sk: debug_sk,
                gks: gks,
                ring: ring.get_ring(),
                rk: rk,
                strategy: self
            }
        );
        // outputs may be left un-relinearized by lazy relinearization; relinearize them so that
        // callers receive ordinary (relinearizable/decryptable) ciphertexts
        return result.into_iter().map(|ct| if ct.data.is_norelin() {
            self.relinearize_if_needed(P, C_master, ct, rk.expect("relinearizing an un-relinearized output requires a relinearization key"), debug_sk)
        } else {
            ct
        }).collect();
    }

    fn fresh_encryption(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> <Self as BGVModswitchStrategy<Params>>::CiphertextInfo {
        self.noise_estimator.enc_sym_zero(P, C, sk)
    }

    fn clone_info(&self, info: &Self::CiphertextInfo) -> Self::CiphertextInfo {
        CiphertextDescriptor::new(info.noise.clone(), info.implicit_scale.clone(), info.sk)
    }

    fn print_info(&self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ct: &ModulusAwareCiphertext<Params, Self>) {
        let Clocal = Params::mod_switch_down_C(C_master, &ct.dropped_rns_factor_indices);
        println!("estimated noise: {}", self.noise_estimator.estimate_log2_relative_noise_level(P, &Clocal, &ct.info));
    }
}

#[cfg(test)]
use feanor_math::rings::poly::dense_poly::DensePolyRing;
#[cfg(test)]
use crate::bgv::noise_estimator::NaiveBGVNoiseEstimator;
#[cfg(test)]
use crate::poly_eval::digit_extract::centered_digit_retain_poly;
#[cfg(test)]
use crate::poly_eval::to_circuit::poly_to_circuit;

#[test]
fn test_modswitch_strategy_inner_prod() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();

    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(17 * 17 * 17, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);
    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);

    let modswitch_strategy: DefaultModswitchStrategy<Pow2BGV, _, true> = DefaultModswitchStrategy::new(NaiveBGVNoiseEstimator);
    let inputs = [P.int_hom().map(2), P.int_hom().map(100), P.int_hom().map(-1)];
    let mut cts = inputs.iter().map(|x| ModulusAwareCiphertext {
        data: CiphertextOrNoRelin::Relin(Pow2BGV::enc_sym(&P, &C, &mut rng, &x, &sk, 3.2)),
        dropped_rns_factor_indices: RNSFactorIndexList::empty(),
        info: modswitch_strategy.fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary)
    }).collect::<Vec<_>>();

    let res = modswitch_strategy.inner_prod(&P, &C, &[
        &Coefficient::NegOne,
        &Coefficient::One,
        &Coefficient::Other(P.int_hom().map(17))
    ], &cts.iter().collect::<Vec<_>>(), &P, None);
    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);
    assert_el_eq!(&P, &P.int_hom().map(-2 + 100 - 17), Pow2BGV::dec(&P, &res_C, res.data.unwrap_relin(), &res_sk));

    let to_drop = RNSFactorIndexList::from([0], C.base_ring().len());
    let C_new = Pow2BGV::mod_switch_down_C(&C, &to_drop);
    cts[0] = modswitch_strategy.mod_switch_down(&P, &C_new, &C, &to_drop, modswitch_strategy.clone_ct(&P, &C, &cts[0]), "", None);

    let res = modswitch_strategy.inner_prod(&P, &C, &[
        &Coefficient::NegOne,
        &Coefficient::One,
        &Coefficient::Other(P.int_hom().map(17))
    ], &cts.iter().collect::<Vec<_>>(), &P, None);
    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);
    assert_el_eq!(&P, &P.int_hom().map(-2 + 100 - 17), Pow2BGV::dec(&P, &res_C, res.data.unwrap_relin(), &res_sk));

    let to_drop = RNSFactorIndexList::from([1], C.base_ring().len());
    let C_new = Pow2BGV::mod_switch_down_C(&C, &to_drop);
    cts[2] = modswitch_strategy.mod_switch_down(&P, &C_new, &C, &to_drop, modswitch_strategy.clone_ct(&P, &C, &cts[2]), "", None);

    let res = modswitch_strategy.inner_prod(&P, &C, &[
        &Coefficient::NegOne,
        &Coefficient::One,
        &Coefficient::Other(P.int_hom().map(17))
    ], &cts.iter().collect::<Vec<_>>(), &P, None);
    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);
    assert_el_eq!(&P, &P.int_hom().map(-2 + 100 - 17), Pow2BGV::dec(&P, &res_C, res.data.unwrap_relin(), &res_sk));
}

#[test]
fn test_modswitch_strategy_mul() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();

    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);
    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2);

    let modswitch_strategy: DefaultModswitchStrategy<Pow2BGV, _, true> = DefaultModswitchStrategy::new(NaiveBGVNoiseEstimator);
    let pow8_circuit = PlaintextCircuit::mul(ZZbig)
        .compose(PlaintextCircuit::mul(ZZbig).output_twice(ZZbig), ZZbig)
        .compose(PlaintextCircuit::mul(ZZbig).output_twice(ZZbig), ZZbig)
        .compose(PlaintextCircuit::identity(1, ZZbig).output_twice(ZZbig), ZZbig);

    let input = P.int_hom().map(2);
    let ct = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk, 3.2);
    let res = modswitch_strategy.evaluate_circuit(
        &pow8_circuit,
        ZZbig,
        &P,
        &C,
        &[ModulusAwareCiphertext {
            dropped_rns_factor_indices: RNSFactorIndexList::empty(),
            info: modswitch_strategy.fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
            data: CiphertextOrNoRelin::Relin(ct)
        }],
        Some(&rk),
        &[],
        Some(&sk)
    ).into_iter().next().unwrap();

    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);
    let res_ct = res.data.unwrap_relin();
    let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res_ct, &res_sk);
    println!("Actual output noise budget is {}", res_noise);
    assert_el_eq!(&P, &P.neg_one(), Pow2BGV::dec(&P, &res_C, res_ct, &res_sk));
}

#[test]
fn test_never_modswitch_strategy_mul() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();

    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);

    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2);

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk, 3.2);

    {
        let modswitch_strategy = DefaultModswitchStrategy::never_modswitch();
        let pow4_circuit = PlaintextCircuit::mul(ZZbig)
            .compose(PlaintextCircuit::square(ZZbig).output_twice(ZZbig), ZZbig);

        let res = modswitch_strategy.evaluate_circuit(
            &pow4_circuit,
            ZZbig,
            &P,
            &C,
            &[ModulusAwareCiphertext {
                dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                info: modswitch_strategy.fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
                data: CiphertextOrNoRelin::Relin(Pow2BGV::clone_ct(&P, &C, &ctxt))
            }],
            Some(&rk),
            &[],
            None
        ).into_iter().next().unwrap();

        let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
        let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);

        let res_ct = res.data.unwrap_relin();
        let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res_ct, &res_sk);
        println!("Actual output noise budget is {}", res_noise);
        assert_el_eq!(&P, &P.int_hom().map(16), Pow2BGV::dec(&P, &res_C, res_ct, &res_sk));
    }
    {
        let modswitch_strategy = DefaultModswitchStrategy::never_modswitch();
        let pow8_circuit = PlaintextCircuit::mul(ZZbig)
            .compose(PlaintextCircuit::mul(ZZbig).output_twice(ZZbig), ZZbig)
            .compose(PlaintextCircuit::mul(ZZbig).output_twice(ZZbig), ZZbig)
            .compose(PlaintextCircuit::identity(1, ZZbig).output_twice(ZZbig), ZZbig);

        let res = modswitch_strategy.evaluate_circuit(
            &pow8_circuit,
            ZZbig,
            &P,
            &C,
            &[ModulusAwareCiphertext {
                dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                info: modswitch_strategy.fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
                data: CiphertextOrNoRelin::Relin(Pow2BGV::clone_ct(&P, &C, &ctxt))
            }],
            Some(&rk),
            &[],
            None
        ).into_iter().next().unwrap();

        let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
        let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);

        let res_ct = res.data.unwrap_relin();
        let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res_ct, &res_sk);
        assert_eq!(0, res_noise);
    }
}

#[test]
fn test_modswitch_strategy_evaluate_circuit() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();

    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(17 * 17 * 17, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);

    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2);

    let modswitch_strategy: DefaultModswitchStrategy<Pow2BGV, _, true> = DefaultModswitchStrategy::new(NaiveBGVNoiseEstimator);
    let ZpeX = DensePolyRing::new(P.base_ring(), "X");
    // the digit-retain circuit has constants in `P.base_ring()` (a `Zn`); map them into the plaintext
    // ring `P`, which is one of the supported `AsBGVPlaintext` rings
    let circuit = poly_to_circuit(&ZpeX, &[centered_digit_retain_poly(&ZpeX, 3)])
        .change_ring_uniform(|c| c.change_ring(|x| P.inclusion().map(x)));

    let input = P.int_hom().map(17 * 17 + 2 * 17 - 3);
    let ct = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk, 3.2);
    let res = modswitch_strategy.evaluate_circuit(
        &circuit,
        &P,
        &P,
        &C,
        &[ModulusAwareCiphertext {
            dropped_rns_factor_indices: RNSFactorIndexList::empty(),
            info: modswitch_strategy.fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
            data: CiphertextOrNoRelin::Relin(Pow2BGV::clone_ct(&P, &C, &ct))
        }],
        Some(&rk),
        &[],
        Some(&sk)
    ).into_iter().next().unwrap();

    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);
    let res_ct = res.data.unwrap_relin();
    let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res_ct, &res_sk);
    println!("Actual output noise budget is {}", res_noise);
    assert_el_eq!(&P, &circuit.evaluate(&[P.clone_el(&input)], P.identity())[0], Pow2BGV::dec(&P, &res_C, res_ct, &res_sk));
}

#[test]
fn test_level_digits() {
    feanor_tracing::DelayedLogger::init_test();
    let a = [2, 2, 6, 6];
    let b = [2, 2, 3, 3];
    let k = 2;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 3);

    let a = [3, 3, 3, 3];
    let b = [3, 3, 3, 3];
    let k = 3;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 4);

    let a = [3, 3, 3, 3];
    let b = [3, 3, 3, 3];
    let k = 4;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 4);

    let a = [2, 4, 4, 4];
    let b = [2, 2, 2, 2];
    let k = 1;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 4);

    let a = [2, 3, 3, 4];
    let b = [1, 2, 3, 4];
    let k = 1;
    assert!(level_digits(&a, &b, k).is_none());

    let a = [3, 3, 3, 4];
    let b = [1, 2, 3, 4];
    let k = 1;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 4);

    let a = [3, 4, 5, 5];
    let b = [1, 2, 3, 4];
    let k = 1;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 3);
}
