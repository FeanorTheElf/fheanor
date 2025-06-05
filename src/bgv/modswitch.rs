use core::f64;
use std::cell::RefCell;
use std::cmp::min;
use std::ops::Range;

use feanor_math::homomorphism::Homomorphism;
use feanor_math::primitive_int::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::zn_64::ZnEl;
use feanor_math::algorithms::matmul::ComputeInnerProduct;

use crate::bgv::noise_estimator::BGVNoiseEstimator;
use crate::circuit::evaluator::DefaultCircuitEvaluator;
use crate::circuit::*;
use crate::cyclotomic::CyclotomicGaloisGroupEl;
use crate::gadget_product::digits::*;
use crate::ZZi64;

use super::noise_estimator::AlwaysZeroNoiseEstimator;
use super::*;

///
/// Given vectors `a` and `b` such that `b <= a`, finds vectors `c <= b` and `d` such
/// that `sum_i c_i = k` and `a, sum_i d_i >= b - c + d` which minimize the number of
/// nonzero entries of `b - c + d`.
/// 
/// Note that this is a very good heuristic, and will be optimal in most cases.
/// In general, it will not give the optimal solution, however.
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
/// A [`Ciphertext`] which additionally stores w.r.t. which ciphertext modulus it is defined,
/// and which noise level (as measured by some [`BGVModswitchStrategy`]) it is estimated to have.
///
pub struct ModulusAwareCiphertext<Params: BGVCiphertextParams, Strategy: ?Sized + BGVModswitchStrategy<Params>> {
    /// The stored raw ciphertext
    pub data: Ciphertext<Params>,
    /// The indices of those RNS components w.r.t. a "master RNS base" (specified by the context)
    /// that are not used for this ciphertext; in other words, the ciphertext modulus of this ciphertext
    /// is the product of all RNS factors of the master RNS base that are not mentioned in this list
    pub dropped_rns_factor_indices: Box<RNSFactorIndexList>,
    /// Additional information required by the modulus-switching strategy
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
pub trait BGVModswitchStrategy<Params: BGVCiphertextParams> {

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
        gks: &[(CyclotomicGaloisGroupEl, KeySwitchKey<Params>)],
        key_switches: &mut usize,
        debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<ModulusAwareCiphertext<Params, Self>>
        where R: RingStore,
            R::Type: AsBGVPlaintext<Params>;

    ///
    /// Returns the info that describes a freshly encrypted ciphertext, w.r.t. a secret
    /// key of hamming weight `sk_hwt`, or a uniformly ternary secret key if `sk_hwt = None`.
    /// 
    /// In other words, this describes the output of [`BGVCiphertextParams::enc_sym()`].
    /// 
    fn info_for_fresh_encryption(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk_hwt: Option<usize>) -> Self::CiphertextInfo;

    fn clone_info(&self, info: &Self::CiphertextInfo) -> Self::CiphertextInfo;

    fn print_info(&self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ct: &ModulusAwareCiphertext<Params, Self>);

    fn clone_ct(&self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ct: &ModulusAwareCiphertext<Params, Self>) -> ModulusAwareCiphertext<Params, Self> {
        let C = Params::mod_switch_down_C(C_master, &ct.dropped_rns_factor_indices);
        ModulusAwareCiphertext {
            data: Params::clone_ct(P, &C, &ct.data),
            info: self.clone_info(&ct.info),
            dropped_rns_factor_indices: ct.dropped_rns_factor_indices.clone()
        }
    }
}

///
/// Trait for rings whose elements can be used as plaintexts in
/// plaintext-ciphertext operations in BGV.
/// 
/// In particular, this includes
///  - integers
///  - plaintext ring elements
///  - ciphertext ring elements - usually these are plaintext ring
///    elements that have already been lifted to the ciphertext ring
///    to avoid the cost of this conversion later
/// 
pub trait AsBGVPlaintext<Params: BGVCiphertextParams>: RingBase {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params>;

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor;

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params>;

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor;

    fn hom_inner_product<I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (Self::Element, Ciphertext<Params>)>
    {
        let mut first_implicit_scale = None;
        data.fold(Params::transparent_zero(P, C), |current, (lhs, rhs)| {
            if first_implicit_scale.is_none() {
                first_implicit_scale = Some(rhs.implicit_scale);
            } else {
                assert!(P.base_ring().eq_el(&first_implicit_scale.unwrap(), &rhs.implicit_scale));
            }
            Params::hom_add(P, C, current, self.hom_mul_to(P, C, dropped_factors, &lhs, rhs))
        })
    }

    fn hom_inner_product_noise<'a, 'b, N: BGVNoiseEstimator<Params>, I>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> N::NoiseDescriptor
        where I: Iterator<Item = (&'a Self::Element, &'b N::NoiseDescriptor)>,
        Self: 'a,
        N::NoiseDescriptor: 'b
    {
        data.fold(estimator.transparent_zero(), |current, (lhs, rhs)| {
            estimator.hom_add(P, C, &current, P.base_ring().one(), &self.hom_mul_to_noise(estimator, P, C, dropped_factors, lhs, &rhs, &P.base_ring().one()), P.base_ring().one())
        })
    }

    fn apply_galois_action_plain(
        &self,
        P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[CyclotomicGaloisGroupEl]
    ) -> Vec<Self::Element>;
}

///
/// Chooses `drop_prime_count` indices from `0..rns_base_len`. These indices are chosen in a way
/// that minimizes the noise growth of key-switching (with the given parameters) after we drop the
/// corresponding RNS factors.
/// 
/// This function will never return indices corresponding to special moduli.
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
/// ```
/// # use feanor_math::seq::*;
/// # use fheanor::gadget_product::*;
/// # use fheanor::bgv::KeySwitchKeyParams;
/// # use fheanor::bgv::modswitch::recommended_rns_factors_to_drop;
/// # use fheanor::gadget_product::digits::*;
/// let digits = RNSGadgetVectorDigitIndices::from([0..3, 3..5].clone_els());
/// let params = KeySwitchKeyParams {
///     digits_without_special: digits,
///     special_modulus_factor_count: 0
/// };
/// // remove the first two indices from 0..3, and the first index from 3..5 - the resulting ranges both have length 1
/// assert_eq!(&[0usize, 1, 3][..] as &[usize], &*recommended_rns_factors_to_drop(params, 3) as &[usize]);
/// ```
/// 
pub fn recommended_rns_factors_to_drop(key_digits: &RNSGadgetVectorDigitIndices, drop_prime_count: usize) -> Box<RNSFactorIndexList> {
    assert!(drop_prime_count < key_digits.rns_base_len());

    let mut drop_from_digit = (0..key_digits.len()).map(|_| 0).collect::<Vec<_>>();

    let effective_len = |range: Range<usize>| range.end - range.start;
    for _ in 0..drop_prime_count {
        let largest_digit_idx = (0..key_digits.len()).max_by_key(|i| effective_len(key_digits.at(*i)) - drop_from_digit[*i]).unwrap();
        drop_from_digit[largest_digit_idx] += 1;
    }

    let result = RNSFactorIndexList::from((0..key_digits.len()).flat_map(|i| key_digits.at(i).start..(key_digits.at(i).start + drop_from_digit[i])).collect(), key_digits.rns_base_len());
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
///
/// These points lead to a relatively simple and generally well-performing modulus switching strategy.
/// However, there may be situations where deviating from 1. could lead to a lower number of mod-switches
/// (and thus better performance), and deviating from 2. could be used for a finer-tuned mod-switching,
/// and thus less noise growth.
///
pub struct DefaultModswitchStrategy<Params: BGVCiphertextParams, N: BGVNoiseEstimator<Params>, const LOG: bool> {
    params: PhantomData<Params>,
    noise_estimator: N
}

impl<Params: BGVCiphertextParams> DefaultModswitchStrategy<Params, AlwaysZeroNoiseEstimator, false> {

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
/// Used internally when evaluating a circuit, since we want to store plaintexts
/// as plaintexts as long as possible - or rather until we know w.r.t. which RNS
/// base we should convert them into a ciphertext ring element
/// 
enum PlainOrCiphertext<'a, Params: BGVCiphertextParams, Strategy: BGVModswitchStrategy<Params>, R: ?Sized + RingBase> {
    Plaintext(Coefficient<R>),
    PlaintextRef(&'a Coefficient<R>),
    CiphertextRef(&'a ModulusAwareCiphertext<Params, Strategy>),
    Ciphertext(ModulusAwareCiphertext<Params, Strategy>)
}

impl<'a, Params: BGVCiphertextParams, Strategy: BGVModswitchStrategy<Params>, R: ?Sized + RingBase> PlainOrCiphertext<'a, Params, Strategy, R> {

    fn as_ciphertext_ref<'b>(&'b self) -> Result<&'b ModulusAwareCiphertext<Params, Strategy>, &'b Coefficient<R>> {
        match self {
            PlainOrCiphertext::Plaintext(x) => Err(x),
            PlainOrCiphertext::PlaintextRef(x) => Err(x),
            PlainOrCiphertext::Ciphertext(x) => Ok(x),
            PlainOrCiphertext::CiphertextRef(x) => Ok(x)
        }
    }

    fn as_ciphertext<S: RingStore<Type = R>>(self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ring: S, strategy: &Strategy) -> Result<(CiphertextRing<Params>, ModulusAwareCiphertext<Params, Strategy>), Coefficient<R>> {
        match self {
            PlainOrCiphertext::Plaintext(x) => Err(x),
            PlainOrCiphertext::PlaintextRef(x) => Err(x.clone(ring)),
            PlainOrCiphertext::CiphertextRef(x) => {
                let Cx = Params::mod_switch_down_C(C_master, &x.dropped_rns_factor_indices);
                let x = ModulusAwareCiphertext {
                    data: Params::clone_ct(P, &Cx, &x.data),
                    dropped_rns_factor_indices: x.dropped_rns_factor_indices.clone(),
                    info: strategy.clone_info(&x.info)
                };
                Ok((Cx, x))
            },
            PlainOrCiphertext::Ciphertext(x) => {
                let Cx = Params::mod_switch_down_C(C_master, &x.dropped_rns_factor_indices);
                Ok((Cx, x))
            }
        }
    }
}

impl<Params: BGVCiphertextParams> AsBGVPlaintext<Params> for StaticRingBase<i64> {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain_encoded(P, C, &C.inclusion().map(C.base_ring().coerce(&ZZi64, *m)), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor {
        estimator.hom_add_plain_encoded(P, C, &C.inclusion().map(C.base_ring().coerce(&ZZi64, *m)), ct_info, *implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain_i64(P, C, *m, ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor {
        estimator.hom_mul_plain_i64(P, C, *m, ct_info, *implicit_scale)
    }

    fn apply_galois_action_plain(
        &self,
        _P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[CyclotomicGaloisGroupEl]
    ) -> Vec<Self::Element> {
        gs.iter().map(|_| self.clone_el(x)).collect()
    }
}

impl<Params: BGVCiphertextParams> AsBGVPlaintext<Params> for StaticRingBase<i32> {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain_encoded(P, C, &C.inclusion().map(C.base_ring().coerce(&StaticRing::<i32>::RING, *m)), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor {
        estimator.hom_add_plain_encoded(P, C, &C.inclusion().map(C.base_ring().coerce(&StaticRing::<i32>::RING, *m)), ct_info, *implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain_i64(P, C, *m as i64, ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor {
        estimator.hom_mul_plain_i64(P, C, *m as i64, ct_info, *implicit_scale)
    }

    fn apply_galois_action_plain(
        &self,
        _P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[CyclotomicGaloisGroupEl]
    ) -> Vec<Self::Element> {
        gs.iter().map(|_| self.clone_el(x)).collect()
    }
}

impl<Params: BGVCiphertextParams> AsBGVPlaintext<Params> for NumberRingQuotientBase<NumberRing<Params>, Zn> {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain(P, C, m, ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor {
        estimator.hom_add_plain(P, C, m, ct_info, *implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain(P, C, m, ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor {
        estimator.hom_mul_plain(P, C, m, ct_info, *implicit_scale)
    }

    fn apply_galois_action_plain(
        &self,
        _P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[CyclotomicGaloisGroupEl]
    ) -> Vec<Self::Element> {
        self.apply_galois_action_many(x, gs)
    }
}

impl<Params: BGVCiphertextParams, A: Allocator + Clone> AsBGVPlaintext<Params> for ManagedDoubleRNSRingBase<NumberRing<Params>, A>
    where CiphertextRing<Params>: RingStore<Type = ManagedDoubleRNSRingBase<NumberRing<Params>, A>>
{
    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, self.clone_el(m)), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor {
        estimator.hom_add_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, self.clone_el(m)), ct_info, *implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, self.clone_el(m)), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::NoiseDescriptor, 
        implicit_scale: &ZnEl
    ) -> N::NoiseDescriptor {
        estimator.hom_mul_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, self.clone_el(m)), ct_info, *implicit_scale)
    }

    #[instrument(skip_all)]
    fn hom_inner_product<I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (Self::Element, Ciphertext<Params>)>
    {
        let mut lhs = Vec::new();
        let mut rhs_c0 = Vec::new();
        let mut rhs_c1 = Vec::new();
        let mut first_implicit_scale = None;
        for (l, r) in data {
            if first_implicit_scale.is_none() {
                first_implicit_scale = Some(r.implicit_scale);
            } else {
                assert!(P.base_ring().eq_el(&first_implicit_scale.unwrap(), &r.implicit_scale));
            }
            lhs.push(l);
            rhs_c0.push(r.c0);
            rhs_c1.push(r.c1);
        }
        return Ciphertext {
            implicit_scale: first_implicit_scale.unwrap_or(P.base_ring().one()),
            c0: <_ as ComputeInnerProduct>::inner_product(C.get_ring(), lhs.iter().zip(rhs_c0.into_iter()).map(|(lhs, rhs)| (C.get_ring().drop_rns_factor_element(self, dropped_factors, self.clone_el(lhs)), rhs))),
            c1: <_ as ComputeInnerProduct>::inner_product(C.get_ring(), lhs.into_iter().zip(rhs_c1.into_iter()).map(|(lhs, rhs)| (C.get_ring().drop_rns_factor_element(self, dropped_factors, lhs), rhs))),
        };
    }

    fn apply_galois_action_plain(
        &self,
        _P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[CyclotomicGaloisGroupEl]
    ) -> Vec<Self::Element> {
        self.apply_galois_action_many(x, gs)
    }
}

impl<Params: BGVCiphertextParams, N: BGVNoiseEstimator<Params>, const LOG: bool> DefaultModswitchStrategy<Params, N, LOG> {

    pub fn new(noise_estimator: N) -> Self {
        Self {
            params: PhantomData,
            noise_estimator: noise_estimator
        }
    }

    pub fn from_noise_level(&self, noise_level: N::NoiseDescriptor) -> <Self as BGVModswitchStrategy<Params>>::CiphertextInfo {
        noise_level
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
        let x_noise_budget = if let Some(sk) = debug_sk {
            let sk_x = Params::mod_switch_down_sk(&Cx, C_master, &x.dropped_rns_factor_indices, sk);
            Some(Params::noise_budget(P, &Cx, &x.data, &sk_x))
        } else { None };
        let result = ModulusAwareCiphertext {
            data: Params::mod_switch_down_ct(P, &C_target, &Cx, &drop_x, x.data),
            info: self.noise_estimator.mod_switch_down(&P, &C_target, &Cx, &drop_x, &x.info),
            dropped_rns_factor_indices: dropped_factors_target.to_owned()
        };
        if LOG && drop_x.len() > 0 {
            println!("{}: Dropping RNS factors {} of operand, estimated noise budget {}/{} -> {}/{}",
                context,
                drop_x,
                -self.noise_estimator.estimate_log2_relative_noise_level(P, &Cx, &x.info).round(),
                ZZbig.abs_log2_ceil(Cx.base_ring().modulus()).unwrap(),
                -self.noise_estimator.estimate_log2_relative_noise_level(P, C_target, &result.info).round(),
                ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap(),
            );
            if let Some(sk) = debug_sk {
                let sk_target = Params::mod_switch_down_sk(C_target, C_master, &dropped_factors_target, sk);
                println!("  actual noise budget: {} -> {}", x_noise_budget.unwrap(), Params::noise_budget(P, C_target, &result.data, &sk_target));
            }
        }
        return result;
    }

    ///
    /// Mod-switches the given ciphertext from its current ciphertext ring
    /// to `C_target`, and adjusts the noise information.
    /// 
    fn mod_switch_down_ref(
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
        let drop_x = dropped_factors_target.pushforward(&x.dropped_rns_factor_indices);
        let result = ModulusAwareCiphertext {
            data: Params::mod_switch_down_ct(P, &C_target, &Cx, &drop_x, Params::clone_ct(P, &Cx, &x.data)),
            info: self.noise_estimator.mod_switch_down(&P, &C_target, &Cx, &drop_x, &x.info),
            dropped_rns_factor_indices: dropped_factors_target.to_owned()
        };
        if LOG && drop_x.len() > 0 {
            println!("{}: Dropping RNS factors {} of operand, estimated noise budget {}/{} -> {}/{}",
                context,
                drop_x,
                -self.noise_estimator.estimate_log2_relative_noise_level(P, &Cx, &x.info).round(),
                ZZbig.abs_log2_ceil(Cx.base_ring().modulus()).unwrap(),
                -self.noise_estimator.estimate_log2_relative_noise_level(P, C_target, &result.info).round(),
                ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap(),
            );
            if let Some(sk) = debug_sk {
                let sk_target = Params::mod_switch_down_sk(C_target, C_master, &dropped_factors_target, sk);
                let sk_x = Params::mod_switch_down_sk(&Cx, C_master, &x.dropped_rns_factor_indices, sk);
                println!("  actual noise budget: {} -> {}", Params::noise_budget(P, &Cx, &x.data, &sk_x), Params::noise_budget(P, C_target, &result.data, &sk_target));
            }
        }
        return result;
    }

    ///
    /// Finds `drop_additional` RNS factors outside of `dropped_factors_input` and
    /// `special_modulus_count` RNS factors such that removing the former, together with
    /// `dropped_factors_input`, and adding the latter, results in the smallest number
    /// of digits in `key_switch_key_digits`, under the constraint that `special_modulus_count`
    /// is larger or equal to the size of the largest digit.
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
    fn compute_optimal_special_modulus(
        &self,
        _P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        dropped_factors_input: &RNSFactorIndexList,
        drop_additional: usize,
        key_switch_key_digits: &RNSGadgetVectorDigitIndices
    ) -> (/* B_final = */ Box<RNSFactorIndexList>, /* B_special = */ Box<RNSFactorIndexList>) {
        let a = key_switch_key_digits.iter().map(|digit| digit.end - digit.start).collect::<Vec<_>>();
        let b = key_switch_key_digits.iter().map(|digit| digit.end - digit.start - dropped_factors_input.num_within(&digit)).collect::<Vec<_>>();
        if let Some((c, d)) = level_digits(&a, &b, drop_additional) {
            let B_additional = key_switch_key_digits.iter().enumerate().flat_map(|(digit_idx, digit)| digit.filter(|i| !dropped_factors_input.contains(*i)).take(c[digit_idx]));
            let B_final = RNSFactorIndexList::from(dropped_factors_input.iter().copied().chain(B_additional).collect::<Vec<_>>(), C_master.base_ring().len());
            let B_special = RNSFactorIndexList::from(key_switch_key_digits.iter().enumerate().flat_map(|(digit_idx, digit)| digit.filter(|i| B_final.contains(*i)).take(d[digit_idx])).collect::<Vec<_>>(), C_master.base_ring().len());
            assert_eq!(B_final.len(), dropped_factors_input.len() + drop_additional);
            return (B_final, B_special);
        } else {
            let additional_drop = recommended_rns_factors_to_drop(&key_switch_key_digits.remove_indices(dropped_factors_input), drop_additional);
            let B_final = additional_drop.pullback(dropped_factors_input);
            let B_special = B_final.clone();
            assert_eq!(B_final.len(), dropped_factors_input.len() + drop_additional);
            return (B_final, B_special);
        }
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
        noise_x: &N::NoiseDescriptor,
        dropped_factors_x: &RNSFactorIndexList,
        noise_y: &N::NoiseDescriptor,
        dropped_factors_y: &RNSFactorIndexList,
        rk_digits: &RNSGadgetVectorDigitIndices
    ) -> (/* total_drop = */ Box<RNSFactorIndexList>, /* special_modulus = */ Box<RNSFactorIndexList>) {
        let Cx = Params::mod_switch_down_C(C_master, dropped_factors_x);
        let Cy = Params::mod_switch_down_C(C_master, dropped_factors_y);

        // first, we drop all the RNS factors that are required to make the product well-defined;
        // these are exactly the RNS factors that are missing in either input
        let base_drop = dropped_factors_x.union(&dropped_factors_y);

        // now try every number of additional RNS factors to drop
        let compute_result_noise = |num_to_drop: usize| {
            let (total_drop, special_modulus) = self.compute_optimal_special_modulus(P, C_master, &base_drop, num_to_drop, rk_digits);
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
                    &total_drop.pushforward(&total_drop_without_special),
                    &self.noise_estimator.mod_switch_down(&P, &C_target, &Cx, &total_drop.pushforward(dropped_factors_x), noise_x),
                    &self.noise_estimator.mod_switch_down(&P, &C_target, &Cy, &total_drop.pushforward(dropped_factors_y), noise_y),
                    &rk_digits_after_total_drop
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
    /// This function is quite complicated, as there are many things to consider:
    ///  - We have to handle both constants and ciphertexts
    ///  - Special coefficients (e.g. `0, 1, -1`) should be handled without a full
    ///    plaintext-ciphertext multiplication
    ///  - We decide not to perform intermediate modulus-switches, but only modulus-switch
    ///    at the very beginning. Note however that it might be possible to group
    ///    summands depending on their RNS base, and reduce the number of modulus-switches
    ///  - We have to decide on the `implicit_scale` of the result, its choice may
    ///    affect noise growth 
    ///  - using inner product functionality of the underlying ring can give us better
    ///    performance than many isolated additions/multiplications
    /// 
    #[instrument(skip_all)]
    fn add_inner_prod<'a, R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: PlainOrCiphertext<'a, Params, Self, R::Type>,
        cs: &[Coefficient<R::Type>],
        ys: &[PlainOrCiphertext<'a, Params, Self, R::Type>],
        ring: R,
        debug_sk: Option<&SecretKey<Params>>
    ) -> PlainOrCiphertext<'a, Params, Self, R::Type>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        assert_eq!(cs.len(), ys.len());

        // first, we separate the inner product into three parts:
        //  - the constant part, which does not contain any ciphertexts and is immediately computed
        //  - the integer part, which is of the form `sum_i c[i] * ct[i]` with `c[i]` being integers
        //  - the main part, which is of the form `sum_i c[i] * ct[i]` with `c[i]` being elements of `R`
        let mut constant = Coefficient::Zero;
        let mut int_products: Vec<(i32, &ModulusAwareCiphertext<Params, Self>)> = Vec::new();
        let mut main_products:  Vec<(&El<R>, &ModulusAwareCiphertext<Params, Self>)> = Vec::new();

        // while separating the different summands, we also keep track of which will be the result modulus
        let mut total_drop = RNSFactorIndexList::empty();
        let mut min_dropped_len = usize::MAX;
        let mut update_total_drop = |ct: &ModulusAwareCiphertext<Params, Self>| {
            total_drop = total_drop.union(&ct.dropped_rns_factor_indices);
            min_dropped_len = min(min_dropped_len, ct.dropped_rns_factor_indices.len());
        };

        for (c, y) in cs.iter().zip(ys.iter()) {
            match y.as_ciphertext_ref() {
                Err(y) => constant = constant.add(c.clone(ring).mul(y.clone(ring), ring), ring),
                Ok(y) => if !c.is_zero() {
                    update_total_drop(y);
                    match c {
                        Coefficient::Zero => unreachable!(),
                        Coefficient::One => int_products.push((1, y)),
                        Coefficient::NegOne => int_products.push((-1, y)),
                        Coefficient::Integer(c) => int_products.push((*c, y)),
                        Coefficient::Other(c) => main_products.push((c, y)),
                    }
                }
            }
        }
        match x.as_ciphertext_ref() {
            Ok(x) => {
                update_total_drop(x);
            },
            Err(x) => if int_products.len() == 0 && main_products.len() == 0 {
                // if `x` is a constant and we have no products involving ciphertexts, everything is just a constant
                return PlainOrCiphertext::Plaintext(x.clone(ring).add(constant, ring));
            }
        }
        assert!(min_dropped_len <= total_drop.len());

        let C_target = Params::mod_switch_down_C(C_master, &total_drop);

        // now perform modulus-switches when necessary
        let mut int_products: Vec<(i32, ModulusAwareCiphertext<Params, Self>)> = int_products.into_iter().map(|(c, y)| (
            c,
            self.mod_switch_down_ref(P, &C_target, C_master, &total_drop, y, "HomInnerProduct", debug_sk)
        )).collect();

        let mut main_products: Vec<(El<R>, ModulusAwareCiphertext<Params, Self>)> = main_products.into_iter().map(|(c, y)| (
            ring.clone_el(c),
            self.mod_switch_down_ref(P, &C_target, C_master, &total_drop, y, "HomInnerProduct", debug_sk)
        )).collect();

        // finally, we do another noise optimization technique: the implicit scale of the output is
        // chosen as total scale (implicit scale + coefficient) of the highest-noise ciphertext; this way
        // we avoid multiplying its size up further
        let Zt = P.base_ring();
        let output_implicit_scale: ZnEl = int_products.iter().filter_map(|(c, ct)| Zt.invert(&Zt.int_hom().map(*c)).map(|c| (c, ct)))
            .map(|(c, ct)| (self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &ct.info), Zt.mul(ct.data.implicit_scale, c))
        ).max_by(|(l, _), (r, _)| f64::total_cmp(l, r)).map(|(_, scale)| scale).unwrap_or(P.base_ring().one());

        for (c, ct) in &mut int_products {
            *c = Zt.smallest_lift(Zt.mul(Zt.int_hom().map(*c), Zt.checked_div(&output_implicit_scale, &ct.data.implicit_scale).unwrap())) as i32;
            ct.data.implicit_scale = output_implicit_scale;
        }
        for (c, ct) in &mut main_products {
            let factor = Zt.smallest_lift(Zt.checked_div(&output_implicit_scale, &ct.data.implicit_scale).unwrap()) as i32;
            if factor != 1 {
                ring.int_hom().mul_assign_map(c, factor);
            }
            ct.data.implicit_scale = output_implicit_scale;
        }

        let int_product_noise = StaticRing::<i32>::RING.get_ring().hom_inner_product_noise(&self.noise_estimator, P, &C_target, &total_drop, int_products.iter().map(|(lhs, rhs)| (lhs, &rhs.info)));
        let int_product_part = StaticRing::<i32>::RING.get_ring().hom_inner_product(P, &C_target, &total_drop, int_products.into_iter().map(|(lhs, rhs)| (lhs, rhs.data)));

        let main_product_noise = ring.get_ring().hom_inner_product_noise(&self.noise_estimator, P, &C_target, &total_drop, main_products.iter().map(|(lhs, rhs)| (lhs, &rhs.info)));
        let main_product_part = ring.get_ring().hom_inner_product(P, &C_target, &total_drop, main_products.into_iter().map(|(lhs, rhs)| (lhs, rhs.data)));

        return PlainOrCiphertext::Ciphertext(match x.as_ciphertext(P, C_master, ring, self) {
            Ok((_, x)) => {
                let x_modswitch = self.mod_switch_down(P, &C_target, C_master, &total_drop, x, "HomAdd", debug_sk);
                ModulusAwareCiphertext {
                    info: self.noise_estimator.hom_add(P, &C_target, &x_modswitch.info, x_modswitch.data.implicit_scale, 
                        &self.noise_estimator.hom_add(P, &C_target, &int_product_noise, P.base_ring().one(), &main_product_noise, P.base_ring().one()),
                        P.base_ring().one()
                    ),
                    data: ring.get_ring().hom_add_to(P, &C_target, &total_drop,
                        &constant.to_ring_el(&ring),
                        Params::hom_add(P, &C_target, x_modswitch.data, Params::hom_add(P, &C_target, int_product_part, main_product_part))
                    ),
                    dropped_rns_factor_indices: total_drop
                }
            },
            Err(x) => {
                constant = constant.add(x, ring);
                // ignore the last plaintext addition for noise analysis, its gonna be fine
                let res_info = self.noise_estimator.hom_add(P, &C_target, &int_product_noise, P.base_ring().one(), &main_product_noise, P.base_ring().one());
                let product_data = Params::hom_add(P, &C_target, int_product_part, main_product_part);
                let res_data = match constant {
                    Coefficient::Zero => product_data,
                    Coefficient::One => Params::hom_add_plain_encoded(P, &C_target, &C_target.one(), product_data),
                    Coefficient::NegOne => Params::hom_add_plain_encoded(P, &C_target, &C_target.neg_one(), product_data),
                    Coefficient::Integer(c) => Params::hom_add_plain_encoded(P, &C_target, &C_target.int_hom().map(c), product_data),
                    Coefficient::Other(m) => ring.get_ring().hom_add_to(P, &C_target, &total_drop, &m, product_data),
                };
                ModulusAwareCiphertext {
                    data: res_data,
                    info: res_info,
                    dropped_rns_factor_indices: total_drop
                }
            }
        });
    }

    #[instrument(skip_all)]
    fn mul<'a, R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: PlainOrCiphertext<'a, Params, Self, R::Type>,
        y: PlainOrCiphertext<'a, Params, Self, R::Type>,
        ring: R,
        rk: Option<&RelinKey<Params>>,
        key_switches: &RefCell<&mut usize>,
        debug_sk: Option<&SecretKey<Params>>
    ) -> PlainOrCiphertext<'a, Params, Self, R::Type>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        match (x.as_ciphertext(P, C_master, ring, self), y.as_ciphertext(P, C_master, ring, self)) {
            (Err(x), Err(y)) => PlainOrCiphertext::Plaintext(x.mul(y, ring)),
            // possibly swap `x` and `y` here so that we can handle both asymmetric cases in one statement
            (Ok((Cx, x)), Err(y)) | (Err(y), Ok((Cx, x))) => PlainOrCiphertext::Ciphertext({
                let total_drop = x.dropped_rns_factor_indices.clone();
                let C_target = &Cx;
                
                let (res_info, res_data) = match y {
                    Coefficient::Zero => unreachable!(),
                    Coefficient::One => (x.info, x.data),
                    Coefficient::NegOne => (x.info, Params::hom_mul_plain_i64(P, &C_target, -1, x.data)),
                    Coefficient::Integer(c) => (
                        StaticRing::<i64>::RING.get_ring().hom_mul_to_noise(&self.noise_estimator, P, &C_target, &total_drop, &(c as i64), &x.info, &x.data.implicit_scale),
                        StaticRing::<i64>::RING.get_ring().hom_mul_to(P, &C_target, &total_drop, &(c as i64), Params::clone_ct(P, &Cx, &x.data)),
                    ),
                    Coefficient::Other(m) => (
                        ring.get_ring().hom_mul_to_noise(&self.noise_estimator, P, &C_target, &total_drop, &m, &x.info, &x.data.implicit_scale),
                        ring.get_ring().hom_mul_to(P, &C_target, &total_drop, &m, Params::clone_ct(P, &Cx, &x.data)),
                    ),
                };

                ModulusAwareCiphertext {
                    data: res_data,
                    info: res_info,
                    dropped_rns_factor_indices: total_drop
                }
            }),
            // the ciphertext-ciphertext multiplication case
            (Ok((_, x)), Ok((_, y))) => PlainOrCiphertext::Ciphertext({
                assert!(x.dropped_rns_factor_indices.len() < C_master.base_ring().len());
                assert!(y.dropped_rns_factor_indices.len() < C_master.base_ring().len());
                **key_switches.borrow_mut() += 1;
                let rk = rk.unwrap();

                let (total_drop, special_modulus) = self.compute_optimal_mul_modswitch(P, C_master, &x.info, &x.dropped_rns_factor_indices, &y.info, &y.dropped_rns_factor_indices, rk.gadget_vector_digits());
                let total_drop_without_special = total_drop.subtract(&special_modulus);
                let C_special = Params::mod_switch_down_C(&C_master, &total_drop_without_special);
                let C_target = Params::mod_switch_down_C(C_master, &total_drop);
                let rk_modswitch = Params::mod_switch_down_rk(&C_special, C_master, &total_drop_without_special, &rk);
                debug_assert!(total_drop.len() >= x.dropped_rns_factor_indices.len());
                debug_assert!(total_drop.len() >= y.dropped_rns_factor_indices.len());

                let x_modswitched = self.mod_switch_down(P, &C_target, C_master, &total_drop, x, "HomMul", debug_sk);
                let y_modswitched = self.mod_switch_down(P, &C_target, C_master, &total_drop, y, "HomMul", debug_sk);

                if LOG {
                    println!(
                        "Using a special modulus of {} RNS factors and a gadget vector of {} digits (largest has {} RNS factors) for relinearization", 
                        special_modulus.len(), 
                        rk_modswitch.gadget_vector_digits().len(),
                        rk_modswitch.gadget_vector_digits().iter().map(|digit| digit.end - digit.start).max().unwrap()
                    );
                }

                let res_data = Params::hom_mul(
                    P, 
                    &C_target, 
                    &C_special, 
                    &total_drop.pushforward(&total_drop_without_special),
                    x_modswitched.data, 
                    y_modswitched.data, 
                    &rk_modswitch
                );
                let res_info = self.noise_estimator.hom_mul(
                    P, 
                    &C_target, 
                    &C_special, 
                    &total_drop.pushforward(&total_drop_without_special),
                    &x_modswitched.info, 
                    &y_modswitched.info, 
                    rk_modswitch.gadget_vector_digits()
                );

                if LOG {
                    println!("HomMul: Result has estimated noise budget {}/{}",
                        -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &res_info).round(),
                        ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
                    );
                    if let Some(sk) = debug_sk {
                        let sk_target = Params::mod_switch_down_sk(&C_target, C_master, &total_drop, sk);
                        println!("  actual noise budget: {}", Params::noise_budget(P, &C_target, &res_data, &sk_target));
                    }
                }
                ModulusAwareCiphertext {
                    dropped_rns_factor_indices: total_drop,
                    info: res_info,
                    data: res_data
                }
            })
        }
    }

    #[instrument(skip_all)]
    fn square<'a, R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: PlainOrCiphertext<'a, Params, Self, R::Type>,
        ring: R,
        rk: Option<&RelinKey<Params>>,
        key_switches: &RefCell<&mut usize>,
        debug_sk: Option<&SecretKey<Params>>
    ) -> PlainOrCiphertext<'a, Params, Self, R::Type>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        match x.as_ciphertext(P, C_master, ring, self) {
            Err(x) => PlainOrCiphertext::Plaintext(x.clone(ring).mul(x, ring)),
            Ok((_, x)) => PlainOrCiphertext::Ciphertext({
                assert!(x.dropped_rns_factor_indices.len() < C_master.base_ring().len());
                **key_switches.borrow_mut() += 1;
                let rk = rk.unwrap();

                let (total_drop, special_modulus) = self.compute_optimal_mul_modswitch(P, C_master, &x.info, &x.dropped_rns_factor_indices, &x.info, &x.dropped_rns_factor_indices, rk.gadget_vector_digits());
                let total_drop_without_special = total_drop.subtract(&special_modulus);
                let C_special = Params::mod_switch_down_C(&C_master, &total_drop_without_special);
                let C_target = Params::mod_switch_down_C(C_master, &total_drop);
                let rk_modswitch = Params::mod_switch_down_rk(&C_special, C_master, &total_drop_without_special, &rk);
                debug_assert!(total_drop.len() >= x.dropped_rns_factor_indices.len());

                let x_modswitched = self.mod_switch_down(P, &C_target, C_master, &total_drop, x, "HomSquare", debug_sk);

                if LOG {
                    println!(
                        "Using a special modulus of {} RNS factors and a gadget vector of {} digits (largest has {} RNS factors) for relinearization", 
                        special_modulus.len(), 
                        rk_modswitch.gadget_vector_digits().len(),
                        rk_modswitch.gadget_vector_digits().iter().map(|digit| digit.end - digit.start).max().unwrap()
                    );
                }

                let res_info = self.noise_estimator.hom_mul(
                    P, 
                    &C_target, 
                    &C_special, 
                    &total_drop.pushforward(&total_drop_without_special),
                    &x_modswitched.info,
                    &x_modswitched.info,
                    &rk_modswitch.gadget_vector_digits()
                );
                let res_data = Params::hom_square(
                    P, 
                    &C_target, 
                    &C_special, 
                    &total_drop.pushforward(&total_drop_without_special),
                    x_modswitched.data, 
                    &rk_modswitch
                );

                if LOG {
                    println!("HomSquare: Result has estimated noise budget {}/{}",
                        -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &res_info).round(),
                        ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
                    );
                    if let Some(sk) = debug_sk {
                        let sk_target = Params::mod_switch_down_sk(&C_target, C_master, &total_drop, sk);
                        println!("  actual noise budget: {}", Params::noise_budget(P, &C_target, &res_data, &sk_target));
                    }
                }
                ModulusAwareCiphertext {
                    dropped_rns_factor_indices: total_drop,
                    info: res_info,
                    data: res_data
                }
            })
        }
    }

    #[instrument(skip_all)]
    fn gal_many<'a, R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: PlainOrCiphertext<'a, Params, Self, R::Type>,
        ring: R,
        gs: &[CyclotomicGaloisGroupEl],
        gks: &[(CyclotomicGaloisGroupEl, KeySwitchKey<Params>)],
        key_switches: &RefCell<&mut usize>,
        _debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<PlainOrCiphertext<'a, Params, Self, R::Type>>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        match x.as_ciphertext(P, C_master, ring, self) {
            Ok((Cx, x)) => {
                assert!(x.dropped_rns_factor_indices.len() < C_master.base_ring().len());
                **key_switches.borrow_mut() += gs.len();
                
                let get_gk = |g| if let Some(res) = gks.iter().filter(|(provided_g, _)| C_master.galois_group().eq_el(g, *provided_g)).next() {
                    res
                } else {
                    panic!("Galois key for {} not found", C_master.galois_group().representative(g))
                };

                let gk_digits = get_gk(gs[0]).1.gadget_vector_digits();
                assert!(gs.iter().all(|g| get_gk(*g).1.gadget_vector_digits() == gk_digits), "when using `gal_many()`, all Galois keys must have the same digits");
                let (total_drop, special_modulus) = self.compute_optimal_special_modulus(P, C_master, &x.dropped_rns_factor_indices, 0, gk_digits);
                assert!(total_drop.len() < C_master.base_ring().len());

                let C_target = Params::mod_switch_down_C(&Cx, &total_drop.pushforward(&x.dropped_rns_factor_indices));
                let total_drop_without_special = total_drop.subtract(&special_modulus);
                let C_special = Params::mod_switch_down_C(&C_master, &total_drop_without_special);

                let gks_mod_switched = gs.iter().map(|g| Params::mod_switch_down_gk(&C_special, C_master, &total_drop_without_special, &get_gk(*g).1)).collect::<Vec<_>>();
        
                if LOG {
                    println!(
                        "Using a special modulus of {} RNS factors and a gadget vector of {} digits (largest has {} RNS factors) for Galois key switching", 
                        special_modulus.len(), 
                        gk_digits.remove_indices(&total_drop_without_special).len(),
                        gk_digits.remove_indices(&total_drop_without_special).iter().map(|digit| digit.end - digit.start).max().unwrap()
                    );
                }

                let result = if gs.len() == 1 {
                    vec![Params::hom_galois(
                        P, 
                        &C_target, 
                        &C_special, 
                        &total_drop.pushforward(&total_drop_without_special),
                        x.data, 
                        gs[0], 
                        gks_mod_switched.at(0)
                    )]
                } else {
                    Params::hom_galois_many(
                        P, 
                        &C_target, 
                        &C_special, 
                        &total_drop.pushforward(&total_drop_without_special),
                        x.data, 
                        gs, 
                        gks_mod_switched.as_fn()
                    )
                };
                result.into_iter().zip(gs.into_iter()).zip(gks_mod_switched.iter()).map(|((res, g), gk)| PlainOrCiphertext::Ciphertext(ModulusAwareCiphertext {
                    dropped_rns_factor_indices: total_drop.clone(),
                    info: self.noise_estimator.hom_galois(
                        &P, 
                        &C_target, 
                        &C_special, 
                        &total_drop.pushforward(&total_drop_without_special),
                        &x.info, 
                        *g, 
                        gk.gadget_vector_digits()
                    ),
                    data: res
                })).collect()
            },
            Err(Coefficient::Other(x)) => ring.get_ring().apply_galois_action_plain(P, &x, gs).into_iter().map(|x| PlainOrCiphertext::Plaintext(Coefficient::Other(x))).collect(),
            // integers are preserved under all galois automorphisms
            Err(x) => gs.iter().map(|_| PlainOrCiphertext::Plaintext(x.clone(ring))).collect()
        }
    }
}

impl<Params: BGVCiphertextParams, N: BGVNoiseEstimator<Params>, const LOG: bool> BGVModswitchStrategy<Params> for DefaultModswitchStrategy<Params, N, LOG> {

    type CiphertextInfo = N::NoiseDescriptor;

    #[instrument(skip_all)]
    fn evaluate_circuit<R>(
        &self,
        circuit: &PlaintextCircuit<R::Type>,
        ring: R,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        inputs: &[ModulusAwareCiphertext<Params, Self>],
        rk: Option<&RelinKey<Params>>,
        gks: &[(CyclotomicGaloisGroupEl, KeySwitchKey<Params>)],
        key_switches: &mut usize,
        mut debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<ModulusAwareCiphertext<Params, Self>>
        where R: RingStore,
            R::Type: AsBGVPlaintext<Params>
    {
        if !LOG {
            debug_sk = None;
        }
        let key_switches_refcell = std::cell::RefCell::new(key_switches);

        let result = circuit.evaluate_generic(
            &inputs.iter().map(PlainOrCiphertext::CiphertextRef).collect::<Vec<_>>(),
            DefaultCircuitEvaluator::new(
                |m| PlainOrCiphertext::PlaintextRef(m),
                |_, _, _| unreachable!(),
            ).with_mul( 
                |x, y| self.mul(P, C_master, x, y, &ring, rk, &key_switches_refcell, debug_sk),
            ).with_square(
                |x| self.square(P, C_master, x, &ring, rk, &key_switches_refcell, debug_sk),
            ).with_gal(
                |x, gs| self.gal_many(P, C_master, x, &ring, gs, gks, &key_switches_refcell, debug_sk)
            ).with_inner_product(
                |x, cs, ys| self.add_inner_prod(P, C_master, x, cs, ys, &ring, debug_sk)
            )
        );
        return result.into_iter().map(|res| match res {
            PlainOrCiphertext::Ciphertext(x) => x,
            PlainOrCiphertext::CiphertextRef(x) => {
                let Cx = Params::mod_switch_down_C(C_master, &x.dropped_rns_factor_indices);
                ModulusAwareCiphertext {
                    data: Params::clone_ct(&P, &Cx, &x.data),
                    dropped_rns_factor_indices: x.dropped_rns_factor_indices.clone(),
                    info: self.clone_info(&x.info)
                }
            },
            PlainOrCiphertext::Plaintext(x) => {
                let x = x.to_ring_el(&ring);
                let res_info = ring.get_ring().hom_add_to_noise(&self.noise_estimator, P, C_master, &RNSFactorIndexList::empty(), &x, &self.noise_estimator.transparent_zero(), &P.base_ring().one());
                let res_data = ring.get_ring().hom_add_to(P, C_master, &RNSFactorIndexList::empty(), &x, Params::transparent_zero(P, C_master));
                ModulusAwareCiphertext {
                    data: res_data,
                    dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                    info: res_info
                }
            },
            PlainOrCiphertext::PlaintextRef(x) => {
                let x = x.clone(&ring).to_ring_el(&ring);
                let res_info = ring.get_ring().hom_add_to_noise(&self.noise_estimator, P, C_master, &RNSFactorIndexList::empty(), &x, &self.noise_estimator.transparent_zero(), &P.base_ring().one());
                let res_data = ring.get_ring().hom_add_to(P, C_master, &RNSFactorIndexList::empty(), &x, Params::transparent_zero(P, C_master));
                ModulusAwareCiphertext {
                    data: res_data,
                    dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                    info: res_info
                }
            }
        }).collect();
    }

    fn info_for_fresh_encryption(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, hwt: Option<usize>) -> <Self as BGVModswitchStrategy<Params>>::CiphertextInfo {
        self.from_noise_level(self.noise_estimator.enc_sym_zero(P, C, hwt))
    }

    fn clone_info(&self, info: &Self::CiphertextInfo) -> Self::CiphertextInfo {
        self.noise_estimator.clone_critical_quantity_level(info)
    }

    fn print_info(&self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ct: &ModulusAwareCiphertext<Params, Self>) {
        let Clocal = Params::mod_switch_down_C(C_master, &ct.dropped_rns_factor_indices);
        println!("estimated noise: {}", self.noise_estimator.estimate_log2_relative_noise_level(P, &Clocal, &ct.info));
    }
}

#[cfg(test)]
use crate::bgv::noise_estimator::NaiveBGVNoiseEstimator;

#[test]
fn test_default_modswitch_strategy_mul() {
    let mut rng = thread_rng();

    let params = Pow2BGV {
        log2_q_min: 500,
        log2_q_max: 520,
        log2_N: 7,
        ciphertext_allocator: DefaultCiphertextAllocator::default(),
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };
    let t = 257;
    
    let P = params.create_plaintext_ring(t);
    let C = params.create_initial_ciphertext_ring();

    let sk = Pow2BGV::gen_sk(&C, &mut rng, None);
    let rk = Pow2BGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()));

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk);

    let modswitch_strategy: DefaultModswitchStrategy<Pow2BGV, _, true> = DefaultModswitchStrategy::new(NaiveBGVNoiseEstimator);
    let pow8_circuit = PlaintextCircuit::mul(ZZ)
        .compose(PlaintextCircuit::mul(ZZ).output_twice(ZZ), ZZ)
        .compose(PlaintextCircuit::mul(ZZ).output_twice(ZZ), ZZ)
        .compose(PlaintextCircuit::identity(1, ZZ).output_twice(ZZ), ZZ);

    let res = modswitch_strategy.evaluate_circuit(
        &pow8_circuit,
        ZZi64,
        &P,
        &C,
        &[ModulusAwareCiphertext {
            dropped_rns_factor_indices: RNSFactorIndexList::empty(),
            info: modswitch_strategy.info_for_fresh_encryption(&P, &C, None),
            data: ctxt
        }],
        Some(&rk),
        &[],
        &mut 0,
        Some(&sk)
    ).into_iter().next().unwrap();

    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_down_sk(&res_C, &C, &res.dropped_rns_factor_indices, &sk);

    let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res.data, &res_sk);
    println!("Actual output noise budget is {}", res_noise);
    assert_el_eq!(&P, &P.neg_one(), Pow2BGV::dec(&P, &res_C, res.data, &res_sk));
}

#[test]
fn test_never_modswitch_strategy() {
    let mut rng = thread_rng();

    let params = Pow2BGV {
        log2_q_min: 500,
        log2_q_max: 520,
        log2_N: 7,
        ciphertext_allocator: DefaultCiphertextAllocator::default(),
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };
    let t = 257;
    
    let P = params.create_plaintext_ring(t);
    let C = params.create_initial_ciphertext_ring();

    let sk = Pow2BGV::gen_sk(&C, &mut rng, None);
    let rk = Pow2BGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()));

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk);

    {
        let modswitch_strategy = DefaultModswitchStrategy::never_modswitch();
        let pow4_circuit = PlaintextCircuit::mul(ZZ)
            .compose(PlaintextCircuit::square(ZZ).output_twice(ZZ), ZZ);

        let res = modswitch_strategy.evaluate_circuit(
            &pow4_circuit,
            ZZi64,
            &P,
            &C,
            &[ModulusAwareCiphertext {
                dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                info: modswitch_strategy.info_for_fresh_encryption(&P, &C, None),
                data: Pow2BGV::clone_ct(&P, &C, &ctxt)
            }],
            Some(&rk),
            &[],
            &mut 0,
            None
        ).into_iter().next().unwrap();

        let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
        let res_sk = Pow2BGV::mod_switch_down_sk(&res_C, &C, &res.dropped_rns_factor_indices, &sk);

        let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res.data, &res_sk);
        println!("Actual output noise budget is {}", res_noise);
        assert_el_eq!(&P, &P.int_hom().map(16), Pow2BGV::dec(&P, &res_C, res.data, &res_sk));
    }
    {
        let modswitch_strategy = DefaultModswitchStrategy::never_modswitch();
        let pow8_circuit = PlaintextCircuit::mul(ZZ)
            .compose(PlaintextCircuit::mul(ZZ).output_twice(ZZ), ZZ)
            .compose(PlaintextCircuit::mul(ZZ).output_twice(ZZ), ZZ)
            .compose(PlaintextCircuit::identity(1, ZZ).output_twice(ZZ), ZZ);

        let res = modswitch_strategy.evaluate_circuit(
            &pow8_circuit,
            ZZi64,
            &P,
            &C,
            &[ModulusAwareCiphertext {
                dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                info: modswitch_strategy.info_for_fresh_encryption(&P, &C, None),
                data: Pow2BGV::clone_ct(&P, &C, &ctxt)
            }],
            Some(&rk),
            &[],
            &mut 0,
            None
        ).into_iter().next().unwrap();

        let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
        let res_sk = Pow2BGV::mod_switch_down_sk(&res_C, &C, &res.dropped_rns_factor_indices, &sk);

        let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res.data, &res_sk);
        assert_eq!(0, res_noise);
    }
}

#[test]
fn test_level_digits() {
    let a = [2, 2, 6, 6];
    let b = [2, 2, 3, 3];
    let k = 2;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    println!("{:?}, {:?}", c, d);
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 3);
    
    let a = [3, 3, 3, 3];
    let b = [3, 3, 3, 3];
    let k = 3;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    println!("{:?}, {:?}", c, d);
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 4);
    
    let a = [3, 3, 3, 3];
    let b = [3, 3, 3, 3];
    let k = 4;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    println!("{:?}, {:?}", c, d);
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 4);

    let a = [2, 4, 4, 4];
    let b = [2, 2, 2, 2];
    let k = 1;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    println!("{:?}, {:?}", c, d);
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
    println!("{:?}, {:?}", c, d);
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 4);
    
    let a = [3, 4, 5, 5];
    let b = [1, 2, 3, 4];
    let k = 1;
    let (c, d) = level_digits(&a, &b, k).unwrap();
    println!("{:?}, {:?}", c, d);
    assert!((0..4).all(|i| c[i] <= b[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= a[i]));
    assert!((0..4).all(|i| b[i] - c[i] + d[i] <= d.iter().copied().sum()));
    assert!((0..4).filter(|i| b[*i] - c[*i] + d[*i] != 0).count() <= 3);
}