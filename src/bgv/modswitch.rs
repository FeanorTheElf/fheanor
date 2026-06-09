use core::f64;
use std::cmp::min;
use std::ops::Range;

use feanor_math::algorithms::convolution::ConvolutionAlgorithm;
use feanor_math::homomorphism::CanHomFrom;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::BigIntRingBase;
use feanor_math::primitive_int::*;
use feanor_math::group::*;
use feanor_math::ring::*;
use feanor_math::algorithms::matmul::ComputeInnerProduct;

use crate::bgv::noise_estimator::*;
use crate::boo::Boo;
use crate::circuit::evaluator::CircuitEvaluator;
use crate::circuit::*;
use crate::number_ring::galois::*;
use crate::gadget_product::digits::*;
use crate::number_ring::galois::CyclotomicGaloisGroupOps;
use crate::ZZi64;

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
/// A [`Ciphertext`] which additionally stores w.r.t. which ciphertext modulus it is defined,
/// and which noise level (as measured by some [`BGVModswitchStrategy`]) it is estimated to have.
///
pub struct ModulusAwareCiphertext<Params: BGVInstantiation, Strategy: ?Sized + BGVModswitchStrategy<Params>> {
    /// The stored raw ciphertext
    pub data: Ciphertext<Params>,
    /// The indices of those RNS components w.r.t. a "master RNS base" (specified by the context)
    /// that are not used for this ciphertext; in other words, the ciphertext modulus of this ciphertext
    /// is the product of all RNS factors of the master RNS base that are not mentioned in this list
    pub dropped_rns_factor_indices: Box<RNSFactorIndexList>,
    /// Additional information required by the modulus-switching strategy
    pub info: Strategy::CiphertextInfo,
    /// Information about the secret key w.r.t. which this ciphertext is encrypted
    pub sk: SecretKeyDistribution
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
    fn info_for_fresh_encryption(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> Self::CiphertextInfo;

    fn clone_info(&self, info: &Self::CiphertextInfo) -> Self::CiphertextInfo;

    fn print_info(&self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ct: &ModulusAwareCiphertext<Params, Self>);

    fn clone_ct(&self, P: &PlaintextRing<Params>, C_master: &CiphertextRing<Params>, ct: &ModulusAwareCiphertext<Params, Self>) -> ModulusAwareCiphertext<Params, Self> {
        let C = Params::mod_switch_down_C(C_master, &ct.dropped_rns_factor_indices);
        ModulusAwareCiphertext {
            data: Params::clone_ct(P, &C, &ct.data),
            info: self.clone_info(&ct.info),
            dropped_rns_factor_indices: ct.dropped_rns_factor_indices.clone(),
            sk: ct.sk
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
/// When implementing this trait, you usually shouldn't have
/// nontrivial logic in the functions, but just delegate to the
/// appropriate functions of [`BGVInstantiation`] or [`BGVNoiseEstimator`].
/// 
pub trait AsBGVPlaintext<Params: BGVInstantiation>: RingBase + CanHomFrom<BigIntRingBase> {

    ///
    /// Computes a plaintext-ciphertext addition.
    /// 
    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params>;

    ///
    /// Estimates the noise caused by the plaintext-ciphertext addition.
    /// 
    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor;

    ///
    /// Computes a plaintext-ciphertext multiplication.
    /// 
    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params>;
    
    ///
    /// Estimates the noise caused by the given plaintext-ciphertext multiplication.
    /// 
    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor;

    ///
    /// Computes the inner product of the given vector of ciphertexts with the
    /// given vector of plaintexts.
    /// 
    /// All ciphertexts must have the same implicit scale. Implementors
    /// should not check this however, as calling this function with outdated implicit
    /// scales can sometimes avoid cloning.
    /// 
    fn hom_inner_product<I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (Self::Element, Ciphertext<Params>)>
    {
        data.fold(Params::transparent_zero(P, C), |current, (lhs, mut rhs)| {
            rhs.implicit_scale = P.base_ring().one();
            Params::hom_add(P, C, current, self.hom_mul_to(P, C, dropped_factors, &lhs, rhs))
        })
    }

    ///
    /// Computes the inner product of the given vector of ciphertexts with the
    /// given vector of plaintexts.
    /// 
    /// All ciphertexts are assumed to have the same implicit scale. Implementors
    /// should not check this however, as calling this function with outdated implicit
    /// scales can sometimes avoid cloning.
    /// 
    fn hom_inner_product_ref<'a, I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (&'a Self::Element, &'a Ciphertext<Params>)>,
            Params: 'a,
            Self: 'a
    {
        self.hom_inner_product(P, C, dropped_factors, data.map(|(lhs, rhs)| (self.clone_el(lhs), Params::clone_ct(P, C, rhs))))
    }

    ///
    /// Estimates the noise caused by the plaintext-ciphertext inner product.
    /// 
    /// All ciphertexts must have the same implicit scale.
    /// 
    fn hom_inner_product_noise<'a, 'b, N: BGVNoiseEstimator<Params>, I>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> N::CiphertextDescriptor
        where I: Iterator<Item = (&'a Self::Element, &'b N::CiphertextDescriptor)>,
        Self: 'a,
        N::CiphertextDescriptor: 'b
    {
        data.fold(estimator.transparent_zero(), |current, (lhs, rhs)| estimator.hom_add(
            P, 
            C, 
            &current, 
            &P.base_ring().one(), 
            &self.hom_mul_to_noise(estimator, P, C, dropped_factors, lhs, &rhs, &P.base_ring().one()), 
            &P.base_ring().one()
        ))
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

impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for StaticRingBase<i64> {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain_encoded(P, C, &C.inclusion().compose(C.base_ring().can_hom(&ZZi64).unwrap()).map(*m), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_add_plain_encoded(P, C, &C.inclusion().compose(C.base_ring().can_hom(&ZZi64).unwrap()).map(*m), ct_info, implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain_scalar(P, C, &P.base_ring().coerce(&ZZi64, *m), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_mul_plain_int(P, C, &int_cast(*m, ZZbig, ZZi64), ct_info, implicit_scale)
    }

    #[instrument(skip_all)]
    fn hom_inner_product_ref<'a, I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (&'a Self::Element, &'a Ciphertext<Params>)>,
            Params: 'a,
            Self: 'a
    {
        let h = C.inclusion().compose(C.base_ring().can_hom(&ZZi64).unwrap());
        let mut c0 = C.zero();
        let mut c1 = C.zero();
        for (l, r) in data {
            c0 = h.fma_map(&r.c0, l, c0);
            c1 = h.fma_map(&r.c1, l, c1);
        }
        return Ciphertext {
            implicit_scale: P.base_ring().one(),
            c0: c0,
            c1: c1
        }
    }
}

impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for ZnBase {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>,
        _dropped_factors: &RNSFactorIndexList,
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        assert_eq!(int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZi64, P.base_ring().integer_ring()), *self.modulus());
        Params::hom_add_plain(P, C, &P.inclusion().compose(P.base_ring().can_hom(&ZZi64).unwrap()).map(self.smallest_lift(*m)), ct)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>,
        _dropped_factors: &RNSFactorIndexList,
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        assert_eq!(int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZi64, P.base_ring().integer_ring()), *self.modulus());
        Params::hom_mul_plain_scalar(P, C, &P.base_ring().can_hom(&ZZi64).unwrap().map(self.smallest_lift(*m)), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        assert_eq!(int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZi64, P.base_ring().integer_ring()), *self.modulus());
        estimator.hom_add_plain_encoded(P, C, &C.inclusion().compose(C.base_ring().can_hom(&ZZi64).unwrap()).map(self.smallest_lift(*m)), ct_info, implicit_scale)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        assert_eq!(int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZi64, P.base_ring().integer_ring()), *self.modulus());
        estimator.hom_mul_plain_int(P, C, &int_cast(self.smallest_lift(*m), ZZbig, ZZi64), ct_info, implicit_scale)
    }
}

impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for BigIntRingBase {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain_encoded(P, C, &C.inclusion().compose(C.base_ring().can_hom(&ZZbig).unwrap()).map_ref(m), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_add_plain_encoded(P, C, &C.inclusion().compose(C.base_ring().can_hom(&ZZbig).unwrap()).map_ref(m), ct_info, implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain_scalar(P, C, &P.base_ring().coerce(&ZZbig, ZZbig.clone_el(m)), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_mul_plain_int(P, C, m, ct_info, implicit_scale)
    }

    #[instrument(skip_all)]
    fn hom_inner_product_ref<'a, I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        _dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (&'a Self::Element, &'a Ciphertext<Params>)>,
            Params: 'a,
            Self: 'a
    {
        let h = C.inclusion().compose(C.base_ring().can_hom(&ZZbig).unwrap());
        let mut c0 = C.zero();
        let mut c1 = C.zero();
        for (l, r) in data {
            c0 = h.fma_map(&r.c0, l, c0);
            c1 = h.fma_map(&r.c1, l, c1);
        }
        return Ciphertext {
            implicit_scale: P.base_ring().one(),
            c0: c0,
            c1: c1
        }
    }
}

impl<Params> AsBGVPlaintext<Params> for NumberRingQuotientByIntBase<NumberRing<Params>, Zn>
    where Params: BGVInstantiation<PlaintextRing = NumberRingQuotientByIntBase<NumberRing<Params>, Zn>>
{
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
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_add_plain(P, C, m, ct_info, implicit_scale)
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
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_mul_plain(P, C, m, ct_info, implicit_scale)
    }
}

impl<Params: BGVInstantiation, A: Allocator + Clone> AsBGVPlaintext<Params> for ManagedDoubleRNSRingBase<NumberRing<Params>, A>
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
        Params::hom_add_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_add_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct_info, implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_mul_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct_info, implicit_scale)
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
        for (l, r) in data {
            lhs.push(C.get_ring().drop_rns_factor_element(self, dropped_factors, &l));
            rhs_c0.push(r.c0);
            rhs_c1.push(r.c1);
        }
        return Ciphertext {
            implicit_scale: P.base_ring().one(),
            c0: <_ as ComputeInnerProduct>::inner_product_ref_fst(C.get_ring(), lhs.iter().zip(rhs_c0.into_iter())),
            c1: <_ as ComputeInnerProduct>::inner_product(C.get_ring(), lhs.into_iter().zip(rhs_c1.into_iter())),
        };
    }

    #[instrument(skip_all)]
    fn hom_inner_product_ref<'a, I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (&'a Self::Element, &'a Ciphertext<Params>)>,
            Params: 'a,
            Self: 'a
    {
        let mut lhs = Vec::new();
        let mut rhs_c0 = Vec::new();
        let mut rhs_c1 = Vec::new();
        for (l, r) in data {
            lhs.push(C.get_ring().drop_rns_factor_element(self, dropped_factors, l));
            rhs_c0.push(&r.c0);
            rhs_c1.push(&r.c1);
        }
        return Ciphertext {
            implicit_scale: P.base_ring().one(),
            c0: <_ as ComputeInnerProduct>::inner_product_ref(C.get_ring(), rhs_c0.into_iter().zip(lhs.iter())),
            c1: <_ as ComputeInnerProduct>::inner_product_ref_fst(C.get_ring(), rhs_c1.into_iter().zip(lhs.into_iter())),
        };
    }
}

impl<Params: BGVInstantiation, A: Allocator + Clone> AsBGVPlaintext<Params> for DoubleRNSRingBase<NumberRing<Params>, A>
    where CiphertextRing<Params>: RingStore<Type = DoubleRNSRingBase<NumberRing<Params>, A>>
{
    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_add_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct_info, implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_mul_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct_info, implicit_scale)
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
                first_implicit_scale = Some(P.base_ring().clone_el(&r.implicit_scale));
            } else {
                assert!(P.base_ring().eq_el(first_implicit_scale.as_ref().unwrap(), &r.implicit_scale));
            }
            lhs.push(C.get_ring().drop_rns_factor_element(self, dropped_factors, &l));
            rhs_c0.push(r.c0);
            rhs_c1.push(r.c1);
        }
        return Ciphertext {
            implicit_scale: first_implicit_scale.unwrap_or(P.base_ring().one()),
            c0: <_ as ComputeInnerProduct>::inner_product_ref_fst(C.get_ring(), lhs.iter().zip(rhs_c0.into_iter())),
            c1: <_ as ComputeInnerProduct>::inner_product(C.get_ring(), lhs.into_iter().zip(rhs_c1.into_iter())),
        };
    }

    #[instrument(skip_all)]
    fn hom_inner_product_ref<'a, I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (&'a Self::Element, &'a Ciphertext<Params>)>,
            Params: 'a,
            Self: 'a
    {
        let mut lhs = Vec::new();
        let mut rhs_c0 = Vec::new();
        let mut rhs_c1 = Vec::new();
        for (l, r) in data {
            lhs.push(C.get_ring().drop_rns_factor_element(self, dropped_factors, l));
            rhs_c0.push(&r.c0);
            rhs_c1.push(&r.c1);
        }
        return Ciphertext {
            implicit_scale: P.base_ring().one(),
            c0: <_ as ComputeInnerProduct>::inner_product_ref(C.get_ring(), rhs_c0.into_iter().zip(lhs.iter())),
            c1: <_ as ComputeInnerProduct>::inner_product_ref_fst(C.get_ring(), rhs_c1.into_iter().zip(lhs.into_iter())),
        };
    }
}

impl<Params: BGVInstantiation, A: Allocator + Clone, C: ConvolutionAlgorithm<ZnBase>> AsBGVPlaintext<Params> for SingleRNSRingBase<NumberRing<Params>, A, C>
    where CiphertextRing<Params>: RingStore<Type = SingleRNSRingBase<NumberRing<Params>, A, C>>
{
    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_add_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct_info, implicit_scale)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self, 
        estimator: &N, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        m: &Self::Element, 
        ct_info: &N::CiphertextDescriptor, 
        implicit_scale: &El<PlaintextZnRing<Params>>
    ) -> N::CiphertextDescriptor {
        estimator.hom_mul_plain_encoded(P, C, &C.get_ring().drop_rns_factor_element(self, dropped_factors, m), ct_info, implicit_scale)
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
                first_implicit_scale = Some(P.base_ring().clone_el(&r.implicit_scale));
            } else {
                assert!(P.base_ring().eq_el(first_implicit_scale.as_ref().unwrap(), &r.implicit_scale));
            }
            lhs.push(C.get_ring().drop_rns_factor_element(self, dropped_factors, &l));
            rhs_c0.push(r.c0);
            rhs_c1.push(r.c1);
        }
        return Ciphertext {
            implicit_scale: first_implicit_scale.unwrap_or(P.base_ring().one()),
            c0: <_ as ComputeInnerProduct>::inner_product_ref_fst(C.get_ring(), lhs.iter().zip(rhs_c0.into_iter())),
            c1: <_ as ComputeInnerProduct>::inner_product(C.get_ring(), lhs.into_iter().zip(rhs_c1.into_iter())),
        };
    }

    #[instrument(skip_all)]
    fn hom_inner_product_ref<'a, I>(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dropped_factors: &RNSFactorIndexList, 
        data: I
    ) -> Ciphertext<Params>
        where I: Iterator<Item = (&'a Self::Element, &'a Ciphertext<Params>)>,
            Params: 'a,
            Self: 'a
    {
        let mut lhs = Vec::new();
        let mut rhs_c0 = Vec::new();
        let mut rhs_c1 = Vec::new();
        for (l, r) in data {
            lhs.push(C.get_ring().drop_rns_factor_element(self, dropped_factors, l));
            rhs_c0.push(&r.c0);
            rhs_c1.push(&r.c1);
        }
        return Ciphertext {
            implicit_scale: P.base_ring().one(),
            c0: <_ as ComputeInnerProduct>::inner_product_ref(C.get_ring(), rhs_c0.into_iter().zip(lhs.iter())),
            c1: <_ as ComputeInnerProduct>::inner_product_ref_fst(C.get_ring(), rhs_c1.into_iter().zip(lhs.into_iter())),
        };
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

impl<Params: BGVInstantiation, N: BGVNoiseEstimator<Params>, const LOG: bool> DefaultModswitchStrategy<Params, N, LOG> {

    pub fn new(noise_estimator: N) -> Self {
        Self {
            params: PhantomData,
            noise_estimator: noise_estimator
        }
    }

    pub fn from_noise_level(&self, noise_level: N::CiphertextDescriptor) -> <Self as BGVModswitchStrategy<Params>>::CiphertextInfo {
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
        let used_sk = x.sk;
        let Cx = Params::mod_switch_down_C(C_master, &x.dropped_rns_factor_indices);
        let drop_x = dropped_factors_target.pushforward(&x.dropped_rns_factor_indices);
        if drop_x.len() == 0 {
            return x;
        }
        let x_noise_budget = if let Some(sk) = debug_sk {
            let sk_x = Params::mod_switch_sk(&Cx, C_master, sk);
            Some(Params::noise_budget(P, &Cx, &x.data, &sk_x))
        } else { None };
        let result = ModulusAwareCiphertext {
            data: Params::mod_switch_ct(P, &C_target, &Cx, x.data),
            info: self.noise_estimator.mod_switch_down_ct(&P, &C_target, &Cx, &drop_x, &x.info),
            dropped_rns_factor_indices: dropped_factors_target.to_owned(),
            sk: used_sk
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
                let sk_target = Params::mod_switch_sk(C_target, C_master, sk);
                println!("  actual noise budget: {} -> {}", x_noise_budget.unwrap(), Params::noise_budget(P, C_target, &result.data, &sk_target));
            }
        }
        return result;
    }

    ///
    /// Mod-switches the given ciphertext from its current ciphertext ring
    /// to `C_target`, and adjusts the noise information.
    /// 
    fn mod_switch_down_ref<'a>(
        &self, 
        P: &PlaintextRing<Params>, 
        C_target: &CiphertextRing<Params>, 
        C_master: &CiphertextRing<Params>, 
        dropped_factors_target: &RNSFactorIndexList, 
        x: &'a ModulusAwareCiphertext<Params, Self>,
        context: &str,
        debug_sk: Option<&SecretKey<Params>>
    ) -> Boo<'a, ModulusAwareCiphertext<Params, Self>> {
        let used_sk = x.sk;
        let Cx = Params::mod_switch_down_C(C_master, &x.dropped_rns_factor_indices);
        let drop_x = dropped_factors_target.pushforward(&x.dropped_rns_factor_indices);
        if drop_x.len() == 0 {
            return Boo::Borrowed(x);
        }
        let result = ModulusAwareCiphertext {
            data: Params::mod_switch_ct(P, &C_target, &Cx, Params::clone_ct(P, &Cx, &x.data)),
            info: self.noise_estimator.mod_switch_down_ct(&P, &C_target, &Cx, &drop_x, &x.info),
            dropped_rns_factor_indices: dropped_factors_target.to_owned(),
            sk: used_sk
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
                let sk_target = Params::mod_switch_sk(C_target, C_master, sk);
                let sk_x = Params::mod_switch_sk(&Cx, C_master, sk);
                println!("  actual noise budget: {} -> {}", Params::noise_budget(P, &Cx, &x.data, &sk_x), Params::noise_budget(P, C_target, &result.data, &sk_target));
            }
        }
        return Boo::Owned(result);
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
        noise_x: &N::CiphertextDescriptor,
        dropped_factors_x: &RNSFactorIndexList,
        noise_y: &N::CiphertextDescriptor,
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
                    &total_drop.pushforward(&total_drop_without_special),
                    &self.noise_estimator.mod_switch_down_ct(&P, &C_target, &Cx, &total_drop.pushforward(dropped_factors_x), noise_x),
                    &self.noise_estimator.mod_switch_down_ct(&P, &C_target, &Cy, &total_drop.pushforward(dropped_factors_y), noise_y),
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
    fn inner_prod<'a, R>(
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

        // first, we separate the inner product into three parts:
        //  - the constant part, which does not contain any ciphertexts and is immediately computed
        //  - the integer part, which is of the form `sum_i c[i] * ct[i]` with `c[i]` being integers
        //  - the main part, which is of the form `sum_i c[i] * ct[i]` with `c[i]` being elements of `R`
        let mut int_products: Vec<(i32, &ModulusAwareCiphertext<Params, Self>)> = Vec::new();
        let mut main_products:  Vec<(&El<R>, &ModulusAwareCiphertext<Params, Self>)> = Vec::new();

        // while separating the different summands, we also keep track of which will be the result modulus
        let mut total_drop = RNSFactorIndexList::empty();
        let mut min_dropped_len = usize::MAX;
        let mut update_total_drop = |ct: &ModulusAwareCiphertext<Params, Self>| {
            total_drop = total_drop.union(&ct.dropped_rns_factor_indices);
            min_dropped_len = min(min_dropped_len, ct.dropped_rns_factor_indices.len());
        };
        let mut used_sk = SecretKeyDistribution::Zero;

        for (lhs, rhs) in coeffs.iter().copied().zip(ys.iter().copied()).into_iter() {
            if !lhs.is_zero() {
                update_total_drop(rhs);
                used_sk = assert_sk_distr_match(used_sk, rhs.sk);
                match lhs {
                    Coefficient::Zero => unreachable!(),
                    Coefficient::One => int_products.push((1, rhs)),
                    Coefficient::NegOne => int_products.push((-1, rhs)),
                    Coefficient::Integer(c) => int_products.push((*c, rhs)),
                    Coefficient::Other(c) => main_products.push((c, rhs)),
                }
            }
        }
        if int_products.len() == 0 && main_products.len() == 0 {
            // everything is just zero
            return ModulusAwareCiphertext { data: Params::transparent_zero(P, C_master), dropped_rns_factor_indices: RNSFactorIndexList::empty(), info: self.noise_estimator.transparent_zero(), sk: SecretKeyDistribution::Zero };
        }
        assert!(min_dropped_len <= total_drop.len());

        let C_target = Params::mod_switch_down_C(C_master, &total_drop);

        // now perform modulus-switches when necessary
        let int_products: Vec<(i32, Boo<ModulusAwareCiphertext<Params, Self>>)> = int_products.iter().map(|(lhs, rhs)| (
            *lhs,
            self.mod_switch_down_ref(P, &C_target, C_master, &total_drop, rhs, "HomInnerProduct", debug_sk)
        )).collect();

        let main_products: Vec<(&El<R>, Boo<ModulusAwareCiphertext<Params, Self>>)> = main_products.iter().map(|(lhs, rhs)| (
            *lhs,
            self.mod_switch_down_ref(P, &C_target, C_master, &total_drop, rhs, "HomInnerProduct", debug_sk)
        )).collect();

        // finally, we do another noise optimization technique: the implicit scale of the output is
        // chosen as total scale (implicit scale & coefficient) of the highest-noise ciphertext; this way
        // we avoid multiplying its size up further
        let Zt = P.base_ring();
        let ZZ: &_ = Zt.integer_ring();
        let output_implicit_scale = int_products.iter().filter_map(|(c, ct)| Zt.invert(&Zt.int_hom().map(*c)).map(|c| (c, ct)))
            .map(|(c, ct)| (self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &ct.info), Zt.mul_ref_fst(&ct.data.implicit_scale, c))
        ).max_by(|(l, _), (r, _)| f64::total_cmp(l, r)).map(|(_, scale)| scale).unwrap_or(P.base_ring().one());

        let int_products: Vec<(El<BigIntRing>, Boo<ModulusAwareCiphertext<Params, Self>>)> = int_products.into_iter().map(|(lhs, rhs)| {
            let lhs = int_cast(Zt.smallest_lift(Zt.mul(Zt.int_hom().map(lhs), Zt.checked_div(&output_implicit_scale, &rhs.data.implicit_scale).unwrap())), ZZbig, ZZ);
            return (lhs, rhs);
        }).collect();

        let ZZbig_to_ring = ring.can_hom(&ZZbig).unwrap();
        let main_products: Vec<(Boo<El<R>>, Boo<ModulusAwareCiphertext<Params, Self>>)> = main_products.into_iter().map(|(lhs, rhs)| {
            let factor = Zt.smallest_lift(Zt.checked_div(&output_implicit_scale, &rhs.data.implicit_scale).unwrap());
            if !ZZ.is_one(&factor) {
                let mut lhs = ring.clone_el(lhs);
                ZZbig_to_ring.mul_assign_map(&mut lhs, int_cast(factor, ZZbig, ZZ));
                return (Boo::Owned(lhs), rhs);
            } else {
                return (Boo::Borrowed(lhs), rhs);
            }
        }).collect();

        let int_product_noise = ZZbig.get_ring().hom_inner_product_noise(&self.noise_estimator, P, &C_target, &total_drop, int_products.iter().map(|(lhs, rhs)| (lhs, &rhs.info)));
        let mut int_product_part = ZZbig.get_ring().hom_inner_product_ref(P, &C_target, &total_drop, int_products.iter().map(|(lhs, rhs)| (lhs, &rhs.data)));
        int_product_part.implicit_scale = P.base_ring().clone_el(&output_implicit_scale);

        let main_product_noise = ring.get_ring().hom_inner_product_noise(&self.noise_estimator, P, &C_target, &total_drop, main_products.iter().map(|(lhs, rhs)| (&**lhs, &rhs.info)));
        let mut main_product_part = ring.get_ring().hom_inner_product_ref(P, &C_target, &total_drop, main_products.iter().map(|(lhs, rhs)| (&**lhs, &rhs.data)));
        main_product_part.implicit_scale = P.base_ring().clone_el(&output_implicit_scale);

        // ignore the last plaintext addition for noise analysis, it's gonna be fine
        let product_info = self.noise_estimator.hom_add(P, &C_target, &int_product_noise, &P.base_ring().one(), &main_product_noise, &P.base_ring().one());
        let product_data = Params::hom_add(P, &C_target, int_product_part, main_product_part);
        return ModulusAwareCiphertext {
            data: product_data,
            info: product_info,
            dropped_rns_factor_indices: total_drop,
            sk: used_sk
        };
    }

    #[instrument(skip_all)]
    fn mul<'a, R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: ModulusAwareCiphertext<Params, Self>,
        y: ModulusAwareCiphertext<Params, Self>,
        _ring: R,
        rk: Option<&RelinKey<Params>>,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Self>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        let used_sk = assert_sk_distr_match(x.sk, y.sk);
        assert!(x.dropped_rns_factor_indices.len() < C_master.base_ring().len());
        assert!(y.dropped_rns_factor_indices.len() < C_master.base_ring().len());

        let rk = rk.unwrap();
        let (total_drop, special_modulus) = self.compute_optimal_mul_modswitch(P, C_master, &x.info, &x.dropped_rns_factor_indices, &y.info, &y.dropped_rns_factor_indices, rk.gadget_vector_digits(), used_sk);
        let total_drop_without_special = total_drop.subtract(&special_modulus);
        let C_special = Params::mod_switch_down_C(&C_master, &total_drop_without_special);
        let C_target = Params::mod_switch_down_C(C_master, &total_drop);
        let rk_modswitch = Params::mod_switch_down_rk(&C_special, C_master, &rk);
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
            &x_modswitched.data, 
            &y_modswitched.data, 
            &rk_modswitch
        );
        let res_info = self.noise_estimator.hom_mul(
            P, 
            &C_target, 
            &C_special, 
            &total_drop.pushforward(&total_drop_without_special),
            &x_modswitched.info, 
            &y_modswitched.info, 
            KeySwitchKeyDescriptor {
                digits: rk_modswitch.gadget_vector_digits(),
                new_sk: used_sk,
                sigma: 3.2
            }
        );
        if LOG {
            println!("HomMul: Result has estimated noise budget {}/{}",
                -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &res_info).round(),
                ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
            );
            if let Some(sk) = debug_sk {
                let sk_target = Params::mod_switch_sk(&C_target, C_master, sk);
                println!("  actual noise budget: {}", Params::noise_budget(P, &C_target, &res_data, &sk_target));
                Params::dec_println(P, &C_target, &res_data, &sk_target);
            }
        }
        return ModulusAwareCiphertext {
            dropped_rns_factor_indices: total_drop,
            info: res_info,
            data: res_data,
            sk: used_sk
        };
    }

    #[instrument(skip_all)]
    fn square<'a, R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: ModulusAwareCiphertext<Params, Self>,
        _ring: R,
        rk: Option<&RelinKey<Params>>,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Self>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        let used_sk = x.sk;
        assert!(x.dropped_rns_factor_indices.len() < C_master.base_ring().len());

        let rk = rk.unwrap();
        let (total_drop, special_modulus) = self.compute_optimal_mul_modswitch(P, C_master, &x.info, &x.dropped_rns_factor_indices, &x.info, &x.dropped_rns_factor_indices, rk.gadget_vector_digits(), used_sk);
        let total_drop_without_special = total_drop.subtract(&special_modulus);
        let C_special = Params::mod_switch_down_C(&C_master, &total_drop_without_special);
        let C_target = Params::mod_switch_down_C(C_master, &total_drop);
        let rk_modswitch = Params::mod_switch_down_rk(&C_special, C_master, &rk);
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
            KeySwitchKeyDescriptor {
                digits: rk_modswitch.gadget_vector_digits(),
                new_sk: used_sk,
                sigma: 3.2
            }
        );
        let res_data = Params::hom_square(
            P, 
            &C_target, 
            &C_special, 
            &x_modswitched.data, 
            &rk_modswitch
        );
        if LOG {
            println!("HomSquare: Result has estimated noise budget {}/{}",
                -self.noise_estimator.estimate_log2_relative_noise_level(P, &C_target, &res_info).round(),
                ZZbig.abs_log2_ceil(C_target.base_ring().modulus()).unwrap()
            );
            if let Some(sk) = debug_sk {
                let sk_target = Params::mod_switch_sk(&C_target, C_master, sk);
                println!("  actual noise budget: {}", Params::noise_budget(P, &C_target, &res_data, &sk_target));
                Params::dec_println(P, &C_target, &res_data, &sk_target);
            }
        }
        return ModulusAwareCiphertext {
            dropped_rns_factor_indices: total_drop,
            info: res_info,
            data: res_data,
            sk: used_sk
        };
    }

    #[instrument(skip_all)]
    fn gal_many<'a, R>(
        &self,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>,
        x: ModulusAwareCiphertext<Params, Self>,
        _ring: R,
        gs: &[GaloisGroupEl],
        gks: &[(GaloisGroupEl, KeySwitchKey<Params>)],
        _debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<ModulusAwareCiphertext<Params, Self>>
        where R: RingStore + Copy,
            R::Type: AsBGVPlaintext<Params>
    {
        let used_sk = x.sk;
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
        let result = if gs.len() == 1 {
            vec![Params::hom_galois(P, &C_target, &C_special, x.data, &gs[0], gks_mod_switched.at(0))]
        } else {
            Params::hom_galois_many(P, &C_target, &C_special, x.data, gs, gks_mod_switched.as_fn())
        };
        return result.into_iter().zip(gs.into_iter()).zip(gks_mod_switched.iter()).map(|((res, g), gk)| ModulusAwareCiphertext {
            dropped_rns_factor_indices: total_drop.clone(),
            info: self.noise_estimator.hom_galois(
                &P, 
                &C_target, 
                &C_special, 
                &total_drop.pushforward(&total_drop_without_special),
                &x.info, 
                g, 
                KeySwitchKeyDescriptor {
                    digits: gk.gadget_vector_digits(),
                    new_sk: used_sk,
                    sigma: 3.2
                }
            ),
            sk: used_sk,
            data: res
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
    where R: ?Sized + AsBGVPlaintext<Inst>, Inst: BGVInstantiation, N: BGVNoiseEstimator<Inst>
{
    fn supports_gal(&self) -> bool {
        self.gks.len() > 0
    }

    fn supports_mul(&self) -> bool {
        self.rk.is_some() && self.rk.is_some()
    }

    fn add_constant(&mut self, val: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, constant: &'b Coefficient<R>) -> ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>> {
        let ring = RingRef::new(self.ring);
        let current_C = Inst::mod_switch_down_C(self.C_master, &val.dropped_rns_factor_indices);
        let constant = constant.clone(ring).to_ring_el(ring);
        ModulusAwareCiphertext {
            info: self.ring.hom_add_to_noise(&self.strategy.noise_estimator, self.P, &current_C, &val.dropped_rns_factor_indices, &constant, &val.info, &val.data.implicit_scale),
            data: self.ring.hom_add_to(self.P, &current_C, &val.dropped_rns_factor_indices, &constant, val.data),
            dropped_rns_factor_indices: val.dropped_rns_factor_indices,
            sk: val.sk
        }
    }

    fn gal(&mut self, val: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, gs: &'b [GaloisGroupEl]) -> Vec<ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>> {
        self.strategy.gal_many(self.P, self.C_master, val, RingRef::new(self.ring), gs, self.gks, self.debug_sk)
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

    fn mul(&mut self, lhs: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>, rhs: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>) -> ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>> {
        self.strategy.mul(self.P, self.C_master, lhs, rhs, RingRef::new(self.ring), self.rk, self.debug_sk)
    }

    fn square(&mut self, val: ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>>) -> ModulusAwareCiphertext<Inst, DefaultModswitchStrategy<Inst, N, LOG>> {
        self.strategy.square(self.P, self.C_master, val, RingRef::new(self.ring), self.rk, self.debug_sk)
    }
}

impl<Params: BGVInstantiation, N: BGVNoiseEstimator<Params>, const LOG: bool> BGVModswitchStrategy<Params> for DefaultModswitchStrategy<Params, N, LOG> {

    type CiphertextInfo = N::CiphertextDescriptor;

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
        return result;
    }

    fn info_for_fresh_encryption(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> <Self as BGVModswitchStrategy<Params>>::CiphertextInfo {
        self.from_noise_level(self.noise_estimator.enc_sym_zero(P, C, sk))
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
        data: Pow2BGV::enc_sym(&P, &C, &mut rng, &x, &sk, 3.2),
        dropped_rns_factor_indices: RNSFactorIndexList::empty(),
        info: modswitch_strategy.info_for_fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
        sk: SecretKeyDistribution::UniformTernary
    }).collect::<Vec<_>>();

    let res = modswitch_strategy.inner_prod(&P, &C, &[
        &Coefficient::NegOne,
        &Coefficient::One,
        &Coefficient::Other(P.int_hom().map(17))
    ], &cts.iter().collect::<Vec<_>>(), &P, None);
    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);
    assert_el_eq!(&P, &P.int_hom().map(-2 + 100 - 17), Pow2BGV::dec(&P, &res_C, res.data, &res_sk));

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
    assert_el_eq!(&P, &P.int_hom().map(-2 + 100 - 17), Pow2BGV::dec(&P, &res_C, res.data, &res_sk));

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
    assert_el_eq!(&P, &P.int_hom().map(-2 + 100 - 17), Pow2BGV::dec(&P, &res_C, res.data, &res_sk));
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
    let pow8_circuit = PlaintextCircuit::mul(ZZi64)
        .compose(PlaintextCircuit::mul(ZZi64).output_twice(ZZi64), ZZi64)
        .compose(PlaintextCircuit::mul(ZZi64).output_twice(ZZi64), ZZi64)
        .compose(PlaintextCircuit::identity(1, ZZi64).output_twice(ZZi64), ZZi64);

    let input = P.int_hom().map(2);
    let ct = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk, 3.2);
    let res = modswitch_strategy.evaluate_circuit(
        &pow8_circuit,
        ZZi64,
        &P,
        &C,
        &[ModulusAwareCiphertext {
            dropped_rns_factor_indices: RNSFactorIndexList::empty(),
            info: modswitch_strategy.info_for_fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
            data: ct,
            sk: SecretKeyDistribution::UniformTernary
        }],
        Some(&rk),
        &[],
        Some(&sk)
    ).into_iter().next().unwrap();

    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);
    let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res.data, &res_sk);
    println!("Actual output noise budget is {}", res_noise);
    assert_el_eq!(&P, &P.neg_one(), Pow2BGV::dec(&P, &res_C, res.data, &res_sk));
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
        let pow4_circuit = PlaintextCircuit::mul(ZZi64)
            .compose(PlaintextCircuit::square(ZZi64).output_twice(ZZi64), ZZi64);

        let res = modswitch_strategy.evaluate_circuit(
            &pow4_circuit,
            ZZi64,
            &P,
            &C,
            &[ModulusAwareCiphertext {
                dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                info: modswitch_strategy.info_for_fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
                data: Pow2BGV::clone_ct(&P, &C, &ctxt),
                sk: SecretKeyDistribution::UniformTernary
            }],
            Some(&rk),
            &[],
            None
        ).into_iter().next().unwrap();

        let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
        let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);

        let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res.data, &res_sk);
        println!("Actual output noise budget is {}", res_noise);
        assert_el_eq!(&P, &P.int_hom().map(16), Pow2BGV::dec(&P, &res_C, res.data, &res_sk));
    }
    {
        let modswitch_strategy = DefaultModswitchStrategy::never_modswitch();
        let pow8_circuit = PlaintextCircuit::mul(ZZi64)
            .compose(PlaintextCircuit::mul(ZZi64).output_twice(ZZi64), ZZi64)
            .compose(PlaintextCircuit::mul(ZZi64).output_twice(ZZi64), ZZi64)
            .compose(PlaintextCircuit::identity(1, ZZi64).output_twice(ZZi64), ZZi64);

        let res = modswitch_strategy.evaluate_circuit(
            &pow8_circuit,
            ZZi64,
            &P,
            &C,
            &[ModulusAwareCiphertext {
                dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                info: modswitch_strategy.info_for_fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
                data: Pow2BGV::clone_ct(&P, &C, &ctxt),
                sk: SecretKeyDistribution::UniformTernary
            }],
            Some(&rk),
            &[],
            None
        ).into_iter().next().unwrap();

        let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
        let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);

        let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res.data, &res_sk);
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
    let circuit = poly_to_circuit(&ZpeX, &[centered_digit_retain_poly(&ZpeX, 3)]);

    let input = P.int_hom().map(17 * 17 + 2 * 17 - 3);
    let ct = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk, 3.2);
    let res = modswitch_strategy.evaluate_circuit(
        &circuit,
        P.base_ring(),
        &P,
        &C,
        &[ModulusAwareCiphertext {
            dropped_rns_factor_indices: RNSFactorIndexList::empty(),
            info: modswitch_strategy.info_for_fresh_encryption(&P, &C, SecretKeyDistribution::UniformTernary),
            data: Pow2BGV::clone_ct(&P, &C, &ct),
            sk: SecretKeyDistribution::UniformTernary
        }],
        Some(&rk),
        &[],
        Some(&sk)
    ).into_iter().next().unwrap();

    let res_C = Pow2BGV::mod_switch_down_C(&C, &res.dropped_rns_factor_indices);
    let res_sk = Pow2BGV::mod_switch_sk(&res_C, &C, &sk);
    let res_noise = Pow2BGV::noise_budget(&P, &res_C, &res.data, &res_sk);
    println!("Actual output noise budget is {}", res_noise);
    assert_el_eq!(&P, &circuit.evaluate(&[input], P.inclusion())[0], Pow2BGV::dec(&P, &res_C, res.data, &res_sk));
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