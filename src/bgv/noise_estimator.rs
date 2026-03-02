
use super::*;

///
/// Before we say what this is, let's state what the problem is that 
/// we want to solve:
/// Since our noise estimator is currently relatively bad, we might
/// actually underestimate the noise of a ciphertext by some amount.
/// For linear operations, this is not a problem, since this deviation
/// won't grow too much. However, homomorphic multiplications will basically
/// double the error every time: The multiplication result has critical
/// quantity about `lhs_cq * rhs_cq`, so if we estimate `log2(lhs_cq)`
/// resp. `log2(rhs_cq)` slightly wrong, the result will be estimated
/// about twice as wrong.
/// 
/// To counter this, we just increase the estimate of the log2-size of
/// the input critical quantities by this factor, which means we will
/// perform in general more modulus-switching, and the worst-case error
/// growth will be limited. Note that overestimating the actual error
/// is not really a problem.
/// 
/// This factor is chosen experimentally, and we hopefully won't need
/// it anymore once we get a better noise estimator.
/// 
const HEURISTIC_FACTOR_MUL_INPUT_NOISE: f64 = 1.2;

#[derive(Debug, Clone, Copy)]
pub struct KeySwitchKeyDescriptor<'a> {
    pub digits: &'a RNSGadgetVectorDigitIndices,
    pub sigma: f64,
    pub new_sk: SecretKeyDistribution
}

pub trait BGVNoiseEstimator<Params: BGVInstantiation> {

    ///
    /// An estimate of the size and distribution of the critical quantity
    /// `c0 + c1 s = m + t e`. The only requirement is that the noise estimator
    /// can derive an estimate about its infinity norm via
    /// [`BGVNoiseEstimator::estimate_log2_relative_noise_level`], but estimators are free
    /// to store additional data to get more precise estimates on the noise growth
    /// of operations.
    ///
    type CiphertextDescriptor;

    ///
    /// Should return an estimate of
    /// ```text
    ///   log2( | c0 + c1 * s |_inf / q )
    /// ```
    ///
    fn estimate_log2_relative_noise_level(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &Self::CiphertextDescriptor) -> f64;

    fn enc_sym_zero(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> Self::CiphertextDescriptor;

    fn transparent_zero(&self) -> Self::CiphertextDescriptor;

    fn hom_add_plain(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, ct: &Self::CiphertextDescriptor, implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor;

    fn hom_add_plain_encoded(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<CiphertextRing<Params>>, ct: &Self::CiphertextDescriptor, implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor;

    fn enc_sym(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, sk: SecretKeyDistribution) -> Self::CiphertextDescriptor {
        self.hom_add_plain(P, C, m, &self.enc_sym_zero(P, C, sk), &P.base_ring().one())
    }

    fn hom_mul_plain(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, ct: &Self::CiphertextDescriptor, implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor;

    fn hom_mul_plain_encoded(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<CiphertextRing<Params>>, ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor;

    fn hom_mul_plain_int(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<BigIntRing>, ct: &Self::CiphertextDescriptor, implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor;

    fn merge_implicit_scale(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &Self::CiphertextDescriptor, implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {
        self.hom_mul_plain_int(P, C, &int_cast(P.base_ring().smallest_lift(P.base_ring().invert(&implicit_scale).unwrap()), ZZbig, P.base_ring().integer_ring()), ct, implicit_scale)
    }

    fn key_switch(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, special_modulus_rns_factor_indices: &RNSFactorIndexList, ct: &Self::CiphertextDescriptor, key_switch_key: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor;

    fn hom_mul(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, special_modulus_rns_factor_indices: &RNSFactorIndexList, lhs: &Self::CiphertextDescriptor, rhs: &Self::CiphertextDescriptor, rk: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor;

    fn hom_add(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, lhs: &Self::CiphertextDescriptor, lhs_implicit_scale: &El<PlaintextZnRing<Params>>, rhs: &Self::CiphertextDescriptor, rhs_implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor;

    fn hom_galois(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, special_modulus_rns_factor_indices: &RNSFactorIndexList, ct: &Self::CiphertextDescriptor, _g: &GaloisGroupEl, gk: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor;

    fn mod_switch_down_ct(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, drop_moduli: &RNSFactorIndexList, ct: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor;

    fn change_plaintext_modulus(Pnew: &PlaintextRing<Params>, Pold: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor;

    fn clone_critical_quantity_level(&self, val: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor;
}

///
/// An estimate of `log2(|s|_can)` when `s` is sampled from `C`.
/// 
fn log2_can_norm_sk_estimate<Params: BGVInstantiation>(C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> f64 {
    match sk {
        SecretKeyDistribution::Custom(log2_can_norm) => log2_can_norm,
        SecretKeyDistribution::SparseWithHwt(hwt) => (hwt as f64).log2(),
        SecretKeyDistribution::UniformTernary => (C.rank() as f64).log2(),
        SecretKeyDistribution::Zero => -f64::INFINITY
    }
}

///
/// An estimate of `max_(x in P) log2( | shortest-lift(x) |_can )`.
/// 
fn log2_can_norm_shortest_lift_estimate<Params: BGVInstantiation>(P: &PlaintextRing<Params>) -> f64 {
    (P.rank() as f64).log2() + t_log2::<Params>(P)
}

fn t_log2<Params: BGVInstantiation>(P: &PlaintextRing<Params>) -> f64 {
    P.base_ring().integer_ring().to_float_approx(P.base_ring().modulus()).log2()
}

pub fn assert_sk_distr_match(lhs: SecretKeyDistribution, rhs: SecretKeyDistribution) -> SecretKeyDistribution {
    match (lhs, rhs) {
        (SecretKeyDistribution::Zero, rhs) => rhs,
        (lhs, SecretKeyDistribution::Zero) => lhs,
        (SecretKeyDistribution::Custom(lhs_can_norm), SecretKeyDistribution::Custom(rhs_can_norm)) => SecretKeyDistribution::Custom(f64::max(lhs_can_norm, rhs_can_norm)),
        (SecretKeyDistribution::Custom(_), _) => lhs,
        (_, SecretKeyDistribution::Custom(_)) => rhs,
        (SecretKeyDistribution::UniformTernary, SecretKeyDistribution::UniformTernary) => SecretKeyDistribution::UniformTernary,
        (SecretKeyDistribution::SparseWithHwt(lhs_hwt), SecretKeyDistribution::SparseWithHwt(rhs_hwt)) if lhs_hwt == rhs_hwt => SecretKeyDistribution::SparseWithHwt(lhs_hwt),
        _ => panic!("secret key mismatch")
    }
}

///
/// A [`BGVNoiseEstimator`] that uses some very simple formulas to estimate the noise
/// growth of BGV operations. This is WIP and very likely to be replaced later by
/// a better and more rigorous estimator.
///
pub struct NaiveBGVNoiseEstimator;

#[derive(Copy, Clone, Debug)]
pub struct NaiveBGVNoiseEstimatorNoiseDescriptor {
    /// We store `log2(| c0 + c1 s |_can / q)`; this is hopefully `< 0`
    log2_relative_critical_quantity: f64,
    sk: SecretKeyDistribution
}

impl<Params: BGVInstantiation> BGVNoiseEstimator<Params> for NaiveBGVNoiseEstimator {

    type CiphertextDescriptor = NaiveBGVNoiseEstimatorNoiseDescriptor;

    fn estimate_log2_relative_noise_level(&self, _P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, noise: &Self::CiphertextDescriptor) -> f64 {
        // we subtract `(C.rank() as f64).log2()`, since that should be about the difference between `l_inf` and canonical norm
        noise.log2_relative_critical_quantity - (C.rank() as f64).log2()
    }

    fn enc_sym_zero(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> Self::CiphertextDescriptor {
        let result = t_log2::<Params>(P) + log2_can_norm_sk_estimate::<Params>(C, sk) - BigIntRing::RING.abs_log2_floor(C.base_ring().modulus()).unwrap() as f64;
        assert!(!result.is_nan());
        return NaiveBGVNoiseEstimatorNoiseDescriptor {
            log2_relative_critical_quantity: result,
            sk
        };
    }

    fn hom_add(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, lhs: &Self::CiphertextDescriptor, lhs_implicit_scale: &El<PlaintextZnRing<Params>>, rhs: &Self::CiphertextDescriptor, rhs_implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {
        let Zt = P.base_ring();
        let ZZ = Zt.integer_ring();
        let (a, b) = equalize_implicit_scale(Zt, Zt.checked_div(&lhs_implicit_scale, &rhs_implicit_scale).unwrap());
        debug_assert!(!Zt.eq_el(&lhs_implicit_scale, &rhs_implicit_scale) || (ZZ.is_one(&a) && ZZ.is_one(&b)));
        debug_assert!(Zt.is_unit(&Zt.coerce(ZZ, ZZ.clone_el(&a))));
        debug_assert!(Zt.is_unit(&Zt.coerce(ZZ, ZZ.clone_el(&b))));
        let result = f64::max(
            ZZ.to_float_approx(&b).abs().log2() + lhs.log2_relative_critical_quantity, 
            ZZ.to_float_approx(&a).abs().log2() + rhs.log2_relative_critical_quantity
        );
        assert!(!result.is_nan());
        return NaiveBGVNoiseEstimatorNoiseDescriptor{
            log2_relative_critical_quantity: result,
            sk: assert_sk_distr_match(lhs.sk, rhs.sk)
        };
    }

    fn hom_add_plain(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<PlaintextRing<Params>>, ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {
        debug_assert!(!ct.log2_relative_critical_quantity.is_nan());
        return *ct;
    }

    fn hom_add_plain_encoded(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {
        debug_assert!(!ct.log2_relative_critical_quantity.is_nan());
        return *ct;
    }

    fn hom_mul_plain(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<PlaintextRing<Params>>, ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {
        let mut result = *ct;
        result.log2_relative_critical_quantity += log2_can_norm_shortest_lift_estimate::<Params>(P);
        assert!(!result.log2_relative_critical_quantity.is_nan());
        return result;
    }

    fn hom_mul_plain_encoded(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {
        let mut result = *ct;
        result.log2_relative_critical_quantity += log2_can_norm_shortest_lift_estimate::<Params>(P);
        assert!(!result.log2_relative_critical_quantity.is_nan());
        return result;
    }

    fn hom_mul_plain_int(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, m: &El<BigIntRing>, ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {
        let mut result = *ct;
        result.log2_relative_critical_quantity += ZZbig.abs_log2_ceil(m).unwrap_or(0) as f64;
        assert!(!result.log2_relative_critical_quantity.is_nan());
        return result;
    }

    fn transparent_zero(&self) -> Self::CiphertextDescriptor {
        let result = NaiveBGVNoiseEstimatorNoiseDescriptor {
            log2_relative_critical_quantity: -f64::INFINITY,
            sk: SecretKeyDistribution::Zero
        };
        debug_assert!(!result.log2_relative_critical_quantity.is_nan());
        return result;
    }

    fn mod_switch_down_ct(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, drop_moduli: &RNSFactorIndexList, ct: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor {
        assert_eq!(Cnew.base_ring().len() + drop_moduli.len(), Cold.base_ring().len());
        let result = f64::max(
            ct.log2_relative_critical_quantity,
            t_log2::<Params>(P) + log2_can_norm_sk_estimate::<Params>(Cnew, ct.sk) - BigIntRing::RING.abs_log2_ceil(Cnew.base_ring().modulus()).unwrap() as f64
        );
        assert!(!result.is_nan());
        return NaiveBGVNoiseEstimatorNoiseDescriptor {
            log2_relative_critical_quantity: result,
            sk: ct.sk
        };
    }

    fn hom_mul(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, special_modulus_rns_factor_indices: &RNSFactorIndexList, lhs: &Self::CiphertextDescriptor, rhs: &Self::CiphertextDescriptor, rk: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor {
        let log2_q = BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap() as f64;
        let intermediate_result = NaiveBGVNoiseEstimatorNoiseDescriptor {
            log2_relative_critical_quantity: (lhs.log2_relative_critical_quantity + rhs.log2_relative_critical_quantity + 2. * log2_q) * HEURISTIC_FACTOR_MUL_INPUT_NOISE - log2_q,
            sk: assert_sk_distr_match(lhs.sk, rhs.sk)
        };

        let result = <Self as BGVNoiseEstimator<Params>>::key_switch(
            self, 
            P, 
            C, 
            C_special, 
            special_modulus_rns_factor_indices, 
            &intermediate_result, 
            rk,
        );
        assert!(!result.log2_relative_critical_quantity.is_nan());
        return result;
    }

    fn key_switch(&self, _P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, special_modulus_rns_factor_indices: &RNSFactorIndexList, ct: &Self::CiphertextDescriptor, key_switch_key: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor {
        assert_eq!(C.base_ring().len() + special_modulus_rns_factor_indices.len(), C_special.base_ring().len());
        let log2_q = BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap() as f64;
        let log2_largest_digit = key_switch_key.digits.iter().map(|digit| digit.iter().map(|i| C_special.base_ring().at(i).integer_ring().abs_log2_ceil(C_special.base_ring().at(i).modulus()).unwrap() as f64).sum::<f64>()).max_by(f64::total_cmp).unwrap();
        let special_modulus_log2 = special_modulus_rns_factor_indices.iter().map(|i| C_special.base_ring().at(*i).integer_ring().abs_log2_ceil(C_special.base_ring().at(*i).modulus()).unwrap() as f64).sum::<f64>();
        let result = f64::max(
            ct.log2_relative_critical_quantity,
            log2_largest_digit - special_modulus_log2 + (C_special.rank() as f64).log2() * 2. - log2_q
        );
        assert!(!result.is_nan());
        return NaiveBGVNoiseEstimatorNoiseDescriptor {
            log2_relative_critical_quantity: result,
            sk: key_switch_key.new_sk
        };
    }

    fn hom_galois(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, special_modulus_rns_factor_indices: &RNSFactorIndexList, ct: &Self::CiphertextDescriptor, _g: &GaloisGroupEl, gk: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor {
        <Self as BGVNoiseEstimator<Params>>::key_switch(self, P, C, C_special, special_modulus_rns_factor_indices, &ct, gk)
    }

    fn change_plaintext_modulus(_Pnew: &PlaintextRing<Params>, _Pold: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, ct: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor {
        debug_assert!(!ct.log2_relative_critical_quantity.is_nan());
        return *ct;
    }

    fn clone_critical_quantity_level(&self, val: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor {
        *val
    }
}

///
/// Noise estimator that always returns 0 as estimated noise budget.
///
/// Its only use is probably to have a default value in places where a
/// noise estimator is required but never used, as well as to implement
/// [`super::modswitch::DefaultModswitchStrategy::never_modswitch()`].
///
pub struct AlwaysZeroNoiseEstimator;

impl<Params: BGVInstantiation> BGVNoiseEstimator<Params> for AlwaysZeroNoiseEstimator {

    type CiphertextDescriptor = ();

    fn estimate_log2_relative_noise_level(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _noise: &Self::CiphertextDescriptor) -> f64 {
        0.
    }

    fn enc_sym_zero(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _hwt: SecretKeyDistribution) -> Self::CiphertextDescriptor {}
    fn hom_add(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _lhs: &Self::CiphertextDescriptor, _lhs_implicit_scale: &El<PlaintextZnRing<Params>>, _rhs: &Self::CiphertextDescriptor, _rhs_implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {}
    fn hom_add_plain(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<PlaintextRing<Params>>, _ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {}
    fn hom_add_plain_encoded(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, _ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {}
    fn hom_galois(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _C_special: &CiphertextRing<Params>, _special_modulus_rns_factor_indices: &RNSFactorIndexList, _ct: &Self::CiphertextDescriptor, _g: &GaloisGroupEl, _gk: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor {}
    fn hom_mul(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _C_special: &CiphertextRing<Params>, _special_modulus_rns_factor_indices: &RNSFactorIndexList, _lhs: &Self::CiphertextDescriptor, _rhs: &Self::CiphertextDescriptor, _rk: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor {}
    fn hom_mul_plain(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<PlaintextRing<Params>>, _ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {}
    fn hom_mul_plain_encoded(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, _ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {}
    fn hom_mul_plain_int(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<BigIntRing>, _ct: &Self::CiphertextDescriptor, _implicit_scale: &El<PlaintextZnRing<Params>>) -> Self::CiphertextDescriptor {}
    fn key_switch(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _C_special: &CiphertextRing<Params>, _special_modulus_rns_factor_indices: &RNSFactorIndexList, _ct: &Self::CiphertextDescriptor, _key_switch_key: KeySwitchKeyDescriptor) -> Self::CiphertextDescriptor {}
    fn mod_switch_down_ct(&self, _P: &PlaintextRing<Params>, _Cnew: &CiphertextRing<Params>, _Cold: &CiphertextRing<Params>, _drop_moduli: &RNSFactorIndexList, _ct: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor {}
    fn transparent_zero(&self) -> Self::CiphertextDescriptor {}
    fn change_plaintext_modulus(_Pnew: &PlaintextRing<Params>, _Pold: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _ct: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor {}
    fn clone_critical_quantity_level(&self, _val: &Self::CiphertextDescriptor) -> Self::CiphertextDescriptor {}
}
