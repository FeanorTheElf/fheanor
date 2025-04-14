
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

pub trait BGVNoiseEstimator<Params: BGVCiphertextParams> {

    ///
    /// An estimate of the size and distribution of the critical quantity
    /// `c0 + c1 s = m + t e`. The only requirement is that the noise estimator
    /// can derive an estimate about its infinity norm via
    /// [`BGVNoiseEstimator::estimate_log2_relative_noise_level`], but estimators are free
    /// to store additional data to get more precise estimates on the noise growth
    /// of operations.
    ///
    type CriticalQuantityLevel;

    ///
    /// Should return an estimate of
    /// ```text
    ///   log2( | c0 + c1 * s |_inf / q )
    /// ```
    ///
    fn estimate_log2_relative_noise_level(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, noise: &Self::CriticalQuantityLevel) -> f64;

    fn enc_sym_zero(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, hwt: Option<usize>) -> Self::CriticalQuantityLevel;

    fn transparent_zero(&self) -> Self::CriticalQuantityLevel;

    fn hom_add_plain(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, ct: &Self::CriticalQuantityLevel, implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel;

    fn hom_add_plain_encoded(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<CiphertextRing<Params>>, ct: &Self::CriticalQuantityLevel, implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel;

    fn enc_sym(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, hwt: Option<usize>) -> Self::CriticalQuantityLevel {
        self.hom_add_plain(P, C, m, &self.enc_sym_zero(P, C, hwt), P.base_ring().one())
    }

    fn hom_mul_plain(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, ct: &Self::CriticalQuantityLevel, implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel;

    fn hom_mul_plain_encoded(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<CiphertextRing<Params>>, ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel;

    fn hom_mul_plain_i64(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: i64, ct: &Self::CriticalQuantityLevel, implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel;

    fn merge_implicit_scale(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &Self::CriticalQuantityLevel, implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {
        self.hom_mul_plain_i64(P, C, P.base_ring().smallest_lift(P.base_ring().invert(&implicit_scale).unwrap()), ct, implicit_scale)
    }

    fn key_switch(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, ct: &Self::CriticalQuantityLevel, key: KeySwitchKeyParams) -> Self::CriticalQuantityLevel;

    fn hom_mul(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>,lhs: &Self::CriticalQuantityLevel, rhs: &Self::CriticalQuantityLevel, rk: KeySwitchKeyParams) -> Self::CriticalQuantityLevel;

    fn hom_add(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, lhs: &Self::CriticalQuantityLevel, lhs_implicit_scale: El<Zn>, rhs: &Self::CriticalQuantityLevel, rhs_implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel;

    fn hom_galois(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>,ct: &Self::CriticalQuantityLevel, _g: CyclotomicGaloisGroupEl, gk: KeySwitchKeyParams) -> Self::CriticalQuantityLevel {
        self.key_switch(P, C, C_special, ct, gk)
    }

    fn mod_switch_down(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, drop_moduli: &RNSFactorIndexList, ct: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel;

    fn change_plaintext_modulus(Pnew: &PlaintextRing<Params>, Pold: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel;

    fn clone_critical_quantity_level(&self, val: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel;
}

///
/// An estimate of `log2(|s|_can)` when `s` is sampled from `C`
/// 
fn log2_can_norm_sk_estimate<Params: BGVCiphertextParams>(C: &CiphertextRing<Params>) -> f64 {
    (C.rank() as f64).log2()
}

///
/// An estimate of `max_(x in P) log2( | shortest-lift(x) |_can )`
/// 
fn log2_can_norm_shortest_lift_estimate<Params: BGVCiphertextParams>(P: &PlaintextRing<Params>) -> f64 {
    (P.rank() as f64).log2() + (*P.base_ring().modulus() as f64).log2()
}

///
/// A [`BGVNoiseEstimator`] that uses some very simple formulas to estimate the noise
/// growth of BGV operations. This is WIP and very likely to be replaced later by
/// a better and more rigorous estimator.
///
pub struct NaiveBGVNoiseEstimator;

impl<Params: BGVCiphertextParams> BGVNoiseEstimator<Params> for NaiveBGVNoiseEstimator {

    /// We store `log2(| c0 + c1 s |_can / q)`; this is hopefully `< 0`
    type CriticalQuantityLevel = f64;

    fn estimate_log2_relative_noise_level(&self, _P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, noise: &Self::CriticalQuantityLevel) -> f64 {
        // we subtract `(C.rank() as f64).log2()`, since that should be about the difference between `l_inf` and canonical norm
        *noise - (C.rank() as f64).log2()
    }

    fn enc_sym_zero(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, _hwt: Option<usize>) -> Self::CriticalQuantityLevel {
        let result = (*P.base_ring().modulus() as f64).log2() + log2_can_norm_sk_estimate::<Params>(C) - BigIntRing::RING.abs_log2_floor(C.base_ring().modulus()).unwrap() as f64;
        assert!(!result.is_nan());
        return result;
    }

    fn hom_add(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, lhs: &Self::CriticalQuantityLevel, lhs_implicit_scale: El<Zn>, rhs: &Self::CriticalQuantityLevel, rhs_implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {
        let Zt = P.base_ring();
        let (a, b) = equalize_implicit_scale(Zt, Zt.checked_div(&lhs_implicit_scale, &rhs_implicit_scale).unwrap());
        assert!(!Zt.eq_el(&lhs_implicit_scale, &rhs_implicit_scale) || a == 1 && b == 1);
        debug_assert!(Zt.is_unit(&Zt.coerce(&ZZi64, a)));
        debug_assert!(Zt.is_unit(&Zt.coerce(&ZZi64, b)));
        let result = f64::max((b as f64).abs().log2() + *lhs, (a as f64).abs().log2() + *rhs);
        assert!(!result.is_nan());
        return result;
    }

    fn hom_add_plain(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<PlaintextRing<Params>>, ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {
        let result = *ct;
        assert!(!result.is_nan());
        return result;
    }

    fn hom_add_plain_encoded(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {
        let result = *ct;
        assert!(!result.is_nan());
        return result;
    }

    fn hom_mul_plain(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<PlaintextRing<Params>>, ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {
        let result = *ct + log2_can_norm_shortest_lift_estimate::<Params>(P);
        assert!(!result.is_nan());
        return result;
    }

    fn hom_mul_plain_encoded(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {
        let result = *ct + log2_can_norm_shortest_lift_estimate::<Params>(P);
        assert!(!result.is_nan());
        return result;
    }

    fn hom_mul_plain_i64(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, m: i64, ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {
        let result = *ct + (m as f64).abs().log2();
        assert!(!result.is_nan());
        return result;
    }

    fn transparent_zero(&self) -> Self::CriticalQuantityLevel {
        let result = -f64::INFINITY;
        assert!(!result.is_nan());
        return result;
    }

    fn mod_switch_down(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, drop_moduli: &RNSFactorIndexList, ct: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel {
        assert_eq!(Cnew.base_ring().len() + drop_moduli.len(), Cold.base_ring().len());
        let result = f64::max(
            *ct,
            (*P.base_ring().modulus() as f64).log2() + log2_can_norm_sk_estimate::<Params>(Cnew) - BigIntRing::RING.abs_log2_ceil(Cnew.base_ring().modulus()).unwrap() as f64
        );
        assert!(!result.is_nan());
        return result;
    }

    fn hom_mul(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, lhs: &Self::CriticalQuantityLevel, rhs: &Self::CriticalQuantityLevel, rk: KeySwitchKeyParams) -> Self::CriticalQuantityLevel {
        let log2_q = BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap() as f64;
        let intermediate_result = (*lhs + *rhs + 2. * log2_q) * HEURISTIC_FACTOR_MUL_INPUT_NOISE - log2_q;
        let result = <Self as BGVNoiseEstimator<Params>>::key_switch(self, P, C, C_special, &intermediate_result, rk);
        assert!(!result.is_nan());
        return result;
    }

    fn key_switch(&self, _P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, ct: &Self::CriticalQuantityLevel, switch_key: KeySwitchKeyParams) -> Self::CriticalQuantityLevel {
        assert_eq!(C.base_ring().len() + switch_key.special_modulus_factor_count, C_special.base_ring().len());
        let log2_q = BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap() as f64;
        let log2_largest_digit = switch_key.digits.iter().map(|digit| digit.iter().map(|i| *C_special.base_ring().at(i).modulus() as f64).map(f64::log2).sum::<f64>()).max_by(f64::total_cmp).unwrap();
        let special_modulus_log2 = (0..switch_key.special_modulus_factor_count).map(|i| *C_special.base_ring().at(C_special.base_ring().len() - 1 - i).modulus() as f64).map(f64::log2).sum::<f64>();
        let result = f64::max(
            *ct,
            log2_largest_digit - special_modulus_log2 + (C_special.rank() as f64).log2() * 2. - log2_q
        );
        assert!(!result.is_nan());
        return result;
    }

    fn change_plaintext_modulus(_Pnew: &PlaintextRing<Params>, _Pold: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, ct: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel {
        let result = *ct;
        assert!(!result.is_nan());
        return result;
    }

    fn clone_critical_quantity_level(&self, val: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel {
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

impl<Params: BGVCiphertextParams> BGVNoiseEstimator<Params> for AlwaysZeroNoiseEstimator {

    type CriticalQuantityLevel = ();

    fn estimate_log2_relative_noise_level(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _noise: &Self::CriticalQuantityLevel) -> f64 {
        0.
    }

    fn enc_sym_zero(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _hwt: Option<usize>) -> Self::CriticalQuantityLevel {}
    fn hom_add(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _lhs: &Self::CriticalQuantityLevel, _lhs_implicit_scale: El<Zn>, _rhs: &Self::CriticalQuantityLevel, _rhs_implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {}
    fn hom_add_plain(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<PlaintextRing<Params>>, _ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {}
    fn hom_add_plain_encoded(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, _ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {}
    fn hom_galois(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _C_special: &CiphertextRing<Params>, _ct: &Self::CriticalQuantityLevel, _g: CyclotomicGaloisGroupEl, _gk: KeySwitchKeyParams) -> Self::CriticalQuantityLevel {}
    fn hom_mul(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _C_special: &CiphertextRing<Params>, _lhs: &Self::CriticalQuantityLevel, _rhs: &Self::CriticalQuantityLevel, _rk: KeySwitchKeyParams) -> Self::CriticalQuantityLevel {}
    fn hom_mul_plain(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<PlaintextRing<Params>>, _ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {}
    fn hom_mul_plain_encoded(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, _ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {}
    fn hom_mul_plain_i64(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: i64, _ct: &Self::CriticalQuantityLevel, _implicit_scale: El<Zn>) -> Self::CriticalQuantityLevel {}
    fn key_switch(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _C_special: &CiphertextRing<Params>, _ct: &Self::CriticalQuantityLevel, _switch_key: KeySwitchKeyParams) -> Self::CriticalQuantityLevel {}
    fn mod_switch_down(&self, _P: &PlaintextRing<Params>, _Cnew: &CiphertextRing<Params>, _Cold: &CiphertextRing<Params>, _drop_moduli: &RNSFactorIndexList, _ct: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel {}
    fn transparent_zero(&self) -> Self::CriticalQuantityLevel {}
    fn change_plaintext_modulus(_Pnew: &PlaintextRing<Params>, _Pold: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _ct: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel {}
    fn clone_critical_quantity_level(&self, _val: &Self::CriticalQuantityLevel) -> Self::CriticalQuantityLevel {}
}
