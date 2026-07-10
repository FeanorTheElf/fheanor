
use std::borrow::Borrow;

use crate::bgv::*;

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

///
/// Shorthand for the type of an implicit scale value, i.e. an element of `Z/tZ`.
///
type ImplicitScale<Params> = <<Params as BGVInstantiation>::PlaintextZnRing as RingBase>::Element;

#[derive(Debug, Clone, Copy)]
pub struct KeySwitchKeyDescriptor<'a> {
    pub digits: &'a RNSGadgetVectorDigitIndices,
    pub sigma: f64,
    pub new_sk: SecretKeyDistribution
}

///
/// Bundles the estimator-specific noise descriptor of a ciphertext together with the
/// deterministic data that every BGV ciphertext carries: its implicit scale (see
/// [`Ciphertext::implicit_scale`]) and the [`SecretKeyDistribution`] of the secret key
/// it is encrypted with respect to.
///
pub struct CiphertextDescriptor<Params: BGVInstantiation, N: BGVNoiseEstimator<Params> + ?Sized> {
    /// The estimator-specific noise descriptor, see [`BGVNoiseEstimator::CiphertextDescriptor`].
    pub noise: N::CiphertextDescriptor,
    /// The implicit scale, see [`Ciphertext::implicit_scale`].
    pub implicit_scale: ImplicitScale<Params>,
    /// The distribution of the secret key this ciphertext is encrypted with respect to.
    pub sk: SecretKeyDistribution
}

impl<Params: BGVInstantiation, N: BGVNoiseEstimator<Params>> CiphertextDescriptor<Params, N> {

    pub fn new(noise: N::CiphertextDescriptor, implicit_scale: ImplicitScale<Params>, sk: SecretKeyDistribution) -> Self {
        Self { noise, implicit_scale, sk }
    }
}

///
/// A trait for objects that provide estimates of the noise level of BGV ciphertexts after
/// homomorphic operations.
///
/// # Relation to [`BGVInstantiation`]
///
/// The interface of [`BGVNoiseEstimator`] mirrors the interface of [`BGVInstantiation`]:
/// for each (noise-relevant) homomorphic operation of [`BGVInstantiation`], there is a
/// correspondingly-named operation here. The differences are
///  - [`Ciphertext`] parameters/return values are replaced by [`CiphertextDescriptor`],
///  - key-switching keys are replaced by [`KeySwitchKeyDescriptor`],
///  - secret keys are replaced by [`SecretKeyDistribution`],
///  - functions that do nothing noise-related (e.g. `create_rns_base`, `create_plaintext_ring`,
///    `gen_sk`) are omitted, and randomness (`rng`) and noise standard deviations are not
///    passed in (the latter is folded into [`KeySwitchKeyDescriptor::sigma`] where relevant).
///
/// As with [`BGVInstantiation`], most operations have a default implementation that delegates
/// to a small set of "primitive" operations, so an implementor only needs to provide noise
/// formulas for the latter.
///
pub trait BGVNoiseEstimator<Params: BGVInstantiation>: Sized {

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
    fn estimate_log2_relative_noise_level(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> f64;

    ///
    /// Copies a ciphertext descriptor, see [`BGVInstantiation::clone_ct()`].
    ///
    fn clone_ct(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Describes a fresh encryption of zero, see [`BGVInstantiation::enc_sym_zero()`].
    ///
    fn enc_sym_zero(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Describes a transparent encryption of zero, see [`BGVInstantiation::transparent_zero()`].
    ///
    fn transparent_zero(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_add_plain_encoded()`].
    ///
    fn hom_add_plain_encoded(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<CiphertextRing<Params>>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_mul_plain_encoded()`].
    ///
    fn hom_mul_plain_encoded(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<CiphertextRing<Params>>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of a plaintext-ciphertext multiplication by an integer (interpreted
    /// as a constant plaintext). This has no direct analogue in [`BGVInstantiation`], but is
    /// useful since the size of the integer determines the noise growth more tightly than
    /// going through the plaintext ring.
    ///
    fn hom_mul_plain_int(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<BigIntRing>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_add()`].
    ///
    fn hom_add(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, lhs: &CiphertextDescriptor<Params, Self>, rhs: &CiphertextDescriptor<Params, Self>, policy: ImplicitScalePolicy) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::key_switch()`]. The special modulus is inferred
    /// from `C` and `C_special` (it is the set of RNS factors of `C_special` not present in `C`).
    ///
    fn key_switch(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>, switch_key: KeySwitchKeyDescriptor) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::mod_switch_ct()`].
    ///
    fn mod_switch_ct(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::fake_mod_switch_down_ct()`].
    ///
    fn fake_mod_switch_down_ct(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::change_plaintext_modulus()`].
    ///
    fn change_plaintext_modulus(&self, Pnew: &PlaintextRing<Params>, Pold: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::encode_plain()`] followed by
    /// [`BGVInstantiation::hom_add_plain_encoded()`], see [`BGVInstantiation::hom_add_plain()`].
    ///
    fn hom_add_plain(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        self.hom_add_plain_encoded(P, C, &Params::encode_plain(P, C, m), ct)
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_add_plain_scalar()`].
    ///
    fn hom_add_plain_scalar(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &ImplicitScale<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        let m_encoded = C.inclusion().map(C.base_ring().coerce(&ZZbig, int_cast(P.base_ring().smallest_lift(P.base_ring().clone_el(m)), ZZbig, P.base_ring().integer_ring())));
        self.hom_add_plain_encoded(P, C, &m_encoded, ct)
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::enc_sym()`].
    ///
    fn enc_sym(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, sk: SecretKeyDistribution) -> CiphertextDescriptor<Params, Self> {
        self.hom_add_plain(P, C, m, &self.enc_sym_zero(P, C, sk))
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_mul_plain()`].
    ///
    fn hom_mul_plain(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &El<PlaintextRing<Params>>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        self.hom_mul_plain_encoded(P, C, &Params::encode_plain(P, C, m), ct)
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_mul_plain_scalar()`].
    ///
    fn hom_mul_plain_scalar(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, m: &ImplicitScale<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        self.hom_mul_plain_int(P, C, &int_cast(P.base_ring().smallest_lift(P.base_ring().clone_el(m)), ZZbig, P.base_ring().integer_ring()), ct)
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::merge_implicit_scale()`].
    ///
    fn merge_implicit_scale(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        let scale = int_cast(P.base_ring().smallest_lift(P.base_ring().invert(&ct.implicit_scale).unwrap()), ZZbig, P.base_ring().integer_ring());
        let mut result = self.hom_mul_plain_int(P, C, &scale, ct);
        result.implicit_scale = P.base_ring().one();
        return result;
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_sub()`].
    ///
    fn hom_sub(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, lhs: &CiphertextDescriptor<Params, Self>, rhs: &CiphertextDescriptor<Params, Self>, policy: ImplicitScalePolicy) -> CiphertextDescriptor<Params, Self> {
        // negating a ciphertext does not change its noise (or implicit scale magnitude)
        self.hom_add(P, C, lhs, rhs, policy)
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_mul()`].
    ///
    fn hom_mul(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, lhs: &CiphertextDescriptor<Params, Self>, rhs: &CiphertextDescriptor<Params, Self>, rk: KeySwitchKeyDescriptor) -> CiphertextDescriptor<Params, Self>;

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_square()`].
    ///
    fn hom_square(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, val: &CiphertextDescriptor<Params, Self>, rk: KeySwitchKeyDescriptor) -> CiphertextDescriptor<Params, Self> {
        self.hom_mul(P, C, C_special, val, val, rk)
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_galois()`].
    ///
    fn hom_galois(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>, _g: &GaloisGroupEl, gk: KeySwitchKeyDescriptor) -> CiphertextDescriptor<Params, Self> {
        self.key_switch(P, C, C_special, ct, gk)
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_galois_many()`].
    ///
    fn hom_galois_many<'b, V>(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>, gs: &[GaloisGroupEl], gks: V) -> Vec<CiphertextDescriptor<Params, Self>>
        where V: VectorFn<KeySwitchKeyDescriptor<'b>>
    {
        assert_eq!(gs.len(), gks.len());
        (0..gs.len()).map(|i| self.hom_galois(P, C, C_special, ct, &gs[i], gks.at(i))).collect()
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_inner_product_plain_scalar()`].
    ///
    fn hom_inner_product_plain_scalar<'a, I>(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, summands: I) -> CiphertextDescriptor<Params, Self>
        where I: IntoIterator<Item = (ImplicitScale<Params>, &'a CiphertextDescriptor<Params, Self>)>,
            Params: 'a,
            Self: 'a
    {
        let mut acc: Option<CiphertextDescriptor<Params, Self>> = None;
        for (m, ct) in summands {
            // mirror the data side (`BGVInstantiation::hom_inner_product_plain_scalar`): fold the
            // implicit scale into the scalar (free, does not increase noise), so the term has
            // implicit scale 1; do *not* merge the implicit scale into the ciphertext.
            let scalar = P.base_ring().mul_ref_fst(m.borrow(), P.base_ring().invert(&ct.implicit_scale).unwrap());
            let mut term = self.hom_mul_plain_scalar(P, C, &scalar, ct);
            term.implicit_scale = P.base_ring().one();
            acc = Some(match acc {
                None => term,
                Some(a) => self.hom_add(P, C, &a, &term, ImplicitScalePolicy::AssertEqual)
            });
        }
        acc.unwrap_or_else(|| self.transparent_zero(P, C))
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_inner_product_plain()`].
    ///
    fn hom_inner_product_plain<L, R, I>(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, summands: I) -> CiphertextDescriptor<Params, Self>
        where L: Borrow<El<PlaintextRing<Params>>>,
            R: Borrow<CiphertextDescriptor<Params, Self>>,
            I: IntoIterator<Item = (L, R)>
    {
        let mut acc: Option<CiphertextDescriptor<Params, Self>> = None;
        for (m, ct) in summands {
            let ct = ct.borrow();
            // mirror the data side (`BGVInstantiation::hom_inner_product_plain`): fold the implicit
            // scale into the plaintext (free, does not increase noise), so the term has implicit
            // scale 1; do *not* merge the implicit scale into the ciphertext.
            let m_merged = P.inclusion().mul_map(P.clone_el(m.borrow()), P.base_ring().invert(&ct.implicit_scale).unwrap());
            let mut term = self.hom_mul_plain(P, C, &m_merged, ct);
            term.implicit_scale = P.base_ring().one();
            acc = Some(match acc {
                None => term,
                Some(a) => self.hom_add(P, C, &a, &term, ImplicitScalePolicy::AssertEqual)
            });
        }
        acc.unwrap_or_else(|| self.transparent_zero(P, C))
    }

    ///
    /// Noise equivalent of [`BGVInstantiation::hom_inner_product_plain_encoded()`].
    ///
    fn hom_inner_product_plain_encoded<L, R, I>(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, summands: I, policy: ImplicitScalePolicy) -> CiphertextDescriptor<Params, Self>
        where L: Borrow<El<CiphertextRing<Params>>>,
            R: Borrow<CiphertextDescriptor<Params, Self>>,
            I: IntoIterator<Item = (L, R)>
    {
        let mut acc: Option<CiphertextDescriptor<Params, Self>> = None;
        for (m, ct) in summands {
            // mirror the data side (`BGVInstantiation::hom_inner_product_plain_encoded`): bring
            // each summand to the policy-dictated implicit scale *first* - `Merge` rescales each
            // summand to implicit scale 1 (which genuinely increases noise here, since an encoded
            // plaintext cannot be merged for free), `AssertEqual` keeps the common scale - then add
            // the (now equalized) terms directly.
            let term = match policy {
                ImplicitScalePolicy::Merge => {
                    let merged = self.merge_implicit_scale(P, C, ct.borrow());
                    self.hom_mul_plain_encoded(P, C, m.borrow(), &merged)
                },
                ImplicitScalePolicy::AssertEqual => self.hom_mul_plain_encoded(P, C, m.borrow(), ct.borrow())
            };
            acc = Some(match acc {
                None => term,
                Some(a) => self.hom_add(P, C, &a, &term, ImplicitScalePolicy::AssertEqual)
            });
        }
        acc.unwrap_or_else(|| self.transparent_zero(P, C))
    }
}

fn mul_scale<Params: BGVInstantiation>(P: &PlaintextRing<Params>, lhs: &ImplicitScale<Params>, rhs: &ImplicitScale<Params>) -> ImplicitScale<Params> {
    P.base_ring().mul_ref(lhs, rhs)
}

fn mod_switch_scale<Params: BGVInstantiation>(P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, scale: &ImplicitScale<Params>) -> ImplicitScale<Params> {
    P.base_ring().mul_ref_fst(scale, Params::mod_switch_compute_implicit_scale_factor(P, Cnew.base_ring().modulus(), Cold.base_ring().modulus()))
}

fn change_plaintext_modulus_scale<Params: BGVInstantiation>(Pnew: &PlaintextRing<Params>, Pold: &PlaintextRing<Params>, scale: &ImplicitScale<Params>) -> ImplicitScale<Params> {
    Pnew.base_ring().coerce(Pnew.base_ring().integer_ring(), Pold.base_ring().smallest_positive_lift(Pold.base_ring().clone_el(scale)))
}

fn add_scale<Params: BGVInstantiation>(P: &PlaintextRing<Params>, lhs: &ImplicitScale<Params>, rhs: &ImplicitScale<Params>, policy: ImplicitScalePolicy) -> ImplicitScale<Params> {
    match policy {
        ImplicitScalePolicy::AssertEqual => {
            assert!(P.base_ring().eq_el(lhs, rhs), "ImplicitScalePolicy::AssertEqual requires all summands to have the same implicit scale");
            P.base_ring().clone_el(lhs)
        },
        ImplicitScalePolicy::Merge => P.base_ring().one()
    }
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
    log2_relative_critical_quantity: f64
}

impl NaiveBGVNoiseEstimator {

    fn descriptor<Params: BGVInstantiation>(log2_relative_critical_quantity: f64, implicit_scale: ImplicitScale<Params>, sk: SecretKeyDistribution) -> CiphertextDescriptor<Params, Self> {
        assert!(!log2_relative_critical_quantity.is_nan());
        CiphertextDescriptor::new(NaiveBGVNoiseEstimatorNoiseDescriptor { log2_relative_critical_quantity }, implicit_scale, sk)
    }
}

impl<Params: BGVInstantiation> BGVNoiseEstimator<Params> for NaiveBGVNoiseEstimator {

    type CiphertextDescriptor = NaiveBGVNoiseEstimatorNoiseDescriptor;

    fn estimate_log2_relative_noise_level(&self, _P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> f64 {
        // we subtract `(C.rank() as f64).log2()`, since that should be about the difference between `l_inf` and canonical norm
        ct.noise.log2_relative_critical_quantity - (C.rank() as f64).log2()
    }

    fn clone_ct(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        Self::descriptor::<Params>(ct.noise.log2_relative_critical_quantity, P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn enc_sym_zero(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> CiphertextDescriptor<Params, Self> {
        let result = t_log2::<Params>(P) + log2_can_norm_sk_estimate::<Params>(C, sk) - BigIntRing::RING.abs_log2_floor(C.base_ring().modulus()).unwrap() as f64;
        Self::descriptor::<Params>(result, P.base_ring().one(), sk)
    }

    fn transparent_zero(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>) -> CiphertextDescriptor<Params, Self> {
        Self::descriptor::<Params>(-f64::INFINITY, P.base_ring().one(), SecretKeyDistribution::Zero)
    }

    fn hom_add_plain_encoded(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        Self::descriptor::<Params>(ct.noise.log2_relative_critical_quantity, P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn hom_mul_plain_encoded(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        Self::descriptor::<Params>(ct.noise.log2_relative_critical_quantity + log2_can_norm_shortest_lift_estimate::<Params>(P), P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn hom_mul_plain_int(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, m: &El<BigIntRing>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        Self::descriptor::<Params>(ct.noise.log2_relative_critical_quantity + ZZbig.abs_log2_ceil(m).unwrap_or(0) as f64, P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn hom_add(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, lhs: &CiphertextDescriptor<Params, Self>, rhs: &CiphertextDescriptor<Params, Self>, policy: ImplicitScalePolicy) -> CiphertextDescriptor<Params, Self> {
        let (lhs, rhs) = match policy {
            ImplicitScalePolicy::AssertEqual => (self.clone_ct(P, C, lhs), self.clone_ct(P, C, rhs)),
            ImplicitScalePolicy::Merge => (self.merge_implicit_scale(P, C, lhs), self.merge_implicit_scale(P, C, rhs))
        };
        let result = f64::max(lhs.noise.log2_relative_critical_quantity, rhs.noise.log2_relative_critical_quantity);
        Self::descriptor::<Params>(result, add_scale::<Params>(P, &lhs.implicit_scale, &rhs.implicit_scale, policy), assert_sk_distr_match(lhs.sk, rhs.sk))
    }

    fn key_switch(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>, switch_key: KeySwitchKeyDescriptor) -> CiphertextDescriptor<Params, Self> {
        let special_modulus_rns_factor_indices = RNSFactorIndexList::missing_from_subset(C.base_ring(), C_special.base_ring()).unwrap();
        let log2_q = BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap() as f64;
        let log2_largest_digit = switch_key.digits.iter().map(|digit| digit.iter().map(|i| *C_special.base_ring().at(i).modulus() as f64).map(f64::log2).sum::<f64>()).max_by(f64::total_cmp).unwrap();
        let special_modulus_log2 = special_modulus_rns_factor_indices.iter().map(|i| *C_special.base_ring().at(*i).modulus() as f64).map(f64::log2).sum::<f64>();
        let result = f64::max(
            ct.noise.log2_relative_critical_quantity,
            log2_largest_digit - special_modulus_log2 + (C_special.rank() as f64).log2() * 2. - log2_q
        );
        Self::descriptor::<Params>(result, P.base_ring().clone_el(&ct.implicit_scale), switch_key.new_sk)
    }

    fn mod_switch_ct(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        let result = f64::max(
            ct.noise.log2_relative_critical_quantity,
            t_log2::<Params>(P) + log2_can_norm_sk_estimate::<Params>(Cnew, ct.sk) - BigIntRing::RING.abs_log2_ceil(Cnew.base_ring().modulus()).unwrap() as f64
        );
        Self::descriptor::<Params>(result, mod_switch_scale::<Params>(P, Cnew, Cold, &ct.implicit_scale), ct.sk)
    }

    fn hom_mul(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_special: &CiphertextRing<Params>, lhs: &CiphertextDescriptor<Params, Self>, rhs: &CiphertextDescriptor<Params, Self>, rk: KeySwitchKeyDescriptor) -> CiphertextDescriptor<Params, Self> {
        let log2_q = BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap() as f64;
        let result = (lhs.noise.log2_relative_critical_quantity + rhs.noise.log2_relative_critical_quantity + 2. * log2_q) * HEURISTIC_FACTOR_MUL_INPUT_NOISE - log2_q;
        let result_no_relin = Self::descriptor::<Params>(result, mul_scale::<Params>(P, &lhs.implicit_scale, &rhs.implicit_scale), assert_sk_distr_match(lhs.sk, rhs.sk));
        self.key_switch(P, C, C_special, &result_no_relin, rk)
    }

    fn fake_mod_switch_down_ct(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        let result = ct.noise.log2_relative_critical_quantity + ZZbig.abs_log2_ceil(Cold.base_ring().modulus()).unwrap() as f64 - ZZbig.abs_log2_floor(Cnew.base_ring().modulus()).unwrap() as f64;
        Self::descriptor(result, P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn change_plaintext_modulus(&self, Pnew: &PlaintextRing<Params>, Pold: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        Self::descriptor::<Params>(ct.noise.log2_relative_critical_quantity, change_plaintext_modulus_scale::<Params>(Pnew, Pold, &ct.implicit_scale), ct.sk)
    }
}

///
/// Noise estimator that always returns 0 as estimated noise budget.
///
/// Its only use is probably to have a default value in places where a
/// noise estimator is required but never used, as well as to implement
/// [`super::modswitch::DefaultModswitchStrategy::never_modswitch()`].
///
/// Note that, although it tracks no noise, it still keeps track of the implicit
/// scale and secret key distribution, since these are needed for correctness
/// (and not just noise estimation).
///
pub struct AlwaysZeroNoiseEstimator;

impl<Params: BGVInstantiation> BGVNoiseEstimator<Params> for AlwaysZeroNoiseEstimator {

    type CiphertextDescriptor = ();

    fn estimate_log2_relative_noise_level(&self, _P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _ct: &CiphertextDescriptor<Params, Self>) -> f64 {
        0.
    }

    fn clone_ct(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn enc_sym_zero(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, sk: SecretKeyDistribution) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().one(), sk)
    }

    fn transparent_zero(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().one(), SecretKeyDistribution::Zero)
    }

    fn hom_add_plain_encoded(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn hom_mul_plain_encoded(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<CiphertextRing<Params>>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn hom_mul_plain_int(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _m: &El<BigIntRing>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn hom_add(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, lhs: &CiphertextDescriptor<Params, Self>, rhs: &CiphertextDescriptor<Params, Self>, policy: ImplicitScalePolicy) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), add_scale::<Params>(P, &lhs.implicit_scale, &rhs.implicit_scale, policy), assert_sk_distr_match(lhs.sk, rhs.sk))
    }

    fn hom_mul(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _C_special: &CiphertextRing<Params>, lhs: &CiphertextDescriptor<Params, Self>, rhs: &CiphertextDescriptor<Params, Self>, _rk: KeySwitchKeyDescriptor) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().mul_ref(&lhs.implicit_scale, &rhs.implicit_scale), assert_sk_distr_match(lhs.sk, rhs.sk))
    }

    fn key_switch(&self, P: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, _C_special: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>, switch_key: KeySwitchKeyDescriptor) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().clone_el(&ct.implicit_scale), switch_key.new_sk)
    }

    fn mod_switch_ct(&self, P: &PlaintextRing<Params>, Cnew: &CiphertextRing<Params>, Cold: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), mod_switch_scale::<Params>(P, Cnew, Cold, &ct.implicit_scale), ct.sk)
    }

    fn fake_mod_switch_down_ct(&self, P: &PlaintextRing<Params>, _Cnew: &CiphertextRing<Params>, _Cold: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), P.base_ring().clone_el(&ct.implicit_scale), ct.sk)
    }

    fn change_plaintext_modulus(&self, Pnew: &PlaintextRing<Params>, Pold: &PlaintextRing<Params>, _C: &CiphertextRing<Params>, ct: &CiphertextDescriptor<Params, Self>) -> CiphertextDescriptor<Params, Self> {
        CiphertextDescriptor::new((), change_plaintext_modulus_scale::<Params>(Pnew, Pold, &ct.implicit_scale), ct.sk)
    }
}
