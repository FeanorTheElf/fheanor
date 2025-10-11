use std::alloc::{Allocator, Global};
use std::convert::identity;
use std::fmt::Display;
use std::marker::PhantomData;
use std::ops::Range;
use std::sync::Arc;

use feanor_math::algorithms::convolution::STANDARD_CONVOLUTION;
use feanor_math::algorithms::eea::signed_gcd;
use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::algorithms::rational_reconstruction::reduce_2d_modular_relation_basis;
use feanor_math::homomorphism::*;
use feanor_math::integer::{int_cast, BigIntRing, IntegerRingStore};
use feanor_math::matrix::OwnedMatrix;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::ring::*;
use feanor_math::rings::extension::*;
use feanor_math::rings::finite::*;
use feanor_math::rings::zn::zn_64::{Zn, ZnBase};
use feanor_math::rings::zn::{zn_rns, ZnRing};
use feanor_math::rings::zn::ZnRingStore;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::seq::*;
use tracing::instrument;

use crate::ciphertext_ring::double_rns_managed::ManagedDoubleRNSRingBase;
use crate::ciphertext_ring::double_rns_ring::DoubleRNSRingBase;
use crate::ciphertext_ring::indices::RNSFactorIndexList;
use crate::ciphertext_ring::{perform_rns_op, single_rns_ring::*, RNSFactorCongruence};
use crate::ciphertext_ring::BGFVCiphertextRing;
use crate::gadget_product::{RNSGadgetProductLhsOperand, RNSGadgetProductRhsOperand};
use crate::number_ring::galois::GaloisGroupEl;
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
use crate::NiceZn;
use crate::gadget_product::digits::RNSGadgetVectorDigitIndices;
use crate::ntt::{FheanorConvolution, FheanorNegacyclicNTT};
use crate::number_ring::hypercube::isomorphism::*;
use crate::number_ring::galois::CyclotomicGaloisGroupOps;
use crate::number_ring::hypercube::structure::HypercubeStructure;
use crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing;
use crate::number_ring::*;
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
use crate::rns_conv::bgv_rescale::CongruencePreservingAlmostExactBaseConversion;
use crate::rns_conv::{RNSOperation, UsedBaseConversion};
use crate::{DefaultCiphertextAllocator, DefaultConvolution, DefaultNegacyclicNTT};
use crate::{ZZi64, ZZbig};

use rand_distr::StandardNormal;
use rand::*;

pub type NumberRing<Params: BGVInstantiation> = <Params::CiphertextRing as NumberRingQuotient>::NumberRing;
pub type CiphertextRing<Params: BGVInstantiation> = RingValue<Params::CiphertextRing>;
pub type PlaintextRing<Params: BGVInstantiation> = RingValue<Params::PlaintextRing>;
pub type PlaintextZnRing<Params: BGVInstantiation> = RingValue<Params::PlaintextZnRing>;
pub type SecretKey<Params: BGVInstantiation> = El<CiphertextRing<Params>>;
pub type RelinKey<'a, Params: BGVInstantiation> = KeySwitchKey<'a, Params>;

///
/// When choosing primes for an RNS base, we restrict to primes of this bitlength.
/// The reason is that the corresponding quotient rings can be represented by [`zn_64::Zn`].
/// 
const SAMPLE_PRIMES_SIZE: usize = 57;

///
/// Represents one of multiple distributions over `R` that are commonly used
/// to sample the secret key from.
/// 
#[derive(Debug, Clone, Copy)]
pub enum SecretKeyDistribution {
    /// The constant zero distribution. Clearly such a secret key will be insecure.
    Zero, 
    /// Sparse distribution with given hamming weight.
    /// 
    /// In other words, a random choice of coefficients of the given size is
    /// set to a uniformly random value from `{-1, 1}`, and the others
    /// are set to set.
    SparseWithHwt(usize), 
    /// Each coefficient is taken uniformly at random from `{-1, 0, 1}`.
    UniformTernary, 
    /// A custom distribution, where the given number is the binary logarithm
    /// of a (high-probability) bound on the canonical norm of an element sampled
    /// from this distribution.
    /// 
    /// Clearly this cannot be used in [`BGVInstantiation::gen_sk()`], since the
    /// distribution is not fixed. The main use case of `Custom` is thus to instantiate
    /// noise estimation functionality with customly generated secret keys.
    Custom(f64)
}

///
/// A key-switching key for BGV. This includes Relinearization and Galois keys.
/// Note that this implementation does not include an automatic management of
/// the ciphertext modulus chain, it is up to the user to keep track of the RNS
/// base used for each ciphertext.
/// 
/// # On the special modulus
/// 
/// In Fheanor, a variant of hybrid key-switching is used where the key-switching
/// key does not depend on the special modulus. This means the key-switching keys
/// will be slightly larger (since they have to store a component for the digit
/// that would otherwise belong to the fixed special modulus, and thus can be skipped).
/// However, it gives much more flexibility.
/// 
/// Hence, the special modulus is only given to whatever function performs
/// key-switching, e.g. [`BGVInstantiation::hom_mul()`], [`BGVInstantiation::hom_galois()`]
/// or [`BGVInstantiation::key_switch()`].
/// 
pub struct KeySwitchKey<'a, Params: ?Sized + BGVInstantiation> {
    k0: RNSGadgetProductRhsOperand<Params::CiphertextRing>,
    k1: RNSGadgetProductRhsOperand<Params::CiphertextRing>,
    ring: PhantomData<&'a CiphertextRing<Params>>
}

impl<'a, Params: ?Sized + BGVInstantiation> KeySwitchKey<'a, Params> {

    ///
    /// Returns the digits used for the gadget vector
    /// 
    pub fn gadget_vector_digits(&self) -> &RNSGadgetVectorDigitIndices {
        self.k0.gadget_vector_digits()
    }

    ///
    /// Returns the constant component of the key-switching key, i.e. `k0` from
    /// the tuple `k0, k1` that satisfies `k0[i] + k1[i] * s_new = g[i] * s_old`
    /// 
    pub fn k0<'b>(&'b self) -> &'b RNSGadgetProductRhsOperand<Params::CiphertextRing> {
        &self.k0
    }

    ///
    /// Returns the linear component of the key-switching key, i.e. `k1` from
    /// the tuple `k0, k1` that satisfies `k0[i] + k1[i] * s_new = g[i] * s_old`
    /// 
    pub fn k1<'b>(&'b self) -> &'b RNSGadgetProductRhsOperand<Params::CiphertextRing> {
        &self.k1
    }
}

///
/// Contains the trait [`noise_estimator::BGVNoiseEstimator`] for objects that provide
/// estimates of the noise level of ciphertexts after BGV homomorphic operations.
/// Currently, the only provided implementation is the somewhat imprecise and not rigorously
/// justified [`noise_estimator::NaiveBGVNoiseEstimator`], which is based on simple asymptotic
/// formulas.
/// 
pub mod noise_estimator;
///
/// Contains the trait [`modswitch::BGVModswitchStrategy`] and the implementation
/// [`modswitch::DefaultModswitchStrategy`] for automatic modulus management in BGV.
/// 
pub mod modswitch;
///
/// Contains the implementation of BGV thin bootstrapping.
/// 
pub mod bootstrap;

///
/// A BGV ciphertext w.r.t. some [`BGVInstantiation`]. Note that this implementation
/// does not include an automatic management of the ciphertext modulus chain,
/// it is up to the user to keep track of the RNS base used for each ciphertext.
/// 
pub struct Ciphertext<Params: ?Sized + BGVInstantiation> {
    /// the ciphertext represents the value `implicit_scale^-1 lift(c0 + c1 s) mod t`, 
    /// i.e. `implicit_scale` stores the factor in `Z/tZ` that is introduced by modulus-switching;
    /// Hence, `implicit_scale` is set to `1` when encrypting a value, and only changes when
    /// doing modulus-switching.
    pub implicit_scale: <Params::PlaintextZnRing as RingBase>::Element,
    pub c0: El<CiphertextRing<Params>>,
    pub c1: El<CiphertextRing<Params>>
}

///
/// Computes small `a, b` such that `a/b = implicit_scale_quotient` modulo `t`.
/// 
pub fn equalize_implicit_scale<R>(Zt: R, implicit_scale_quotient: El<R>) -> (El<<R::Type as ZnRing>::IntegerRing>, El<<R::Type as ZnRing>::IntegerRing>)
    where R: Copy + RingStore,
        R::Type: ZnRing
{
    assert!(Zt.is_unit(&implicit_scale_quotient));
    let ([u0, u1], [v0, v1]) = reduce_2d_modular_relation_basis(Zt, Zt.clone_el(&implicit_scale_quotient));
    let ZZi64_to_Zt = Zt.can_hom(Zt.integer_ring()).unwrap();
    let result: (El<<R::Type as ZnRing>::IntegerRing>, El<<R::Type as ZnRing>::IntegerRing>) = if Zt.is_unit(&ZZi64_to_Zt.map_ref(&u0)) {
        (u1, u0)
    } else {
        if !Zt.is_unit(&ZZi64_to_Zt.map_ref(&v0)) {
            // this cannot happen if t is a prime power, since the lattice contains `(1, x)`, hence `a u[0] + b v[0] = 1 mod t`
            // for some `a, b`. If `t` is a prime power, this implies that either `u[0]` or `v[0]` must be a unit mod `t`.
            unimplemented!("the case that the plaintext modulus t is not a prime power is not yet fully supported")
        }
        (v1, v0)
    };
    let ZZ_to_Zt = Zt.can_hom(Zt.integer_ring()).unwrap();
    debug_assert!(Zt.eq_el(&implicit_scale_quotient, &Zt.checked_div(&ZZ_to_Zt.map_ref(&result.0), &ZZ_to_Zt.map_ref(&result.1)).unwrap()));
    return result;
}

///
/// Trait for types that represent an instantiation of BGV.
/// 
/// The design is very similar to [`crate::bfv::BFVInstantiation`], for details
/// have a look at that.
/// 
/// For a few more details on how this works, see [`crate::examples::clpx_basics`].
/// 
pub trait BGVInstantiation {
    
    type NumberRing: AbstractNumberRing;

    ///
    /// Type of the ciphertext ring `R/qR`.
    /// 
    type CiphertextRing: BGFVCiphertextRing<NumberRing = Self::NumberRing>;

    ///
    /// Type of the plaintext base ring `Z/tZ`.
    /// 
    type PlaintextZnRing: NiceZn;
    
    ///
    /// Type of the plaintext ring `R/tR`.
    /// 
    type PlaintextRing: NumberRingQuotient<BaseRing = RingValue<Self::PlaintextZnRing>, NumberRing = Self::NumberRing>;

    ///
    /// Creates a new RNS base, by sampling a fresh, suitable `q` with the
    /// given bitlength.
    /// 
    /// For more details on the modulus chain, see [`crate::examples::bgv_basics`].
    /// 
    fn create_rns_base(&self, log2_q: Range<usize>) -> zn_rns::Zn<Zn, BigIntRing>;

    ///
    /// Creates the ciphertext ring corresponding to the given RNS base.
    /// 
    /// In many cases, you might already have access to a ciphertext ring
    /// with larger RNS base, in these cases it is more efficient to use
    /// [`BGVInstantiation::mod_switch_down_C()`].
    /// 
    fn create_ciphertext_ring_with_rns_base(&self, rns_base: zn_rns::Zn<Zn, BigIntRing>) -> CiphertextRing<Self>;

    ///
    /// Creates a ciphertext ring by sampling a fresh, suitable `q` with the
    /// given bitlength.
    /// 
    /// For more details on the modulus chain, see [`crate::examples::bgv_basics`].
    /// 
    fn create_ciphertext_ring(&self, log2_q: Range<usize>) -> CiphertextRing<Self> {
        self.create_ciphertext_ring_with_rns_base(self.create_rns_base(log2_q))
    }

    ///
    /// The number ring `R` from which we derive the ciphertext rings `R/qR` and the
    /// plaintext ring `R/tR`.
    /// 
    fn number_ring(&self) -> &NumberRing<Self>;

    ///
    /// Creates a plaintext ring `R/tR` for the given plaintext modulus `t`.
    /// 
    fn create_plaintext_ring(&self, modulus: El<BigIntRing>) -> PlaintextRing<Self>;

    ///
    /// Generates a secret key, which is either a sparse ternary element of the
    /// ciphertext ring (with hamming weight `hwt`), or a uniform ternary element
    /// of the ciphertext ring (if `hwt == None`).
    /// 
    #[instrument(skip_all)]
    fn gen_sk<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, mut rng: R, hwt: SecretKeyDistribution) -> SecretKey<Self> {
        match hwt {
            SecretKeyDistribution::Custom(_) => panic!("cannot create a secret key if the distribution is not specified; consider creating it manually"),
            SecretKeyDistribution::SparseWithHwt(hwt) => {
                assert!(hwt > 0, "if you want to use zero as secret key, use SecretKeyDistribution::Zero instead");
                assert!(hwt * 3 <= C.rank() * 2, "it does not make sense to take more than 2/3 of secret key entries in {{-1, 1}}");
                let mut result_data = (0..C.rank()).map(|_| 0).collect::<Vec<_>>();
                for _ in 0..hwt {
                    let mut i = rng.next_u32() as usize % C.rank();
                    while result_data[i] != 0 {
                        i = rng.next_u32() as usize % C.rank();
                    }
                    result_data[i] = (rng.next_u32() % 2) as i32 * 2 - 1;
                }
                return C.from_canonical_basis(result_data.into_iter().map(|c| C.base_ring().int_hom().map(c)));
            },
            SecretKeyDistribution::UniformTernary => C.from_canonical_basis((0..C.rank()).map(|_| C.base_ring().int_hom().map((rng.next_u32() % 3) as i32 - 1))),
            SecretKeyDistribution::Zero => C.zero()
        }
    }

    ///
    /// Creates an RLWE sample `(a, -as + e)`, where `s = sk` is the secret key and `a, e`
    /// are sampled using randomness from `rng`. Currently, the standard deviation of the
    /// error is fixed to `3.2`.
    /// 
    #[instrument(skip_all)]
    fn rlwe_sample<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, mut rng: R, sk: &SecretKey<Self>) -> (El<CiphertextRing<Self>>, El<CiphertextRing<Self>>) {
        let a = C.random_element(|| rng.next_u64());
        let mut b = C.negate(C.mul_ref(&a, &sk));
        let e = C.from_canonical_basis((0..C.rank()).map(|_| C.base_ring().int_hom().map((rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32)));
        C.add_assign(&mut b, e);
        return (a, b);
    }

    ///
    /// Creates a fresh encryption of zero, i.e. a ciphertext `(c0, c1) = (-as + te, a)`
    /// where `s = sk` is the given secret key. `a` and `e` are sampled using the randomness
    /// of `rng`. Currently, the standard deviation of the error is fixed to `3.2`.
    /// 
    #[instrument(skip_all)]
    fn enc_sym_zero<R: Rng + CryptoRng>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, rng: R, sk: &SecretKey<Self>) -> Ciphertext<Self> {
        let t = C.base_ring().coerce(&ZZbig, int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZbig, P.base_ring().integer_ring()));
        let (a, b) = Self::rlwe_sample(C, rng, sk);
        return Ciphertext {
            c0: C.inclusion().mul_ref_snd_map(b, &t),
            c1: C.inclusion().mul_ref_snd_map(a, &t),
            implicit_scale: P.base_ring().one()
        };
    }

    ///
    /// Creates a "transparent" encryption of zero, i.e. a ciphertext that represents zero,
    /// but does not actually hide the value - everyone can see that it is zero, without the
    /// secret key.
    /// 
    /// Mathematically, this is just the ciphertext `(c0, c1) = (0, 0)`.
    /// 
    #[instrument(skip_all)]
    fn transparent_zero(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>) -> Ciphertext<Self> {
        return Ciphertext {
            c0: C.zero(),
            c1: C.zero(),
            implicit_scale: P.base_ring().one()
        };
    }

    ///
    /// Decrypts the given ciphertext and prints it to stdout. Designed for debugging.
    /// 
    #[instrument(skip_all)]
    fn dec_println(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>, sk: &SecretKey<Self>) {
        let m = Self::dec(P, C, Self::clone_ct(P, C, ct), sk);
        println!("ciphertext (noise budget: {} / {}):", Self::noise_budget(P, C, ct, sk), ZZbig.abs_log2_ceil(C.base_ring().modulus()).unwrap());
        P.println(&m);
        println!();
    }
    
    ///
    /// Decrypts the given ciphertext and prints the values of its slots to stdout. 
    /// Designed for debugging.
    /// 
    #[instrument(skip_all)]
    fn dec_println_slots(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>, sk: &SecretKey<Self>, cache_dir: Option<&str>) {
        let ZZ = P.base_ring().integer_ring();
        let (p, _e) = is_prime_power(ZZ, P.base_ring().modulus()).unwrap();
        let hypercube = if P.number_ring().galois_group().m() % 2 == 0 {
            HypercubeStructure::default_pow2_hypercube(P.acting_galois_group(), int_cast(p, ZZbig, ZZ))
        } else {
            HypercubeStructure::halevi_shoup_hypercube(P.acting_galois_group(), int_cast(p, ZZbig, ZZ))
        };
        let H = HypercubeIsomorphism::new::<true>(&P, &hypercube, cache_dir);
        let m = Self::dec(P, C, Self::clone_ct(P, C, ct), sk);
        println!("ciphertext (noise budget: {} / {}):", Self::noise_budget(P, C, ct, sk), ZZbig.abs_log2_ceil(C.base_ring().modulus()).unwrap());
        for a in H.get_slot_values(&m) {
            H.slot_ring().println(&a);
        }
        println!();
    }

    ///
    /// Returns an encryption of the sum of the encrypted input and the given plaintext,
    /// which has already been lifted/encoded into the ciphertext ring.
    /// 
    /// When the plaintext is given as an element of `P`, use [`BGVInstantiation::hom_add_plain()`]
    /// instead. However, internally, the plaintext will be lifted into the ciphertext ring during
    /// the addition, and if this is performed in advance (via [`BGVInstantiation::encode_plain()`]),
    /// addition will be faster.
    /// 
    #[instrument(skip_all)]
    fn hom_add_plain_encoded(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<CiphertextRing<Self>>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        assert!(P.base_ring().is_unit(&ct.implicit_scale));
        let implicit_scale = C.base_ring().coerce(&ZZbig, int_cast(P.base_ring().smallest_lift(P.base_ring().clone_el(&ct.implicit_scale)), ZZbig, P.base_ring().integer_ring()));
        let result = Ciphertext {
            c0: C.add(ct.c0, C.inclusion().mul_ref_map(m, &implicit_scale)),
            c1: ct.c1,
            implicit_scale: ct.implicit_scale
        };
        assert!(P.base_ring().is_unit(&result.implicit_scale));
        return result;
    }

    ///
    /// Returns an encryption of the sum of the encrypted input and the given plaintext.
    /// 
    #[instrument(skip_all)]
    fn hom_add_plain(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        Self::hom_add_plain_encoded(P, C, &Self::encode_plain(P, C, m), ct)
    }

    ///
    /// Returns a fresh encryption of the given element, i.e. a ciphertext `(c0, c1) = (-as + te + m, a)`
    /// where `s = sk` is the given secret key. `a` and `e` are sampled using the randomness of `rng`. 
    /// Currently, the standard deviation of the error is fixed to `3.2`.
    /// 
    #[instrument(skip_all)]
    fn enc_sym<R: Rng + CryptoRng>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, rng: R, m: &El<PlaintextRing<Self>>, sk: &SecretKey<Self>) -> Ciphertext<Self> {
        Self::hom_add_plain(P, C, m, Self::enc_sym_zero(P, C, rng, sk))
    }

    ///
    /// Decrypts the given ciphertext using the given secret key.
    /// 
    #[instrument(skip_all)]
    fn dec(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: Ciphertext<Self>, sk: &SecretKey<Self>) -> El<PlaintextRing<Self>> {
        let noisy_m = C.add(ct.c0, C.mul_ref_snd(ct.c1, sk));
        let mod_t = P.base_ring().can_hom(&ZZbig).unwrap();
        return P.inclusion().mul_map(
            P.from_canonical_basis(C.wrt_canonical_basis(&noisy_m).iter().map(|x| mod_t.map(C.base_ring().smallest_lift(x)))),
            P.base_ring().invert(&ct.implicit_scale).unwrap()
        );
    }

    ///
    /// Returns an encryption of the product of the encrypted input and the given plaintext,
    /// which has already been lifted/encoded into the ciphertext ring.
    /// 
    /// When the plaintext is given as an element of `P`, use [`BGVInstantiation::hom_mul_plain()`]
    /// instead. However, internally, the plaintext will be lifted into the ciphertext ring during
    /// the multiplication, and if this is performed in advance (via [`BGVInstantiation::encode_plain()`]),
    /// multiplication will be faster.
    /// 
    #[instrument(skip_all)]
    fn hom_mul_plain_encoded(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<CiphertextRing<Self>>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        assert!(P.base_ring().is_unit(&ct.implicit_scale));
        let result = Ciphertext {
            c0: C.mul_ref_snd(ct.c0, m), 
            c1: C.mul_ref_snd(ct.c1, m),
            implicit_scale: ct.implicit_scale
        };
        assert!(P.base_ring().is_unit(&result.implicit_scale));
        return result;
    }

    ///
    /// Computes the smallest lift of the plaintext ring element to the ciphertext
    /// ring. The result can be used in [`BGVInstantiation::hom_add_plain_encoded()`]
    /// or [`BGVInstantiation::hom_mul_plain_encoded()`] to compute plaintext-ciphertext
    /// addition resp. multiplication faster.
    /// 
    #[instrument(skip_all)]
    fn encode_plain(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>) -> El<CiphertextRing<Self>> {
        let ZZi64_to_Zq = C.base_ring().can_hom(P.base_ring().integer_ring()).unwrap();
        return C.from_canonical_basis(P.wrt_canonical_basis(m).iter().map(|c| ZZi64_to_Zq.map(P.base_ring().smallest_lift(c))));
    }

    ///
    /// Returns an encryption of the product of the encrypted input and the given plaintext.
    /// 
    #[instrument(skip_all)]
    fn hom_mul_plain(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        Self::hom_mul_plain_encoded(P, C, &Self::encode_plain(P, C, m), ct)
    }

    ///
    /// Returns an encryption of the product of the encrypted input and the given plaintext.
    /// 
    #[instrument(skip_all)]
    fn hom_mul_plain_int(_P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<BigIntRing>, mut ct: Ciphertext<Self>) -> Ciphertext<Self> {
        let hom = C.inclusion().compose(C.base_ring().can_hom(&ZZbig).unwrap());
        hom.mul_assign_ref_map(&mut ct.c0, m);
        hom.mul_assign_ref_map(&mut ct.c1, m);
        return ct;
    }

    ///
    /// Converts a ciphertext into a ciphertext with `implicit_scale = 1`, but slightly
    /// larger noise. Mainly used for internal purposes.
    /// 
    fn merge_implicit_scale(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        let scale = int_cast(P.base_ring().smallest_lift(P.base_ring().invert(&ct.implicit_scale).unwrap()), ZZbig, P.base_ring().integer_ring());
        let mut result = Self::hom_mul_plain_int(P, C, &scale, ct);
        result.implicit_scale = P.base_ring().one();
        return result;
    }

    ///
    /// Copies a ciphertext.
    /// 
    #[instrument(skip_all)]
    fn clone_ct(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>) -> Ciphertext<Self> {
        assert!(P.base_ring().is_unit(&ct.implicit_scale));
        Ciphertext {
            c0: C.clone_el(&ct.c0),
            c1: C.clone_el(&ct.c1),
            implicit_scale: P.base_ring().clone_el(&ct.implicit_scale)
        }
    }

    ///
    /// Returns the value
    /// ```text
    ///   log2( q / | c0 + c1 s |_inf )
    /// ```
    /// which roughly corresponds to the "noise budget" of the ciphertext, in bits.
    /// 
    #[instrument(skip_all)]
    fn noise_budget(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>, sk: &SecretKey<Self>) -> usize {
        let ct = Self::clone_ct(P, C, ct);
        let noisy_m = C.add(ct.c0, C.mul_ref_snd(ct.c1, sk));
        let coefficients = C.wrt_canonical_basis(&noisy_m);
        let size_of_critical_quantity = <_ as Iterator>::max((0..coefficients.len()).map(|i| {
            let c = C.base_ring().smallest_lift(coefficients.at(i));
            let size = ZZbig.abs_log2_ceil(&c);
            return size.unwrap_or(0);
        })).unwrap();
        return ZZbig.abs_log2_ceil(C.base_ring().modulus()).unwrap().saturating_sub(size_of_critical_quantity + 1);
    }

    ///
    /// Generates a key-switch key, which can be used (by [`BGVInstantiation::key_switch()`]) to
    /// convert a ciphertext w.r.t. `old_sk` into a ciphertext w.r.t. `new_sk`.
    /// 
    /// Note that we use a variant of hybrid key switching, where the key-switching key
    /// does not depend on the special modulus, and can be used w.r.t. any special modulus.
    /// 
    #[instrument(skip_all)]
    fn gen_switch_key<'a, R: Rng + CryptoRng>(P: &PlaintextRing<Self>, C: &'a CiphertextRing<Self>, mut rng: R, old_sk: &SecretKey<Self>, new_sk: &SecretKey<Self>, digits: &RNSGadgetVectorDigitIndices) -> KeySwitchKey<'a, Self>
        where Self: 'a
    {
        assert_eq!(C.base_ring().len(), digits.rns_base_len());
        let mut res0 = RNSGadgetProductRhsOperand::new_with_digits(C.get_ring(), digits.to_owned());
        let mut res1 = RNSGadgetProductRhsOperand::new_with_digits(C.get_ring(), digits.to_owned());
        for digit_i in 0..digits.len() {
            let base = Self::enc_sym_zero(P, C, &mut rng, new_sk);
            let digit_range = res0.gadget_vector_digits().at(digit_i).clone();
            let factor = C.base_ring().get_ring().from_congruence((0..C.base_ring().len()).map(|i2| {
                let Fp = C.base_ring().at(i2);
                if digit_range.contains(&i2) { Fp.one() } else { Fp.zero() } 
            }));
            if !C.base_ring().is_zero(&factor) {
                let mut payload = C.clone_el(&old_sk);
                C.inclusion().mul_assign_ref_map(&mut payload, &factor);
                C.add_assign(&mut payload, base.c0);
                res0.set_rns_factor(C.get_ring(), digit_i, payload);
                res1.set_rns_factor(C.get_ring(), digit_i, base.c1);
            }
        }
        return KeySwitchKey {
            k0: res0,
            k1: res1,
            ring: PhantomData
        };
    }

    ///
    /// Converts a ciphertext w.r.t. a secret key `old_sk` to a ciphertext w.r.t. a
    /// secret key `new_sk`, where `switch_key` is a key-switching key for `old_sk` and
    /// `new_sk` (which can be generated using [`BGVInstantiation::gen_switch_key()`]).
    /// 
    /// # Hybrid key-switching
    /// 
    /// `C_special` must be the ciphertext ring w.r.t. which the key-switching key is defined.
    /// In other words, this is the ciphertext ring, with additional RNS factors corresponding
    /// to the special modulus. This can be equal to `C`, if no hybrid key-switching is used.
    /// 
    /// On a technical level, hybrid key-switching (as implemented in Fheanor) is equivalent
    /// to modulus-switching the ciphertext up to `C_special`, and modulus-switch it down after
    /// the key-switch. This decreases the noise caused by the key-switch.
    ///  
    /// Note that we use a variant of hybrid key switching, where the key-switching key
    /// does not depend on the special modulus, and can be used w.r.t. any special modulus.
    /// 
    #[instrument(skip_all)]
    fn key_switch<'a>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, C_special: &CiphertextRing<Self>, ct: Ciphertext<Self>, switch_key: &KeySwitchKey<'a, Self>) -> Ciphertext<Self>
        where Self: 'a
    {
        let special_modulus_rns_factor_indices = RNSFactorIndexList::missing_from_subset(C.base_ring(), C_special.base_ring()).unwrap();
        assert!(switch_key.k0.gadget_vector_digits() == switch_key.k1.gadget_vector_digits());

        if special_modulus_rns_factor_indices.len() == 0 {
            let op = RNSGadgetProductLhsOperand::from_element_with(C.get_ring(), &ct.c1, switch_key.k0.gadget_vector_digits());
            return Ciphertext {
                c0: C.add_ref_snd(ct.c0, &op.gadget_product(&switch_key.k0, C.get_ring())),
                c1: op.gadget_product(&switch_key.k1, C.get_ring()),
                implicit_scale: ct.implicit_scale
            };
        } else {
            let special_modulus = ZZbig.prod(special_modulus_rns_factor_indices.iter().map(|i| int_cast(*C_special.base_ring().at(*i).modulus(), ZZbig, ZZi64)));
            let special_modulus = C_special.base_ring().coerce(&ZZbig, special_modulus);
            let mut ct1_modswitched = C_special.get_ring().add_rns_factor_element(C.get_ring(), &special_modulus_rns_factor_indices, &ct.c1);
            C_special.inclusion().mul_assign_map(&mut ct1_modswitched, special_modulus);
            
            let op = RNSGadgetProductLhsOperand::from_element_with(
                C_special.get_ring(), 
                &ct1_modswitched, 
                switch_key.gadget_vector_digits(),
            );
            // we cheat regarding the implicit scale; since the scaling up and down later exactly
            // cancel out any changes to the implicit scale, we just temporarily set it to 1 and later
            // overwrite it with the original implicit scale
            let switched = Ciphertext {
                c0: op.gadget_product(&switch_key.k0, C_special.get_ring()),
                c1: op.gadget_product(&switch_key.k1, C_special.get_ring()),
                implicit_scale: P.base_ring().one()
            };
            let mut result = Self::mod_switch_ct(P, C, C_special, switched);
            C.add_assign(&mut result.c0, ct.c0);
            result.implicit_scale = ct.implicit_scale;
            return result;
        }
    }

    ///
    /// Generates a relinearization key, necessary to compute homomorphic multiplications.
    /// 
    /// Note that we use a variant of hybrid key switching, where the relinearization key
    /// does not depend on the special modulus, and can be used w.r.t. any special modulus.
    /// 
    #[instrument(skip_all)]
    fn gen_rk<'a, R: Rng + CryptoRng>(P: &PlaintextRing<Self>, C: &'a CiphertextRing<Self>, rng: R, sk: &SecretKey<Self>, digits: &RNSGadgetVectorDigitIndices) -> RelinKey<'a, Self>
        where Self: 'a
    {
        Self::gen_switch_key(P, C, rng, &C.pow(C.clone_el(sk), 2), sk, digits)
    }

    ///
    /// Computes an encryption of the product of two encrypted inputs.
    /// 
    /// Since Fheanor does not (at least not implicitly) perform automatic modulus management,
    /// it is necessary to modulus-switch between calls to `hom_mul()` in order to prevent
    /// `hom_mul()` from causing exponential noise growth. For more info on modulus-switching
    /// and the modulus chain, see [`crate::examples::bgv_basics`].
    /// 
    /// `C_special` must be the ciphertext ring w.r.t. which the relinearization key is defined.
    /// In other words, this is the ciphertext ring, with additional RNS factors corresponding
    /// to the special modulus. This can be equal to `C`, if no hybrid key-switching is used.
    /// For more details, see [`BGVInstantiation::key_switch()`].
    /// 
    #[instrument(skip_all)]
    fn hom_mul<'a>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, C_special: &CiphertextRing<Self>, lhs: Ciphertext<Self>, rhs: Ciphertext<Self>, rk: &RelinKey<'a, Self>) -> Ciphertext<Self>
        where Self: 'a
    {
        assert!(P.base_ring().is_unit(&lhs.implicit_scale));
        assert!(P.base_ring().is_unit(&rhs.implicit_scale));

        let [res0, res1, res2] = C.get_ring().two_by_two_convolution([&lhs.c0, &lhs.c1], [&rhs.c0, &rhs.c1]);
        
        let mut result = Self::key_switch(P, C, C_special, Ciphertext {
            c0: C.zero(),
            c1: res2,
            implicit_scale: P.base_ring().mul(lhs.implicit_scale, rhs.implicit_scale)
        }, rk);
        C.add_assign(&mut result.c0, res0);
        C.add_assign(&mut result.c1, res1);
        assert!(P.base_ring().is_unit(&result.implicit_scale));
        return result;
    }
    
    ///
    /// Computes an encryption of the square of an encrypted input.
    /// 
    /// Since Fheanor does not (at least not implicitly) perform automatic modulus management,
    /// it is necessary to modulus-switch between calls to `hom_square()` in order to prevent
    /// `hom_square()` from causing exponential noise growth. For more info on modulus-switching
    /// and the modulus chain, see [`crate::examples::bgv_basics`].
    ///  
    /// `C_special` must be the ciphertext ring w.r.t. which the relinearization key is defined.
    /// In other words, this is the ciphertext ring, with additional RNS factors corresponding
    /// to the special modulus. This can be equal to `C`, if no hybrid key-switching is used.
    /// For more details, see [`BGVInstantiation::key_switch()`].
    /// 
    #[instrument(skip_all)]
    fn hom_square<'a>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, C_special: &CiphertextRing<Self>, val: Ciphertext<Self>, rk: &RelinKey<'a, Self>) -> Ciphertext<Self>
        where Self: 'a
    {
        assert!(P.base_ring().is_unit(&val.implicit_scale));

        let [res0, res1, res2] = C.get_ring().two_by_two_convolution([&val.c0, &val.c1], [&val.c0, &val.c1]);
                
        let mut result = Self::key_switch(P, C, C_special, Ciphertext {
            c0: C.zero(),
            c1: res2,
            implicit_scale: P.base_ring().pow(val.implicit_scale, 2)
        }, rk);
        C.add_assign(&mut result.c0, res0);
        C.add_assign(&mut result.c1, res1);
        assert!(P.base_ring().is_unit(&result.implicit_scale));
        return result;
    }
    
    ///
    /// Computes an encryption of the sum of two encrypted inputs.
    /// 
    #[instrument(skip_all)]
    fn hom_add(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, mut lhs: Ciphertext<Self>, mut rhs: Ciphertext<Self>) -> Ciphertext<Self> {
        assert!(P.base_ring().is_unit(&lhs.implicit_scale));
        assert!(P.base_ring().is_unit(&rhs.implicit_scale));

        let Zt = P.base_ring();
        let (a, b) = equalize_implicit_scale(Zt, Zt.checked_div(&lhs.implicit_scale, &rhs.implicit_scale).unwrap());

        debug_assert!(!Zt.eq_el(&lhs.implicit_scale, &rhs.implicit_scale) || Zt.integer_ring().is_one(&a) && Zt.integer_ring().is_one(&b));
        let ZZ_to_C = C.inclusion().compose(C.base_ring().can_hom(Zt.integer_ring()).unwrap());
        let ZZ_to_Zt = P.base_ring().can_hom(Zt.integer_ring()).unwrap();
        if !Zt.integer_ring().is_one(&a) {
            ZZ_to_C.mul_assign_ref_map(&mut rhs.c0, &a);
            ZZ_to_C.mul_assign_ref_map(&mut rhs.c1, &a);
            ZZ_to_Zt.mul_assign_map(&mut rhs.implicit_scale, a);
        }
        if !Zt.integer_ring().is_one(&b) {
            ZZ_to_C.mul_assign_ref_map(&mut lhs.c0, &b);
            ZZ_to_C.mul_assign_ref_map(&mut lhs.c1, &b);
            ZZ_to_Zt.mul_assign_map(&mut lhs.implicit_scale, b);
        }

        debug_assert!(Zt.eq_el(&lhs.implicit_scale, &rhs.implicit_scale));
        let result = Ciphertext {
            c0: C.add(lhs.c0, rhs.c0),
            c1: C.add(lhs.c1, rhs.c1),
            implicit_scale: lhs.implicit_scale
        };
        assert!(P.base_ring().is_unit(&result.implicit_scale));
        return result;
    }

    ///
    /// Computes an encryption of the difference of two encrypted inputs.
    /// 
    fn hom_sub(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, lhs: Ciphertext<Self>, rhs: Ciphertext<Self>) -> Ciphertext<Self> {
        Self::hom_add(P, C, lhs, Ciphertext { c0: rhs.c0, c1: rhs.c1, implicit_scale: P.base_ring().negate(rhs.implicit_scale) })
    }
    
    ///
    /// Computes an encryption of `sigma(x)`, where `x` is the message encrypted by the given ciphertext
    /// and `sigma` is the given Galois automorphism.
    ///  
    /// `C_special` must be the ciphertext ring w.r.t. which the Galois key is defined.
    /// In other words, this is the ciphertext ring, with additional RNS factors corresponding
    /// to the special modulus. This can be equal to `C`, if no hybrid key-switching is used.
    /// For more details, see [`BGVInstantiation::key_switch()`].
    /// 
    #[instrument(skip_all)]
    fn hom_galois<'a>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, C_special: &CiphertextRing<Self>, ct: Ciphertext<Self>, g: &GaloisGroupEl, gk: &KeySwitchKey<'a, Self>) -> Ciphertext<Self>
        where Self: 'a
    {
        Self::key_switch(P, C, C_special, Ciphertext {
            c0: C.get_ring().apply_galois_action(&ct.c0, g),
            c1: C.get_ring().apply_galois_action(&ct.c1, g),
            implicit_scale: ct.implicit_scale
        }, gk)
    }

    ///
    /// Homomorphically applies multiple Galois automorphisms at once.
    /// Functionally, this is equivalent to calling [`BGVInstantiation::hom_galois()`]
    /// multiple times, but can be faster.
    ///  
    /// `C_special` must be the ciphertext ring w.r.t. which all the Galois key are defined.
    /// In other words, this is the ciphertext ring, with additional RNS factors corresponding
    /// to the special modulus. This can be equal to `C`, if no hybrid key-switching is used.
    /// For more details, see [`BGVInstantiation::key_switch()`].
    /// 
    #[instrument(skip_all)]
    fn hom_galois_many<'a, 'b, V>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, C_special: &CiphertextRing<Self>, ct: Ciphertext<Self>, gs: &[GaloisGroupEl], gks: V) -> Vec<Ciphertext<Self>>
        where V: VectorFn<&'b KeySwitchKey<'a, Self>>,
            KeySwitchKey<'a, Self>: 'b,
            'a: 'b,
            Self: 'a
    {
        assert!(P.base_ring().is_unit(&ct.implicit_scale));
        assert_eq!(gs.len(), gks.len());
        if gs.len() == 0 {
            return Vec::new();
        }
        let special_modulus_rns_factor_indices = RNSFactorIndexList::missing_from_subset(C.base_ring(), C_special.base_ring()).unwrap();

        let digits = gks.at(0).k0.gadget_vector_digits();
        let has_same_digits = |gk: &RNSGadgetProductRhsOperand<_>| gk.gadget_vector_digits().len() == digits.len() && gk.gadget_vector_digits().iter().zip(digits.iter()).all(|(l, r)| l == r);
        assert!(gks.iter().all(|gk| has_same_digits(&gk.k0) && has_same_digits(&gk.k1)), "hom_galois_many() requires all Galois keys to use the same parameters");

        let c1_op = if special_modulus_rns_factor_indices.len() == 0 {
            RNSGadgetProductLhsOperand::from_element_with(
                C.get_ring(), 
                &ct.c1, 
                &digits
            )
        } else {
            let special_modulus = ZZbig.prod(special_modulus_rns_factor_indices.iter().map(|i| int_cast(*C_special.base_ring().at(*i).modulus(), ZZbig, ZZi64)));
            let special_modulus = C_special.base_ring().coerce(&ZZbig, special_modulus);
            let mut ct1_modswitched = C_special.get_ring().add_rns_factor_element(C.get_ring(), &special_modulus_rns_factor_indices, &ct.c1);
            C_special.inclusion().mul_assign_map(&mut ct1_modswitched, special_modulus);
            RNSGadgetProductLhsOperand::from_element_with(
                C_special.get_ring(), 
                &ct1_modswitched, 
                &digits
            )
        };
        let c1_op_gs = c1_op.apply_galois_action_many(C_special.get_ring(), gs);
        let c0_gs = C.get_ring().apply_galois_action_many(&ct.c0, gs).into_iter();
        assert_eq!(gks.len(), c1_op_gs.len());
        assert_eq!(gks.len(), c0_gs.len());
        return c0_gs.zip(c1_op_gs.iter()).enumerate().map(|(i, (c0_g, c1_g))| if special_modulus_rns_factor_indices.len() == 0 {
            return Ciphertext {
                c0: C.add_ref_snd(c0_g, &c1_g.gadget_product(&gks.at(i).k0, C.get_ring())),
                c1: c1_g.gadget_product(&gks.at(i).k1, C.get_ring()),
                implicit_scale: P.base_ring().clone_el(&ct.implicit_scale)
            };
        } else {
            // we cheat regarding the implicit scale; since the scaling up and down later exactly
            // cancel out any changes to the implicit scale, we just temporarily set it to 1 and later
            // overwrite it with the original implicit scale
            let switched = Ciphertext {
                c0: c1_g.gadget_product(&gks.at(i).k0, C_special.get_ring()),
                c1: c1_g.gadget_product(&gks.at(i).k1, C_special.get_ring()),
                implicit_scale: P.base_ring().one()
            };
            let mut result = Self::mod_switch_ct(P, C, C_special, switched);
            C.add_assign(&mut result.c0, c0_g);
            result.implicit_scale = P.base_ring().clone_el(&ct.implicit_scale);
            return result;
        }).collect();
    }

    ///
    /// Given `R/qR` this creates the ciphertext ring `R/q'R`, where the RNS base for `q'`
    /// is derived from the RNS base of `q` by removing the RNS factors whose indices are mentioned
    /// in `drop_moduli`.
    /// 
    /// Note that for the implementation in Fheanor at least, the underlying rings will share
    /// most of their data, which means that this function is actually very cheap, in particular
    /// much cheaper than creating a new ciphertext ring (e.g. using [`BGVInstantiation::create_ciphertext_ring()`]).
    /// 
    #[instrument(skip_all)]
    fn mod_switch_down_C(C: &CiphertextRing<Self>, drop_moduli: &RNSFactorIndexList) -> CiphertextRing<Self> {
        RingValue::from(C.get_ring().drop_rns_factor(&drop_moduli))
    }

    ///
    /// Modulus-switches a secret key in a way compatible with modulus-switching ciphertexts.
    ///  
    /// More concretely, this function computes the smallest lift of the given secret key
    /// to the number ring, reduced modulo the modulus of `Cnew`. This secret key can successfully
    /// decrypt ciphertexts obtained via [`BGVInstantiation::mod_switch_ct()`].
    /// 
    #[instrument(skip_all)]
    fn mod_switch_sk(Cnew: &CiphertextRing<Self>, Cold: &CiphertextRing<Self>, sk: &SecretKey<Self>) -> SecretKey<Self> {
        if let Ok(dropped_factors) = RNSFactorIndexList::missing_from_subset(Cnew.base_ring(), Cold.base_ring()) {
            return Cnew.get_ring().drop_rns_factor_element(Cold.get_ring(), &dropped_factors, sk);
        } else {
            let mod_switch = UsedBaseConversion::new_with_alloc(
                Cold.base_ring().as_iter().cloned().collect(),
                Cnew.base_ring().as_iter().cloned().collect(),
                Global
            );
            assert!(Cold.base_ring().as_iter().zip(mod_switch.input_rings()).all(|(l, r)| l.get_ring() == r.get_ring()));
            assert!(Cnew.base_ring().as_iter().zip(mod_switch.output_rings()).all(|(l, r)| l.get_ring() == r.get_ring()));
            return perform_rns_op(Cnew.get_ring(), Cold.get_ring(), sk, &mod_switch);
        }
    }

    ///
    /// Modulus-switches a relinearization key in a way compatible with modulus-switching ciphertexts.
    /// 
    /// This is equivalent to creating a new relinearization key (using [`BGVInstantiation::gen_rk()`])
    /// over `Cnew` for the secret key `mod_switch_sk(Cnew, Cold, drop_moduli, sk)`, but does not require
    /// access to `sk`. Currently, this function only supports decreasing the ciphertext modulus, by dropping
    /// RNS factors.
    /// 
    #[instrument(skip_all)]
    fn mod_switch_down_rk<'a, 'b>(Cnew: &'b CiphertextRing<Self>, Cold: &CiphertextRing<Self>, rk: &RelinKey<'a, Self>) -> RelinKey<'b, Self> {
        let drop_moduli = RNSFactorIndexList::missing_from_subset(Cnew.base_ring(), Cold.base_ring()).unwrap();
        if drop_moduli.len() == 0 {
            KeySwitchKey {
                k0: rk.k0.clone(Cnew.get_ring()),
                k1: rk.k1.clone(Cnew.get_ring()),
                ring: PhantomData
            }
        } else {
            KeySwitchKey {
                k0: rk.k0.clone(Cold.get_ring()).modulus_switch(Cnew.get_ring(), &drop_moduli, Cold.get_ring()), 
                k1: rk.k1.clone(Cold.get_ring()).modulus_switch(Cnew.get_ring(), &drop_moduli, Cold.get_ring()), 
                ring: PhantomData
            }
        }
    }

    ///
    /// Modulus-switches a Galois key in a way compatible with modulus-switching ciphertexts.
    /// 
    /// This is equivalent to creating a new Galois key (using [`BGVInstantiation::gen_gk()`])
    /// over `Cnew` for the secret key `mod_switch_down_sk(Cnew, Cold, drop_moduli, sk)`, but does not require
    /// access to `sk`. Currently, this function only supports decreasing the ciphertext modulus, by dropping
    /// RNS factors.
    /// 
    #[instrument(skip_all)]
    fn mod_switch_down_gk<'a, 'b>(Cnew: &'b CiphertextRing<Self>, Cold: &CiphertextRing<Self>, gk: &KeySwitchKey<'a, Self>) -> KeySwitchKey<'b, Self> {
        Self::mod_switch_down_rk(Cnew, Cold, gk)
    }

    ///
    /// Internal function to compute how the implicit scale of a ciphertext changes
    /// once we modulus-switch it.
    /// 
    fn mod_switch_compute_implicit_scale_factor(P: &PlaintextRing<Self>, q_new: &El<BigIntRing>, q_old: &El<BigIntRing>) -> <Self::PlaintextZnRing as RingBase>::Element {
        let ZZbig_to_Zt = P.base_ring().can_hom(&ZZbig).unwrap();
        let result = P.base_ring().checked_div(
            &ZZbig_to_Zt.map_ref(q_new),
            &ZZbig_to_Zt.map_ref(q_old)
        ).unwrap();
        assert!(P.base_ring().is_unit(&result));
        return result;
    }

    fn rescale_ring_element<'a>(P: &'a PlaintextRing<Self>, Cnew: &'a CiphertextRing<Self>, Cold: &'a CiphertextRing<Self>) -> Box<dyn 'a + FnMut(El<CiphertextRing<Self>>) -> El<CiphertextRing<Self>>> {
        let added_rns_factors = RNSFactorIndexList::missing_from(Cold.base_ring(), Cnew.base_ring());
        let dropped_rns_factors = RNSFactorIndexList::missing_from(Cnew.base_ring(), Cold.base_ring());
        let kept_rns_factors = dropped_rns_factors.complement(Cold.base_ring().len());
        let a = Cold.base_ring().coerce(&ZZbig, ZZbig.prod(added_rns_factors.iter().map(|i| int_cast(*Cnew.base_ring().at(*i).modulus(), ZZbig, ZZi64))));

        let map_kept_factors = move |x| Cnew.get_ring().collect_rns_factors((0..Cnew.base_ring().len()).map(|idx| if added_rns_factors.contains(idx) {
            RNSFactorCongruence::Zero
        } else {
            let old_idx = Cold.base_ring().as_iter().enumerate().filter(|(_, old_ring)| old_ring.get_ring() == Cnew.base_ring().at(idx).get_ring()).next().unwrap().0;
            RNSFactorCongruence::CongruentTo(Cold.get_ring(), old_idx, &x)
        }));

        if kept_rns_factors.len() == Cold.base_ring().len() {
            if kept_rns_factors.len() == Cnew.base_ring().len() {
                return Box::new(identity);
            } else {
                return Box::new(move |mut x: El<CiphertextRing<Self>>| {
                    Cold.inclusion().mul_assign_ref_map(&mut x, &a);
                    return map_kept_factors(x);
                });
            }
        }

        let C_dropped = RingValue::from(Cold.get_ring().drop_rns_factor(&kept_rns_factors));
        let Zt = Zn::new(int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZi64, P.base_ring().integer_ring()) as u64);
        let compute_delta = CongruencePreservingAlmostExactBaseConversion::new_with_alloc(
            C_dropped.base_ring().as_iter().cloned().collect(),
            Cnew.base_ring().as_iter().cloned().collect(),
            Zt,
            Global
        );
        let b_inv = Cnew.base_ring().invert(&Cnew.base_ring().coerce(&ZZbig, ZZbig.prod(dropped_rns_factors.iter().map(|i| int_cast(*Cold.base_ring().at(*i).modulus(), ZZbig, ZZi64))))).unwrap();
        Box::new(move |mut x: El<CiphertextRing<Self>>| {
            Cold.inclusion().mul_assign_ref_map(&mut x, &a);

            let x_dropped = C_dropped.get_ring().drop_rns_factor_element(Cold.get_ring(), &kept_rns_factors, &x);
            let mut x_dropped_matrix = OwnedMatrix::zero(C_dropped.base_ring().len(), Cold.get_ring().small_generating_set_len(), Cold.base_ring().at(0));
            C_dropped.get_ring().as_representation_wrt_small_generating_set(&x_dropped, x_dropped_matrix.data_mut());
            let mut delta = OwnedMatrix::zero(Cnew.base_ring().len(), Cnew.get_ring().small_generating_set_len(), Cnew.base_ring().at(0));
            compute_delta.apply(x_dropped_matrix.data(), delta.data_mut());
            let delta = Cnew.get_ring().from_representation_wrt_small_generating_set(delta.data());

            return Cnew.inclusion().mul_ref_snd_map(
                Cnew.sub(map_kept_factors(x), delta),
                &b_inv
            );
        })
    }

    ///
    /// Modulus-switches a ciphertext.
    /// 
    /// More concretely, this function computes a valid ciphertext w.r.t. `Cnew` that
    /// encrypts the same message as the input ciphertext w.r.t. `Cold` (w.r.t. the same
    /// secret key, or rather a modulus-switched variant of the secret key, via
    /// [`BGVInstantiation::mod_switch_sk()`]).
    /// 
    #[instrument(skip_all)]
    fn mod_switch_ct(P: &PlaintextRing<Self>, Cnew: &CiphertextRing<Self>, Cold: &CiphertextRing<Self>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        assert!(P.base_ring().is_unit(&ct.implicit_scale));
        let mut rescale = Self::rescale_ring_element(P, Cnew, Cold);
        let result = Ciphertext {
            c0: rescale(ct.c0),
            c1: rescale(ct.c1),
            implicit_scale: P.base_ring().mul(ct.implicit_scale, Self::mod_switch_compute_implicit_scale_factor(P, Cnew.base_ring().modulus(), Cold.base_ring().modulus()))
        };
        assert!(P.base_ring().is_unit(&result.implicit_scale));
        return result;
    }

    ///
    /// Generates a Galois key, usable for homomorphically applying Galois automorphisms.
    /// 
    /// Note that we use a variant of hybrid key switching, where the Galois key
    /// does not depend on the special modulus, and can be used w.r.t. any special modulus.
    /// 
    #[instrument(skip_all)]
    fn gen_gk<'a, R: Rng + CryptoRng>(P: &PlaintextRing<Self>, C: &'a CiphertextRing<Self>, rng: R, sk: &SecretKey<Self>, g: &GaloisGroupEl, digits: &RNSGadgetVectorDigitIndices) -> KeySwitchKey<'a, Self>
        where Self: 'a
    {
        Self::gen_switch_key(P, C, rng, &C.get_ring().apply_galois_action(sk, g), sk, digits)
    }

    ///
    /// Converts an encrypted value `m` w.r.t. a plaintext modulus `t` to an encryption of `t' m / t` w.r.t.
    /// a plaintext modulus `t'`. This requires that `t' m / t` is an integral ring element (i.e. `t` divides
    /// `t' m`), otherwise this function will cause immediate noise overflow.
    /// 
    #[instrument(skip_all)]
    fn change_plaintext_modulus(Pnew: &PlaintextRing<Self>, Pold: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        assert!(Pold.base_ring().is_unit(&ct.implicit_scale));
        assert!(Pold.base_ring().integer_ring().get_ring() == Pnew.base_ring().integer_ring().get_ring());

        let ZZ_to_Cbase = C.base_ring().can_hom(Pold.base_ring().integer_ring()).unwrap();
        let x = C.base_ring().checked_div(
            &ZZ_to_Cbase.map_ref(Pnew.base_ring().modulus()),
            &ZZ_to_Cbase.map_ref(Pold.base_ring().modulus()),
        ).unwrap();
        let new_implicit_scale = Pnew.base_ring().coerce(Pnew.base_ring().integer_ring(), Pold.base_ring().smallest_positive_lift(ct.implicit_scale));
        let result = Ciphertext {
            c0: C.inclusion().mul_ref_snd_map(ct.c0, &x),
            c1: C.inclusion().mul_ref_snd_map(ct.c1, &x),
            implicit_scale: new_implicit_scale
        };
        assert!(Pnew.base_ring().is_unit(&result.implicit_scale));
        return result;
    }

    ///
    /// Creates an encryption of the secret key.
    /// 
    /// Note that this does not require access to the secret key.
    /// 
    #[instrument(skip_all)]
    fn enc_sk(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>) -> Ciphertext<Self> {
        Ciphertext {
            c0: C.zero(),
            c1: C.one(),
            implicit_scale: P.base_ring().one()
        }
    }

    ///
    /// Modulus-switches from `R/qR` to `R/t'R`, where the latter one is given as a plaintext ring `target`.
    /// In particular, this is necessary during bootstrapping.
    /// 
    /// As opposed to BFV however, the modulus `t'` of `target` must be coprime with the
    /// current plaintext modulus `t`.
    /// 
    #[instrument(skip_all)]
    fn mod_switch_to_plaintext(P: &PlaintextRing<Self>, target: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: Ciphertext<Self>) -> (El<PlaintextRing<Self>>, El<PlaintextRing<Self>>) {
        let ZZ = P.base_ring().integer_ring();
        assert!(ZZ.get_ring() == target.base_ring().integer_ring().get_ring());
        assert!(ZZ.is_one(&signed_gcd(ZZ.clone_el(P.base_ring().modulus()), ZZ.clone_el(target.base_ring().modulus()), ZZ)), "can only mod-switch to ciphertext moduli that are coprime to t");
        assert!(P.base_ring().is_unit(&ct.implicit_scale));

        // this is not very performance-critical, so implement it using big integers
        let t_target = int_cast(target.base_ring().integer_ring().clone_el(target.base_ring().modulus()), ZZbig, target.base_ring().integer_ring());
        let to_Pbase = P.base_ring().can_hom(&ZZbig).unwrap();
        let to_target_base = target.base_ring().can_hom(&ZZbig).unwrap();
        let factor = P.base_ring().checked_div(&to_Pbase.map_ref(&t_target), &to_Pbase.map_ref(C.base_ring().modulus())).unwrap();
        let rescale = |x| target.from_canonical_basis(C.wrt_canonical_basis(x).iter().map(|a| {
            let lift_a = C.base_ring().smallest_lift(a);
            let scaled_a = ZZbig.rounded_div(ZZbig.mul_ref(&lift_a, &t_target), C.base_ring().modulus());
            to_target_base.map(ZZbig.add_ref_fst(
                &scaled_a,
                int_cast(P.base_ring().smallest_lift(P.base_ring().sub(
                    to_Pbase.mul_ref_fst_map(&factor, lift_a),
                    to_Pbase.map_ref(&scaled_a)
                )), ZZbig, ZZ)
            ))
        }));
        let factor = P.base_ring().smallest_lift(P.base_ring().invert(&P.base_ring().mul(
            ct.implicit_scale,
            Self::mod_switch_compute_implicit_scale_factor(P, &int_cast(ZZ.clone_el(target.base_ring().modulus()), ZZbig, ZZ), C.base_ring().modulus())
        )).unwrap());
        let ZZ_to_C = C.inclusion().compose(C.base_ring().can_hom(ZZ).unwrap());
        let c0 = ZZ_to_C.mul_ref_snd_map(ct.c0, &factor);
        let c1 = ZZ_to_C.mul_map(ct.c1, factor);
        return (rescale(&c0), rescale(&c1));
    }
}

#[derive(Debug)]
pub struct Pow2BGV<A: Allocator + Clone  = DefaultCiphertextAllocator, C: FheanorNegacyclicNTT<Zn> = DefaultNegacyclicNTT> {
    number_ring: Pow2CyclotomicNumberRing<C>,
    ciphertext_allocator: A,
    negacyclic_ntt: PhantomData<C>
}

impl Pow2BGV {

    pub fn new(m: usize) -> Self {
        Self::new_with_ntt(m, DefaultCiphertextAllocator::default())
    }
}

impl<A: Allocator + Clone, C: FheanorNegacyclicNTT<Zn>> Pow2BGV<A, C> {

    #[instrument(skip_all)]
    pub fn new_with_ntt(m: usize, alloc: A) -> Self {
        return Self {
            number_ring: Pow2CyclotomicNumberRing::new_with_ntt(m as u64),
            ciphertext_allocator: alloc,
            negacyclic_ntt: PhantomData::<C>
        }
    }
}

impl<A: Allocator + Clone , C: FheanorNegacyclicNTT<Zn>> Clone for Pow2BGV<A, C> {

    fn clone(&self) -> Self {
        Self {
            number_ring: self.number_ring.clone(),
            ciphertext_allocator: self.ciphertext_allocator.clone(),
            negacyclic_ntt: PhantomData
        }
    }
}

impl<A: Allocator + Clone , C: FheanorNegacyclicNTT<Zn>> Display for Pow2BGV<A, C> {

    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BGV({:?})", self.number_ring)
    }
}

impl<A: Allocator + Clone , C: FheanorNegacyclicNTT<Zn>> BGVInstantiation for Pow2BGV<A, C> {

    type NumberRing = Pow2CyclotomicNumberRing<C>;
    type CiphertextRing = DoubleRNSRingBase<Pow2CyclotomicNumberRing<C>, A>;
    type PlaintextZnRing = ZnBase;
    type PlaintextRing = NumberRingQuotientByIntBase<Pow2CyclotomicNumberRing<C>, Zn, A>;

    fn number_ring(&self) -> &Pow2CyclotomicNumberRing<C> {
        &self.number_ring
    }

    #[instrument(skip_all)]
    fn create_plaintext_ring(&self, modulus: El<BigIntRing>) -> PlaintextRing<Self> {
        if ZZbig.is_gt(&modulus, &ZZbig.power_of_two(SAMPLE_PRIMES_SIZE - 2)) {
            unimplemented!("Plaintext modulus greater than 2^{} are not yet supported for BGV", SAMPLE_PRIMES_SIZE - 2)
        }
        NumberRingQuotientByIntBase::create(self.number_ring().clone(), Zn::new(int_cast(modulus, ZZi64, ZZbig) as u64), self.ciphertext_allocator.clone(), STANDARD_CONVOLUTION)
    }

    #[instrument(skip_all)]
    fn enc_sym_zero<R: Rng + CryptoRng>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, rng: R, sk: &SecretKey<Self>) -> Ciphertext<Self> {
        assert!(ZZbig.is_one(&signed_gcd(ZZbig.clone_el(C.base_ring().modulus()), int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZbig, P.base_ring().integer_ring()), ZZbig)));
        let t = C.base_ring().coerce(&ZZi64, *P.base_ring().modulus());
        let (a, b) = Self::rlwe_sample(C, rng, sk);
        let result = Ciphertext {
            c0: C.inclusion().mul_ref_snd_map(b, &t),
            c1: C.inclusion().mul_ref_snd_map(a, &t),
            implicit_scale: P.base_ring().one()
        };
        return result;
    }

    #[instrument(skip_all)]
    fn create_rns_base(&self, log2_q: Range<usize>) -> zn_rns::Zn<Zn, BigIntRing> {
        let number_ring = self.number_ring();
        let required_root_of_unity = number_ring.mod_p_required_root_of_unity() as i64;
        let mut rns_base = sample_primes(
            log2_q.start, 
            log2_q.end, 
            SAMPLE_PRIMES_SIZE, 
            |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64))
        ).unwrap();
        rns_base.sort_unstable_by(|l, r| ZZbig.cmp(l, r));
        return zn_rns::Zn::new(rns_base.into_iter().map(|p| Zn::new(int_cast(p, ZZi64, ZZbig) as u64)).collect(), ZZbig);
    }

    #[instrument(skip_all)]
    fn create_ciphertext_ring_with_rns_base(&self, rns_base: zn_rns::Zn<Zn, BigIntRing>) -> CiphertextRing<Self> {
        return DoubleRNSRingBase::new_with_alloc(
            self.number_ring().clone(),
            rns_base,
            self.ciphertext_allocator.clone()
        );
    }

    #[instrument(skip_all)]
    fn encode_plain(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>) -> El<CiphertextRing<Self>> {
        let ZZi64_to_Zq = C.base_ring().can_hom(P.base_ring().integer_ring()).unwrap();
        let result = C.from_canonical_basis(P.wrt_canonical_basis(m).iter().map(|c| ZZi64_to_Zq.map(P.base_ring().smallest_lift(c))));
        return result;
    }
}

#[derive(Clone, Debug)]
pub struct CompositeBGV<A: Allocator + Clone  = DefaultCiphertextAllocator> {
    number_ring: CompositeCyclotomicNumberRing,
    ciphertext_allocator: A
}

impl<A: Allocator + Clone > Display for CompositeBGV<A> {

    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BGV({:?})", self.number_ring)
    }
}

impl CompositeBGV {

    pub fn new(m1: usize, m2: usize) -> Self {
        Self::new_with_alloc(m1, m2, DefaultCiphertextAllocator::default())
    }
}

impl<A: Allocator + Clone > CompositeBGV<A> {

    #[instrument(skip_all)]
    pub fn new_with_alloc(m1: usize, m2: usize, alloc: A) -> Self {
        return Self {
            number_ring: CompositeCyclotomicNumberRing::new(m1, m2),
            ciphertext_allocator: alloc,
        }
    }
}

impl<A: Allocator + Clone > BGVInstantiation for CompositeBGV<A> {

    type NumberRing = CompositeCyclotomicNumberRing;
    type CiphertextRing = ManagedDoubleRNSRingBase<CompositeCyclotomicNumberRing, A>;
    type PlaintextRing = NumberRingQuotientByIntBase<CompositeCyclotomicNumberRing, Zn, A>;
    type PlaintextZnRing = ZnBase;

    #[instrument(skip_all)]
    fn create_plaintext_ring(&self, modulus: El<BigIntRing>) -> PlaintextRing<Self> {
        if ZZbig.is_gt(&modulus, &ZZbig.power_of_two(SAMPLE_PRIMES_SIZE - 2)) {
            unimplemented!("Plaintext modulus greater than 2^{} are not yet supported for BGV", SAMPLE_PRIMES_SIZE - 2)
        }
        NumberRingQuotientByIntBase::create(self.number_ring().clone(), Zn::new(int_cast(modulus, ZZi64, ZZbig) as u64), self.ciphertext_allocator.clone(), STANDARD_CONVOLUTION)
    }

    #[instrument(skip_all)]
    fn enc_sym_zero<R: Rng + CryptoRng>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, rng: R, sk: &SecretKey<Self>) -> Ciphertext<Self> {
        let t = C.base_ring().coerce(&ZZi64, *P.base_ring().modulus());
        let (a, b) = Self::rlwe_sample(C, rng, sk);
        let result = Ciphertext {
            c0: force_double_rns_repr::<Self, _, _>(C, C.inclusion().mul_ref_snd_map(b, &t)),
            c1: force_double_rns_repr::<Self, _, _>(C, C.inclusion().mul_ref_snd_map(a, &t)),
            implicit_scale: P.base_ring().one()
        };
        return result;
    }

    fn number_ring(&self) -> &CompositeCyclotomicNumberRing {
        &self.number_ring
    }

    #[instrument(skip_all)]
    fn create_rns_base(&self, log2_q: Range<usize>) -> zn_rns::Zn<Zn, BigIntRing> {
        let number_ring = self.number_ring();
        let required_root_of_unity = number_ring.mod_p_required_root_of_unity() as i64;
        let mut rns_base = sample_primes(
            log2_q.start, 
            log2_q.end, 
            SAMPLE_PRIMES_SIZE, 
            |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64))
        ).unwrap();
        rns_base.sort_unstable_by(|l, r| ZZbig.cmp(l, r));
        return zn_rns::Zn::new(rns_base.into_iter().map(|p| Zn::new(int_cast(p, ZZi64, ZZbig) as u64)).collect(), ZZbig);
    }

    #[instrument(skip_all)]
    fn create_ciphertext_ring_with_rns_base(&self, rns_base: zn_rns::Zn<Zn, BigIntRing>) -> CiphertextRing<Self> {
        return ManagedDoubleRNSRingBase::new_with_alloc(
            self.number_ring().clone(),
            rns_base,
            self.ciphertext_allocator.clone()
        );
    }

    #[instrument(skip_all)]
    fn encode_plain(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>) -> El<CiphertextRing<Self>> {
        let ZZi64_to_Zq = C.base_ring().can_hom(P.base_ring().integer_ring()).unwrap();
        let result = C.from_canonical_basis(P.wrt_canonical_basis(m).iter().map(|c| ZZi64_to_Zq.map(P.base_ring().smallest_lift(c))));
        return C.get_ring().to_doublerns(&result).map(|x| C.get_ring().from_double_rns_repr(C.get_ring().unmanaged_ring().clone_el(x))).unwrap_or(C.zero());
    }
}

#[derive(Clone, Debug)]
pub struct CompositeSingleRNSBGV<A: Allocator + Clone  = DefaultCiphertextAllocator, C: FheanorConvolution<Zn> = DefaultConvolution> {
    number_ring: CompositeCyclotomicNumberRing,
    ciphertext_allocator: A,
    convolution: PhantomData<C>
}

impl CompositeSingleRNSBGV {

    pub fn new(m1: usize, m2: usize) -> Self {
        Self::new_with_alloc(m1, m2, DefaultCiphertextAllocator::default())
    }
}

impl<A: Allocator + Clone , C: FheanorConvolution<Zn>> CompositeSingleRNSBGV<A, C> {

    pub fn new_with_alloc(m1: usize, m2: usize, allocator: A) -> Self {
        Self {
            number_ring: CompositeCyclotomicNumberRing::new(m1, m2),
            ciphertext_allocator: allocator,
            convolution: PhantomData
        }
    }
}

impl<A: Allocator + Clone , C: FheanorConvolution<Zn>> BGVInstantiation for CompositeSingleRNSBGV<A, C> {

    type NumberRing = CompositeCyclotomicNumberRing;
    type CiphertextRing = SingleRNSRingBase<CompositeCyclotomicNumberRing, A, C>;
    type PlaintextZnRing = ZnBase;
    type PlaintextRing = NumberRingQuotientByIntBase<CompositeCyclotomicNumberRing, Zn, A>;

    fn number_ring(&self) -> &CompositeCyclotomicNumberRing {
        &self.number_ring
    }

    #[instrument(skip_all)]
    fn create_plaintext_ring(&self, modulus: El<BigIntRing>) -> PlaintextRing<Self> {
        if ZZbig.is_gt(&modulus, &ZZbig.power_of_two(SAMPLE_PRIMES_SIZE - 2)) {
            unimplemented!("Plaintext modulus greater than 2^{} are not yet supported for BGV", SAMPLE_PRIMES_SIZE - 2)
        }
        NumberRingQuotientByIntBase::create(self.number_ring().clone(), Zn::new(int_cast(modulus, ZZi64, ZZbig) as u64), self.ciphertext_allocator.clone(), STANDARD_CONVOLUTION)
    }

    #[instrument(skip_all)]
    fn create_rns_base(&self, log2_q: Range<usize>) -> zn_rns::Zn<Zn, BigIntRing> {
        let number_ring = self.number_ring();
        let required_root_of_unity = number_ring.mod_p_required_root_of_unity() as i64;
        let mut rns_base = sample_primes(
            log2_q.start, 
            log2_q.end, 
            SAMPLE_PRIMES_SIZE, 
            |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64))
        ).unwrap();
        rns_base.sort_unstable_by(|l, r| ZZbig.cmp(l, r));
        return zn_rns::Zn::new(rns_base.into_iter().map(|p| Zn::new(int_cast(p, ZZi64, ZZbig) as u64)).collect(), ZZbig);
    }

    #[instrument(skip_all)]
    fn create_ciphertext_ring_with_rns_base(&self, rns_base: zn_rns::Zn<Zn, BigIntRing>) -> CiphertextRing<Self> {
        let max_log2_n = 1 + ZZi64.abs_log2_ceil(&(self.number_ring().m() as i64)).unwrap();
        let convolutions = rns_base.as_iter().map(|Zp| C::new(*Zp, max_log2_n)).map(Arc::new).collect::<Vec<_>>();
        return SingleRNSRingBase::new_with_alloc(
            self.number_ring().clone(),
            rns_base,
            self.ciphertext_allocator.clone(),
            convolutions
        );
    }
}

///
/// Forces a ring element to be internally stored in double-RNS representation.
/// 
/// Use in benchmarks, when you want to control which representation the inputs
/// to the benchmarked code have.
/// 
pub fn force_double_rns_repr<Params, NumberRing, A>(C: &CiphertextRing<Params>, x: El<CiphertextRing<Params>>) -> El<CiphertextRing<Params>>
    where Params: BGVInstantiation<CiphertextRing = ManagedDoubleRNSRingBase<NumberRing, A>>,
        NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    C.get_ring().into_doublerns(x).map(|x| C.get_ring().from_double_rns_repr(x)).unwrap_or(C.zero())
}

#[cfg(test)]
use tracing_subscriber::prelude::*;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use std::fmt::Debug;
#[cfg(test)]
use crate::log_time;
#[cfg(test)]
use rand::rngs::StdRng;

#[test]
fn test_pow2_bgv_enc_dec() {
    let mut rng = rand::rng();
    
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);
    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::SparseWithHwt(16));

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk);
    let output = Pow2BGV::dec(&P, &C, Pow2BGV::clone_ct(&P, &C, &ctxt), &sk);
    assert_el_eq!(&P, input, output);
}

#[test]
fn test_pow2_bgv_gen_sk() {
    let mut rng = StdRng::from_seed([0; 32]);
        
    let params = Pow2BGV::new(1 << 8);
    let C = params.create_ciphertext_ring(500..520);

    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::Zero);
    assert_el_eq!(&C, C.zero(), &sk);
    
    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::SparseWithHwt(1));
    assert!(C.wrt_canonical_basis(&sk).iter().filter(|c| C.base_ring().is_one(&c) || C.base_ring().is_neg_one(&c)).count() == 1);

    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    assert!(C.wrt_canonical_basis(&sk).iter().filter(|c| C.base_ring().is_one(&c)).count() > 32);
    
}

#[test]
fn test_pow2_bgv_mul() {
    let mut rng = rand::rng();
    
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);
    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()));

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk);
    let result_ctxt = Pow2BGV::hom_mul(&P, &C, &C, Pow2BGV::clone_ct(&P, &C, &ctxt), ctxt, &rk);
    let result = Pow2BGV::dec(&P, &C, result_ctxt, &sk);
    assert_el_eq!(&P, P.int_hom().map(4), result);
}

#[test]
fn test_pow2_bgv_hybrid_key_switch() {
    let mut rng = rand::rng();
    
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C_special = params.create_ciphertext_ring(300..320);
    assert_eq!(6, C_special.base_ring().len());

    let special_modulus_factors = RNSFactorIndexList::from(vec![5], C_special.base_ring().len());
    let C = Pow2BGV::mod_switch_down_C(&C_special, &special_modulus_factors);
    let sk = Pow2BGV::gen_sk(&C_special, &mut rng, SecretKeyDistribution::UniformTernary);
    let sk_new = Pow2BGV::gen_sk(&C_special, &mut rng, SecretKeyDistribution::UniformTernary);
    let switch_key = Pow2BGV::gen_switch_key(&P, &C_special, &mut rng, &sk, &sk_new, &RNSGadgetVectorDigitIndices::select_digits(3, C_special.base_ring().len()));

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &Pow2BGV::mod_switch_sk(&C, &C_special, &sk));
    let result_ctxt = Pow2BGV::key_switch(&P, &C, &C_special, ctxt, &switch_key);
    let result = Pow2BGV::dec(&P, &C, result_ctxt, &Pow2BGV::mod_switch_sk(&C, &C_special, &sk_new));
    assert_el_eq!(&P, P.int_hom().map(2), result);

    let rk = Pow2BGV::gen_rk(&P, &C_special, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_special.base_ring().len()));
    let sk = Pow2BGV::mod_switch_sk(&C, &C_special, &sk);
    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C, &mut rng, &input, &sk);
    let result_ctxt = Pow2BGV::hom_square(&P, &C, &C_special, ctxt, &rk);
    let result = Pow2BGV::dec(&P, &C, result_ctxt, &sk);
    assert_el_eq!(&P, P.int_hom().map(4), result);

    let special_modulus_factors = RNSFactorIndexList::from(vec![0, 1], C_special.base_ring().len());
    let C = Pow2BGV::mod_switch_down_C(&C_special, &special_modulus_factors);
    let sk = Pow2BGV::gen_sk(&C_special, &mut rng, SecretKeyDistribution::UniformTernary);

    let rk = Pow2BGV::gen_rk(&P, &C_special, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_special.base_ring().len()));
    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C_special, &mut rng, &input, &sk);
    let first_mul_ctxt = Pow2BGV::hom_square(&P, &C_special, &C_special, ctxt, &rk);
    let modswitched_ctxt = Pow2BGV::mod_switch_ct(&P, &C, &C_special, first_mul_ctxt);
    let sk = Pow2BGV::mod_switch_sk(&C, &C_special, &sk);
    let result_ctxt = Pow2BGV::hom_square(&P, &C, &C_special, modswitched_ctxt, &rk);
    let result = Pow2BGV::dec(&P, &C, result_ctxt, &sk);
    assert_el_eq!(&P, P.int_hom().map(16), result);
}

#[test]
fn test_pow2_bgv_modulus_switch() {
    let mut rng = rand::rng();
    
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C0 = params.create_ciphertext_ring(500..520);
    assert_eq!(9, C0.base_ring().len());

    let sk = Pow2BGV::gen_sk(&C0, &mut rng, SecretKeyDistribution::UniformTernary);

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C0, &mut rng, &input, &sk);

    for i in [0, 1, 8] {
        let to_drop = RNSFactorIndexList::from(vec![i], C0.base_ring().len());
        let C1 = Pow2BGV::mod_switch_down_C(&C0, &to_drop);
        let ctxt1 = Pow2BGV::mod_switch_ct(&P, &C1, &C0, Pow2BGV::clone_ct(&P, &C0, &ctxt));
        let result = Pow2BGV::dec(&P, &C1, Pow2BGV::clone_ct(&P, &C1, &ctxt1), &Pow2BGV::mod_switch_sk(&C1, &C0, &sk));
        assert_el_eq!(&P, P.int_hom().map(2), result);

        let ctxt2 = Pow2BGV::mod_switch_ct(&P, &C0, &C1, ctxt1);
        let result = Pow2BGV::dec(&P, &C0, ctxt2, &sk);
        assert_el_eq!(&P, P.int_hom().map(2), result);
    }
}

#[test]
fn test_pow2_change_plaintext_modulus() {
    let mut rng = rand::rng();
    
    let params = Pow2BGV::new(1 << 8);
    let C = params.create_ciphertext_ring(500..520);
    let P0 = params.create_plaintext_ring(int_cast(17 * 17, ZZbig, ZZi64));
    let P1 = params.create_plaintext_ring(int_cast(17, ZZbig, ZZi64));

    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);

    let input = P0.int_hom().map(2 * 17);
    let ctxt = Pow2BGV::enc_sym(&P0, &C, &mut rng, &input, &sk);
    let result_ctxt = Pow2BGV::change_plaintext_modulus(&P1, &P0, &C, ctxt);
    let result = Pow2BGV::dec(&P1, &C, result_ctxt, &sk);
    assert_el_eq!(&P1, P1.int_hom().map(2), result);
}

#[test]
fn test_pow2_modulus_switch_hom_add() {
    let mut rng = rand::rng();
    
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C0 = params.create_ciphertext_ring(500..520);
    assert_eq!(9, C0.base_ring().len());

    let sk = Pow2BGV::gen_sk(&C0, &mut rng, SecretKeyDistribution::UniformTernary);

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C0, &mut rng, &input, &sk);

    for i in [0, 1, 8] {
        let to_drop = RNSFactorIndexList::from(vec![i], C0.base_ring().len());
        let C1 = Pow2BGV::mod_switch_down_C(&C0, &to_drop);
        let ctxt_modswitch = Pow2BGV::mod_switch_ct(&P, &C1, &C0, Pow2BGV::clone_ct(&P, &C0, &ctxt));
        let sk_modswitch = Pow2BGV::mod_switch_sk(&C1, &C0, &sk);
        let ctxt_other = Pow2BGV::enc_sym(&P, &C1, &mut rng, &P.int_hom().map(30), &sk_modswitch);

        let ctxt_result = Pow2BGV::hom_add(&P, &C1, ctxt_modswitch, ctxt_other);

        let result = Pow2BGV::dec(&P, &C1, ctxt_result, &sk_modswitch);
        assert_el_eq!(&P, P.int_hom().map(32), result);
    }
}

#[test]
fn test_pow2_bgv_modulus_switch_rk() {
    let mut rng = rand::rng();
    
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C0 = params.create_ciphertext_ring(500..520);
    assert_eq!(9, C0.base_ring().len());

    let sk = Pow2BGV::gen_sk(&C0, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BGV::gen_rk(&P, &C0, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C0.base_ring().len()));

    let input = P.int_hom().map(2);
    let ctxt = Pow2BGV::enc_sym(&P, &C0, &mut rng, &input, &sk);

    for i in [0, 1, 8] {
        let to_drop = RNSFactorIndexList::from(vec![i], C0.base_ring().len());
        let C1 = Pow2BGV::mod_switch_down_C(&C0, &to_drop);
        let new_sk = Pow2BGV::mod_switch_sk(&C1, &C0, &sk);
        let new_rk = Pow2BGV::mod_switch_down_rk(&C1, &C0, &rk);
        let ctxt2 = Pow2BGV::enc_sym(&P, &C1, &mut rng, &P.int_hom().map(3), &new_sk);
        let result_ctxt = Pow2BGV::hom_mul(
            &P,
            &C1,
            &C1,
            Pow2BGV::mod_switch_ct(&P, &C1, &C0, Pow2BGV::clone_ct(&P, &C0, &ctxt)),
            ctxt2,
            &new_rk
        );
        let result = Pow2BGV::dec(&P, &C1, result_ctxt, &new_sk);
        assert_el_eq!(&P, P.int_hom().map(6), result);
    }
}

#[test]
fn test_mod_switch_repeated() {
    let mut rng = StdRng::from_seed([0; 32]);
    
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(17, ZZbig, ZZi64));
    let C0 = params.create_ciphertext_ring(790..800);
    assert_eq!(14, C0.base_ring().len());

    let sk = Pow2BGV::gen_sk(&C0, &mut rng, SecretKeyDistribution::UniformTernary);
    let ctxt = Pow2BGV::enc_sym(&P, &C0, &mut rng, &P.int_hom().map(2), &sk);
    let C1 = Pow2BGV::mod_switch_down_C(&C0, &RNSFactorIndexList::from(vec![0, 1, 12, 13], 14));
    let ctxt1 = Pow2BGV::mod_switch_ct(&P, &C1, &C0, ctxt);
    let sk1 = Pow2BGV::mod_switch_sk(&C1, &C0, &sk);
    assert_el_eq!(&P, &P.int_hom().map(2), Pow2BGV::dec(&P, &C1, Pow2BGV::clone_ct(&P, &C1, &ctxt1), &sk1));

    let C2 = Pow2BGV::mod_switch_down_C(&C0, &RNSFactorIndexList::from(vec![0, 1, 2, 12, 13], 14));
    let ctxt2 = Pow2BGV::mod_switch_ct(&P, &C2, &C1, ctxt1);
    let sk2 = Pow2BGV::mod_switch_sk(&C2, &C0, &sk);
    assert_el_eq!(&P, &P.int_hom().map(2), Pow2BGV::dec(&P, &C2, ctxt2, &sk2));
}

#[test]
#[ignore]
fn measure_time_pow2_bgv_basic_ops() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    tracing_subscriber::registry().with(chrome_layer).init();

    let mut rng = rand::rng();
    let params = Pow2BGV::new(1 << 16);
    
    let P = log_time::<_, _, true, _>("CreatePtxtRing", |[]|
        params.create_plaintext_ring(int_cast(17, ZZbig, ZZi64))
    );

    let C = log_time::<_, _, true, _>("CreateCtxtRing", |[]|
        params.create_ciphertext_ring(790..800)
    );

    let sk = log_time::<_, _, true, _>("GenSK", |[]| 
        Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary)
    );

    let m = P.int_hom().map(2);
    let ct = log_time::<_, _, true, _>("EncSym", |[]|
        Pow2BGV::enc_sym(&P, &C, &mut rng, &m, &sk)
    );

    let res = log_time::<_, _, true, _>("HomAddPlain", |[]| 
        Pow2BGV::hom_add_plain(&P, &C, &m, Pow2BGV::clone_ct(&P, &C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BGV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomMulPlain", |[]| 
        Pow2BGV::hom_mul_plain(&P, &C, &m, Pow2BGV::clone_ct(&P, &C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BGV::dec(&P, &C, res, &sk));

    let rk = log_time::<_, _, true, _>("GenRK", |[]| 
        Pow2BGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()))
    );
    let ct2 = Pow2BGV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res = log_time::<_, _, true, _>("HomMul", |[]| 
        Pow2BGV::hom_mul(&P, &C, &C, ct, ct2, &rk)
    );
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BGV::dec(&P, &C, Pow2BGV::clone_ct(&P, &C, &res), &sk));

    let to_drop = RNSFactorIndexList::from(vec![0], C.base_ring().len());
    let C_new = Pow2BGV::mod_switch_down_C(&C, &to_drop);
    let sk_new = Pow2BGV::mod_switch_sk(&C_new, &C, &sk);
    let res_new = log_time::<_, _, true, _>("ModSwitch", |[]| 
        Pow2BGV::mod_switch_ct(&P, &C_new, &C, res)
    );
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BGV::dec(&P, &C_new, res_new, &sk_new));
}

#[test]
#[ignore]
fn measure_time_double_rns_composite_bgv_basic_ops() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    tracing_subscriber::registry().with(chrome_layer).init();

    let mut rng = rand::rng();
    
    let params = CompositeBGV::new(127, 337);
    
    let P = log_time::<_, _, true, _>("CreatePtxtRing", |[]|
        params.create_plaintext_ring(int_cast(4, ZZbig, ZZi64))
    );

    let C = log_time::<_, _, true, _>("CreateCtxtRing", |[]|
        params.create_ciphertext_ring(1090..1100)
    );

    let sk = log_time::<_, _, true, _>("GenSK", |[]| 
        CompositeBGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary)
    );
    
    let m = P.int_hom().map(3);
    let ct = log_time::<_, _, true, _>("EncSym", |[]|
        CompositeBGV::enc_sym(&P, &C, &mut rng, &m, &sk)
    );
    assert_el_eq!(&P, &P.int_hom().map(3), &CompositeBGV::dec(&P, &C, CompositeBGV::clone_ct(&P, &C, &ct), &sk));

    let res = log_time::<_, _, true, _>("HomAddPlain", |[]| 
        CompositeBGV::hom_add_plain(&P, &C, &m, CompositeBGV::clone_ct(&P, &C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(2), &CompositeBGV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomMulPlain", |[]| 
        CompositeBGV::hom_mul_plain(&P, &C, &m, CompositeBGV::clone_ct(&P, &C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeBGV::dec(&P, &C, res, &sk));

    let rk = log_time::<_, _, true, _>("GenRK", |[]| 
        CompositeBGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()))
    );
    let ct2 = CompositeBGV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res = log_time::<_, _, true, _>("HomMul", |[]|
        CompositeBGV::hom_mul(&P, &C, &C, ct, ct2, &rk)
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeBGV::dec(&P, &C, CompositeBGV::clone_ct(&P, &C, &res), &sk));

    let to_drop = RNSFactorIndexList::from(vec![0], C.base_ring().len());
    let C_new = CompositeBGV::mod_switch_down_C(&C, &to_drop);
    let sk_new = CompositeBGV::mod_switch_sk(&C_new, &C, &sk);
    let res_new = log_time::<_, _, true, _>("ModSwitch", |[]| 
        CompositeBGV::mod_switch_ct(&P, &C_new, &C, res)
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeBGV::dec(&P, &C_new, res_new, &sk_new));
}

#[test]
#[ignore]
fn measure_time_single_rns_composite_bgv_basic_ops() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    tracing_subscriber::registry().with(chrome_layer).init();

    let mut rng = rand::rng();
    
    let params = CompositeSingleRNSBGV::new(127, 337);
    
    let P = log_time::<_, _, true, _>("CreatePtxtRing", |[]|
        params.create_plaintext_ring(int_cast(4, ZZbig, ZZi64))
    );

    let C = log_time::<_, _, true, _>("CreateCtxtRing", |[]|
        params.create_ciphertext_ring(1090..1100)
    );

    let sk = log_time::<_, _, true, _>("GenSK", |[]| 
        CompositeSingleRNSBGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary)
    );
    
    let m = P.int_hom().map(3);
    let ct = log_time::<_, _, true, _>("EncSym", |[]|
        CompositeSingleRNSBGV::enc_sym(&P, &C, &mut rng, &m, &sk)
    );
    assert_el_eq!(&P, &P.int_hom().map(3), &CompositeSingleRNSBGV::dec(&P, &C, CompositeSingleRNSBGV::clone_ct(&P, &C, &ct), &sk));

    let res = log_time::<_, _, true, _>("HomAddPlain", |[]| 
        CompositeSingleRNSBGV::hom_add_plain(&P, &C, &m, CompositeSingleRNSBGV::clone_ct(&P, &C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(2), &CompositeSingleRNSBGV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomMulPlain", |[]| 
        CompositeSingleRNSBGV::hom_mul_plain(&P, &C, &m, CompositeSingleRNSBGV::clone_ct(&P, &C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeSingleRNSBGV::dec(&P, &C, res, &sk));

    let rk = log_time::<_, _, true, _>("GenRK", |[]| 
        CompositeSingleRNSBGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()))
    );
    let ct2 = CompositeSingleRNSBGV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res = log_time::<_, _, true, _>("HomMul", |[]| 
        CompositeSingleRNSBGV::hom_mul(&P, &C, &C, ct, ct2, &rk)
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeSingleRNSBGV::dec(&P, &C, CompositeSingleRNSBGV::clone_ct(&P, &C, &res), &sk));

    let to_drop = RNSFactorIndexList::from(vec![0], C.base_ring().len());
    let C_new = CompositeSingleRNSBGV::mod_switch_down_C(&C, &to_drop);
    let sk_new = CompositeSingleRNSBGV::mod_switch_sk(&C_new, &C, &sk);
    let res_new = log_time::<_, _, true, _>("ModSwitch", |[]| 
        CompositeSingleRNSBGV::mod_switch_ct(&P, &C_new, &C, res)
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeSingleRNSBGV::dec(&P, &C_new, res_new, &sk_new));
}
