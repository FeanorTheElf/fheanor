#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

use std::alloc::{Allocator, Global};
use std::marker::PhantomData;
use std::sync::Arc;
use std::ops::Range;
use std::fmt::Display;

use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::algorithms::miller_rabin::prev_prime;
use feanor_math::matrix::OwnedMatrix;
use feanor_math::ring::*;
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::integer::*;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::seq::*;
use feanor_math::group::*;
use feanor_math::rings::finite::FiniteRingStore;
use tracing::instrument;

use crate::ciphertext_ring::indices::RNSFactorIndexList;
use crate::ciphertext_ring::{perform_rns_op, RNSFactorCongruence};
use crate::ciphertext_ring::BGFVCiphertextRing;
use crate::circuit::evaluator::DefaultCircuitEvaluator;
use crate::circuit::PlaintextCircuit;
use crate::gadget_product::digits::*;
use crate::gadget_product::{RNSGadgetProductLhsOperand, RNSGadgetProductRhsOperand};
use crate::ntt::{FheanorNegacyclicNTT, FheanorConvolution};
use crate::ciphertext_ring::double_rns_managed::*;
use crate::number_ring::galois::*;
use crate::number_ring::hypercube::isomorphism::*;
use crate::number_ring::hypercube::structure::HypercubeStructure;
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
use crate::number_ring::*;
use crate::number_ring::galois::CyclotomicGaloisGroupOps;
use crate::number_ring::pow2_cyclotomic::*;
use crate::number_ring::composite_cyclotomic::*;
use crate::ciphertext_ring::single_rns_ring::SingleRNSRingBase;
use crate::rns_conv::bfv_rescale::{RNSRescaling, RNSRescalingConversion};
use crate::rns_conv::{RNSOperation, UsedBaseConversion};
use crate::rns_conv::shared_lift::RNSSharedBaseConversion;
use crate::DefaultCiphertextAllocator;
use crate::*;

use rand::{Rng, CryptoRng};
use rand_distr::StandardNormal;


pub mod eval;

///
/// Contains [`bootstrap::ThinBootstrapper`], an implementation of
/// thin bootstrapping for BFV.
/// 
pub mod bootstrap;

pub type NumberRing<Params: BFVInstantiation> = <<Params as BFVInstantiation>::CiphertextRing as NumberRingQuotient>::NumberRing;
pub type PlaintextRing<Params: BFVInstantiation> = RingValue<<Params as BFVInstantiation>::PlaintextRing>;
pub type SecretKey<Params: BFVInstantiation> = El<CiphertextRing<Params>>;
pub type KeySwitchKey<Params: BFVInstantiation> = (GadgetProductOperand<Params>, GadgetProductOperand<Params>);
pub type RelinKey<Params: BFVInstantiation> = KeySwitchKey<Params>;
pub type CiphertextRing<Params: BFVInstantiation> = RingValue<Params::CiphertextRing>;
pub type Ciphertext<Params: BFVInstantiation> = (El<CiphertextRing<Params>>, El<CiphertextRing<Params>>);
pub type GadgetProductOperand<Params: BFVInstantiation> = RNSGadgetProductRhsOperand<Params::CiphertextRing>;

///
/// When choosing primes for an RNS base, where the only constraint is that
/// the total modulus is at least `b` bits, we choose the bitlength to be
/// within `SAMPLE_PRIMES_MINOFFSET..SAMPLE_PRIMES_MAXOFFSET`.
/// 
/// This must be `> 0`, since we need a little bit slack to accommodate
/// for the error and exact-lifting constraints of the RNS base conversion 
/// algorithms.
/// 
const SAMPLE_PRIMES_MINOFFSET: usize = 3;

///
/// When choosing primes for an RNS base, where the only constraint is that
/// the total modulus is at least `b` bits, we choose the bitlength to be
/// within `SAMPLE_PRIMES_MINOFFSET..SAMPLE_PRIMES_MAXOFFSET`
/// 
const SAMPLE_PRIMES_MAXOFFSET: usize = SAMPLE_PRIMES_SIZE + SAMPLE_PRIMES_MINOFFSET;

///
/// When choosing primes for an RNS base, we restrict to primes of this bitlength.
/// The reason is that the corresponding quotient rings can be represented by [`zn_64::Zn`].
/// 
const SAMPLE_PRIMES_SIZE: usize = 57;

pub type SecretKeyDistribution = bgv::SecretKeyDistribution;

///
/// Trait for types that represent an instantiation of BFV.
/// 
/// For a few more details on how this works, see [`crate::examples::bfv_basics`].
/// 
/// # Design
/// 
/// Generally speaking, Fheanor tries to avoid storing parameters, in particular
/// plaintext and ciphertext, in a single object. This allows users to work with
/// multiple different plaintext and ciphertext moduli and rings in a single context.
/// 
/// In a sense, the optimal design would thus be for the HE schemes to just be a
/// collection of global functions, accepting the plaintext and ciphertext rings as
/// parameters. 
/// 
/// However, we don't go quite that far, since this approach would make
/// it very hard to provide optimized specializations for certain settings.
/// Instead, we bundle just the information on the number ring in a [`BFVInstantiation`],
/// which then has all the BFV-related functionality as associated functions. A single
/// [`BFVInstantiation`] still supports construction many plaintext and ciphertext rings
/// with different moduli, as well as keys w.r.t. different ring and parameters, as long
/// as all of them live over the same number ring. Since most optimizations are designed
/// for certain classes of number rings, this seems like a reasonable compromise.
/// 
/// Note that it is still supported and valid to exchange data between different number
/// rings, by using functionality provided by the plaintext and ciphertext rings.
/// 
pub trait BFVInstantiation {

    ///
    /// The number ring which this instantiation of BFV is based on.
    /// 
    type NumberRing: AbstractNumberRing;

    ///
    /// Type of the ciphertext ring `R/qR`.
    /// 
    type CiphertextRing: BGFVCiphertextRing<NumberRing = Self::NumberRing> + FiniteRing;

    ///
    /// Type of the plaintext base ring `Z/tZ`.
    /// 
    type PlaintextZnRing: NiceZn;
    
    ///
    /// Type of the plaintext ring `R/tR`.
    /// 
    type PlaintextRing: NumberRingQuotient<BaseRing = RingValue<Self::PlaintextZnRing>, NumberRing = Self::NumberRing> + SelfIso;

    ///
    /// The number ring `R` we work in, i.e. the ciphertext ring is `R/qR` and
    /// the plaintext ring is `R/tR`.
    /// 
    fn number_ring(&self) -> &NumberRing<Self>;

    ///
    /// Creates the ciphertext ring `R/qR` and the extended-modulus ciphertext ring
    /// `R/qq'R` that is necessary for homomorphic multiplication.
    /// 
    /// The modulus for `q` is chosen such that its bitlength is within `log2_q`.
    /// The modulus `q'` is chosen so that `R/qq'R` can represent the result of
    /// the intermediate product of the shortest lifts of two elements of `R/qR`.
    /// 
    /// If the default choice of `q` and `q'` are not suitable for you, you can
    /// also manually create the corresponding ciphertext rings, using for example
    /// [`ManagedDoubleRNSRing::new()`] etc.
    /// 
    fn create_ciphertext_rings(&self, log2_q: Range<usize>) -> (CiphertextRing<Self>, CiphertextRing<Self>);

    ///
    /// Creates the plaintext ring `R/tR` for the given plaintext modulus `t`.
    /// 
    fn create_plaintext_ring(&self, t: El<BigIntRing>) -> PlaintextRing<Self>;

    ///
    /// Generates a secret key, according to the given distribution.
    /// 
    #[instrument(skip_all)]
    fn gen_sk<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, mut rng: R, hwt: SecretKeyDistribution) -> SecretKey<Self> {
        match hwt {
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
            SecretKeyDistribution::Zero => C.zero(),
            SecretKeyDistribution::Custom(_) => panic!("if you use SecretKeyDistribution::Custom(_), you must generate the secret key yourself")
        }
    }
    
    ///
    /// Generates a new encryption of zero using the secret key and the randomness of the given rng.
    /// 
    /// The noise is chosen according to the rounded Gaussian distribution with standard deviation `noise_sigma`.
    /// 
    #[instrument(skip_all)]
    fn enc_sym_zero<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, mut rng: R, sk: &SecretKey<Self>, noise_sigma: f64) -> Ciphertext<Self> {
        let a = C.random_element(|| rng.next_u64());
        let mut b = C.negate(C.mul_ref(&a, &sk));
        let e = C.from_canonical_basis((0..C.rank()).map(|_| C.base_ring().int_hom().map((rng.sample::<f64, _>(StandardNormal) * noise_sigma).round() as i32)));
        C.add_assign(&mut b, e);
        return (b, a);
    }
    
    ///
    /// Creates a transparent encryption of zero, i.e. a noiseless encryption that does not hide
    /// the encrypted value - everyone can read it, even without access to the secret key.
    /// 
    /// Often used to initialize an accumulator (or similar) during algorithms. 
    /// 
    #[instrument(skip_all)]
    fn transparent_zero(C: &CiphertextRing<Self>) -> Ciphertext<Self> {
        (C.zero(), C.zero())
    }

    ///
    /// Encrypts the given value, using the randomness of the given rng.
    /// 
    /// The noise is chosen according to the rounded Gaussian distribution with standard deviation `noise_sigma`.
    /// 
    #[instrument(skip_all)]
    fn enc_sym<R: Rng + CryptoRng>(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, rng: R, m: &El<PlaintextRing<Self>>, sk: &SecretKey<Self>, noise_sigma: f64) -> Ciphertext<Self> {
        Self::hom_add_plain(P, C, m, Self::enc_sym_zero(C, rng, sk, noise_sigma))
    }

    ///
    /// Creates an encryption of the secret key - this is always easily possible in BFV.
    /// 
    #[instrument(skip_all)]
    fn enc_sk(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>) -> Ciphertext<Self> {
        let ZZ = P.base_ring().integer_ring();
        let Delta = ZZbig.rounded_div(
            ZZbig.clone_el(C.base_ring().modulus()), 
            &int_cast(ZZ.clone_el(P.base_ring().modulus()), ZZbig, ZZ)
        );
        (C.zero(), C.inclusion().map(C.base_ring().coerce(&ZZbig, Delta)))
    }
    
    ///
    /// Given `q/t m + e`, removes the noise term `e`, thus returns `q/t m`.
    /// 
    /// Used during [`BFVInstantiation::dec()`] and [`BFVInstantiation::noise_budget()`].
    /// 
    #[instrument(skip_all)]
    fn remove_noise(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, c: &El<CiphertextRing<Self>>) -> El<PlaintextRing<Self>> {
        let coefficients = C.wrt_canonical_basis(c);
        let ZZ = P.base_ring().integer_ring();
        let Delta = ZZbig.rounded_div(
            ZZbig.clone_el(C.base_ring().modulus()), 
            &int_cast(ZZ.clone_el(P.base_ring().modulus()), ZZbig, ZZ)
        );
        let modulo = P.base_ring().can_hom(&ZZbig).unwrap();
        return P.from_canonical_basis((0..coefficients.len()).map(|i| modulo.map(ZZbig.rounded_div(C.base_ring().smallest_lift(coefficients.at(i)), &Delta))));
    }
    
    ///
    /// Decrypts a given ciphertext.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is a valid
    /// BFV encryption w.r.t. the given plaintext modulus.
    /// 
    #[instrument(skip_all)]
    fn dec(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: Ciphertext<Self>, sk: &SecretKey<Self>) -> El<PlaintextRing<Self>> {
        let (c0, c1) = ct;
        let noisy_m = C.add(c0, C.mul_ref_snd(c1, sk));
        return Self::remove_noise(P, C, &noisy_m);
    }
    
    ///
    /// Decrypts a given ciphertext and prints its value to stdout.
    /// Designed for debugging purposes.
    /// 
    #[instrument(skip_all)]
    fn dec_println(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>, sk: &SecretKey<Self>) {
        let m = Self::dec(P, C, Self::clone_ct(C, ct), sk);
        println!("ciphertext (noise budget: {}):", Self::noise_budget(P, C, ct, sk));
        P.println(&m);
        println!();
    }
    
    ///
    /// Decrypts a given ciphertext and prints the values in its slots to stdout.
    /// Designed for debugging purposes.
    /// 
    #[instrument(skip_all)]
    fn dec_println_slots(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>, sk: &SecretKey<Self>, dir: Option<&str>) {
        let ZZ = P.base_ring().integer_ring();
        let (p, _e) = is_prime_power(ZZ, P.base_ring().modulus()).unwrap();
        let hypercube = if P.number_ring().galois_group().m() % 2 == 0 {
            HypercubeStructure::default_pow2_hypercube(P.acting_galois_group(), int_cast(p, ZZbig, ZZ))
        } else {
            HypercubeStructure::halevi_shoup_hypercube(P.acting_galois_group(), int_cast(p, ZZbig, ZZ))
        };
        let H = HypercubeIsomorphism::new::<false>(&P, &hypercube, dir);
        let m = Self::dec(P, C, Self::clone_ct(C, ct), sk);
        println!("ciphertext (noise budget: {}):", Self::noise_budget(P, C, ct, sk));
        for a in H.get_slot_values(&m) {
            H.slot_ring().println(&a);
        }
        println!();
    }
    
    ///
    /// Computes an encryption of the sum of two encrypted messages.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertexts are defined over the given ring, and are
    /// BFV encryptions w.r.t. compatible plaintext moduli.
    /// 
    #[instrument(skip_all)]
    fn hom_add(C: &CiphertextRing<Self>, lhs: Ciphertext<Self>, rhs: &Ciphertext<Self>) -> Ciphertext<Self> {
        let (lhs0, lhs1) = lhs;
        let (rhs0, rhs1) = rhs;
        return (C.add_ref_snd(lhs0, &rhs0), C.add_ref_snd(lhs1, &rhs1));
    }
    
    ///
    /// Computes an encryption of the difference of two encrypted messages.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertexts are defined over the given ring, and are
    /// BFV encryptions w.r.t. compatible plaintext moduli.
    /// 
    #[instrument(skip_all)]
    fn hom_sub(C: &CiphertextRing<Self>, lhs: Ciphertext<Self>, rhs: &Ciphertext<Self>) -> Ciphertext<Self> {
        let (lhs0, lhs1) = lhs;
        let (rhs0, rhs1) = rhs;
        return (C.sub_ref_snd(lhs0, rhs0), C.sub_ref_snd(lhs1, rhs1));
    }
    
    ///
    /// Copies a ciphertext.
    /// 
    #[instrument(skip_all)]
    fn clone_ct(C: &CiphertextRing<Self>, ct: &Ciphertext<Self>) -> Ciphertext<Self> {
        (C.clone_el(&ct.0), C.clone_el(&ct.1))
    }
    
    ///
    /// Computes an encryption of the sum of an encrypted message and a plaintext.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is a valid
    /// BFV encryption w.r.t. the given plaintext modulus.
    /// 
    #[instrument(skip_all)]
    fn hom_add_plain(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        let ZZ_to_Zq = C.base_ring().can_hom(P.base_ring().integer_ring()).unwrap();
        let ZZ = P.base_ring().integer_ring();
        let mut m = C.from_canonical_basis(P.wrt_canonical_basis(m).iter().map(|c| ZZ_to_Zq.map(P.base_ring().smallest_lift(c))));
        let Delta = C.base_ring().coerce(&ZZbig, ZZbig.rounded_div(
            ZZbig.clone_el(C.base_ring().modulus()), 
            &int_cast(ZZ.clone_el(P.base_ring().modulus()), ZZbig, ZZ)
        ));
        C.inclusion().mul_assign_ref_map(&mut m, &Delta);
        return (C.add(ct.0, m), ct.1);
    }
    
    ///
    /// Computes an encryption of the product of an encrypted message and a plaintext.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is
    /// BFV encryption w.r.t. the given plaintext modulus.
    /// 
    #[instrument(skip_all)]
    fn hom_mul_plain(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        Self::hom_mul_plain_encoded(P, C, &Self::encode_plain_multiplicant(P, C, m), ct)
    }
    
    ///
    /// Computes the smallest lift of the plaintext ring element to the ciphertext
    /// ring. The result can be used in [`BFVInstantiation::hom_mul_plain_encoded()`]
    /// to compute plaintext-ciphertext multiplication faster.
    /// 
    /// Note that (as opposed to BFV), encoding of plaintexts that are used as multiplicants
    /// (i.e. multiplied to ciphertexts) is different than for plaintexts that are used as summands
    /// (i.e. added to ciphertexts). Currently only the former is supported for BFV.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the plaintext ring element is defined over the given plaintext ring.
    /// 
    #[instrument(skip_all)]
    fn encode_plain_multiplicant(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>) -> El<CiphertextRing<Self>> {
        let ZZ_to_Zq = C.base_ring().can_hom(P.base_ring().integer_ring()).unwrap();
        return C.from_canonical_basis(P.wrt_canonical_basis(m).iter().map(|c| ZZ_to_Zq.map(P.base_ring().smallest_lift(c))));
    }

    ///
    /// Returns an encryption of the product of the encrypted input and the given plaintext,
    /// which has already been lifted/encoded into the ciphertext ring.
    /// 
    /// When the plaintext is given as an element of `P`, use [`BFVInstantiation::hom_mul_plain()`]
    /// instead. However, internally, the plaintext will be lifted into the ciphertext ring during
    /// the multiplication, and if this is performed in advance (via [`BFVInstantiation::encode_plain_multiplicant()`]),
    /// multiplication will be faster.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is a valid
    /// BFV encryptions w.r.t. compatible plaintext moduli.
    /// 
    #[instrument(skip_all)]
    fn hom_mul_plain_encoded(_P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<CiphertextRing<Self>>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        (C.mul_ref_snd(ct.0, m), C.mul_ref_snd(ct.1, m))
    }

    ///
    /// Computes an encryption of the product of an encrypted message and an integer plaintext.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is a valid
    /// BFV encryption w.r.t. the given plaintext modulus.
    /// 
    #[instrument(skip_all)]
    fn hom_mul_plain_int(_P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<BigIntRing>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        let hom = C.inclusion().compose(C.base_ring().can_hom(&ZZbig).unwrap());
        (hom.mul_ref_snd_map(ct.0, m), hom.mul_ref_snd_map(ct.1, m))
    }

    ///
    /// Computes an encrypted fused-multiply-add, i.e. an encryption of `dst + lhs * rhs`, where
    /// `lhs` is an integer and given as plaintext, and `dst`, `rhs` are given in encrypted form.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is a valid
    /// BFV encryption w.r.t. the given plaintext modulus.
    /// 
    #[instrument(skip_all)]
    fn hom_fma_plain_int(_P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, dst: Ciphertext<Self>, lhs: &El<BigIntRing>, rhs: &Ciphertext<Self>) -> Ciphertext<Self> {
        let hom = C.inclusion().compose(C.base_ring().can_hom(&ZZbig).unwrap());
        (hom.fma_map(&rhs.0, lhs, dst.0), hom.fma_map(&rhs.1, lhs, dst.1))
    }
    
    ///
    /// Computes the "noise budget" of a given ciphertext.
    /// 
    /// Concretely, the noise budget is `log(q/(t|e|))`, where `t` is the plaintext modulus
    /// and `|e|` is the `l_inf`-norm of the noise term. This will decrease during homomorphic
    /// operations, and if it reaches zero, decryption may yield incorrect results.
    /// 
    #[instrument(skip_all)]
    fn noise_budget(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>, sk: &SecretKey<Self>) -> usize {
        let (c0, c1) = Self::clone_ct(C, ct);
        let noisy_m = C.add(c0, C.mul_ref_snd(c1, sk));
        let coefficients = C.wrt_canonical_basis(&noisy_m);
        let ZZ = P.base_ring().integer_ring();
        let Delta = ZZbig.rounded_div(
            ZZbig.clone_el(C.base_ring().modulus()), 
            &int_cast(ZZ.clone_el(P.base_ring().modulus()), ZZbig, ZZ)
        );
        let log2_size_of_noise = <_ as Iterator>::max((0..coefficients.len()).map(|i| {
            let c = C.base_ring().smallest_lift(coefficients.at(i));
            let size = ZZbig.abs_log2_ceil(&ZZbig.sub_ref_fst(&c, ZZbig.mul_ref_snd(ZZbig.rounded_div(ZZbig.clone_el(&c), &Delta), &Delta)));
            return size.unwrap_or(0);
        })).unwrap();
        return ZZbig.abs_log2_ceil(C.base_ring().modulus()).unwrap().saturating_sub(log2_size_of_noise + P.base_ring().integer_ring().abs_log2_ceil(P.base_ring().modulus()).unwrap() + 1);
    }
    
    ///
    /// Generates a relinearization key, necessary to compute homomorphic multiplications.
    /// 
    /// The parameter `digits` defined the RNS-based gadget vector to use for the gadget product
    /// during key-switching. More concretely, when performing key-switching, the ciphertext
    /// will be decomposed into multiple small parts, which are then multiplied with the components
    /// of the key-switching key. Thus, a large number of small digits will result in lower (additive)
    /// noise growth during key-switching, at the cost of higher performance.
    /// 
    /// The noise is chosen according to the rounded Gaussian distribution with standard deviation `noise_sigma`.
    /// 
    #[instrument(skip_all)]
    fn gen_rk<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, rng: R, sk: &SecretKey<Self>, digits: &RNSGadgetVectorDigitIndices, noise_sigma: f64) -> RelinKey<Self> {
        Self::gen_switch_key(C, rng, &C.pow(C.clone_el(sk), 2), sk, digits, noise_sigma)
    }
    
    ///
    /// Computes an encryption of the product of two encrypted messages.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertexts are defined over the given ring, and are
    /// BFV encryptions w.r.t. the given plaintext modulus.
    /// 
    /// As opposed to BGV, hybrid key switching is currently not implemented for BFV.
    /// You can achieve the same effect by manually modulus-switching ciphertext to a higher
    /// modulus before calling `hom_mul()` (although this will be less efficient than 
    /// performing only the key-switch modulo the larger modulus).
    /// 
    #[instrument(skip_all)]
    fn hom_mul(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, C_mul: &CiphertextRing<Self>, lhs: Ciphertext<Self>, rhs: Ciphertext<Self>, rk: &RelinKey<Self>) -> Ciphertext<Self> {
        let (c00, c01) = lhs;
        let (c10, c11) = rhs;

        let mut lift = Self::lift_to_Cmul(C, C_mul);
        let c00_lifted = lift(&c00);
        let c01_lifted = lift(&c01);
        let c10_lifted = lift(&c10);
        let c11_lifted = lift(&c11);

        let [lifted0, lifted1, lifted2] = C_mul.get_ring().two_by_two_convolution([&c00_lifted, &c01_lifted], [&c10_lifted, &c11_lifted]);

        let mut scale_down = Self::rescale_to_C(P, C, C_mul);
        let res0 = scale_down(&lifted0);
        let res1 = scale_down(&lifted1);
        let res2 = scale_down(&lifted2);

        let op = RNSGadgetProductLhsOperand::from_element_with(C.get_ring(), &res2, rk.0.gadget_vector_digits());
        let (s0, s1) = rk;
        return (C.add(res0, op.gadget_product(s0, C.get_ring())), C.add(res1, op.gadget_product(s1, C.get_ring())));
    }
    
    ///
    /// Computes an encryption of the square of an encrypted messages.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertexts are defined over the given ring, and are
    /// BFV encryptions w.r.t. the given plaintext modulus.
    /// 
    /// As opposed to BGV, hybrid key switching is currently not implemented for BFV.
    /// You can achieve the same effect by manually modulus-switching ciphertext to a higher
    /// modulus before calling `hom_square()` (although this will be less efficient than 
    /// performing only the key-switch modulo the larger modulus).
    /// 
    #[instrument(skip_all)]
    fn hom_square(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, C_mul: &CiphertextRing<Self>, val: Ciphertext<Self>, rk: &RelinKey<Self>) -> Ciphertext<Self> {
        let (c0, c1) = val;

        let mut lift = Self::lift_to_Cmul(C, C_mul);
        let c0_lifted = lift(&c0);
        let c1_lifted = lift(&c1);

        let [lifted0, lifted1, lifted2] = C_mul.get_ring().two_by_two_convolution([&c0_lifted, &c1_lifted], [&c0_lifted, &c1_lifted]);

        let mut scale_down = Self::rescale_to_C(P, C, C_mul);
        let res0 = scale_down(&lifted0);
        let res1 = scale_down(&lifted1);
        let res2 = scale_down(&lifted2);

        let op = RNSGadgetProductLhsOperand::from_element_with(C.get_ring(), &res2, rk.0.gadget_vector_digits());
        let (s0, s1) = rk;
        return (C.add(res0, op.gadget_product(s0, C.get_ring())), C.add(res1, op.gadget_product(s1, C.get_ring())));
        
    }
    
    ///
    /// Generates a key-switch key. 
    /// 
    /// In particular, this is used to generate relinearization keys (via [`BFVInstantiation::gen_rk()`])
    /// or Galois keys (via [`BFVInstantiation::gen_gk()`]).
    /// 
    /// The parameter `digits` defined the RNS-based gadget vector to use for the gadget product
    /// during key-switching. More concretely, when performing key-switching, the ciphertext
    /// will be decomposed into multiple small parts, which are then multiplied with the components
    /// of the key-switching key. Thus, a large number of small digits will result in lower (additive)
    /// noise growth during key-switching, at the cost of higher performance.
    /// 
    /// The noise is chosen according to the rounded Gaussian distribution with standard deviation `noise_sigma`.
    /// 
    #[instrument(skip_all)]
    fn gen_switch_key<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, mut rng: R, old_sk: &SecretKey<Self>, new_sk: &SecretKey<Self>, digits: &RNSGadgetVectorDigitIndices, noise_sigma: f64) -> KeySwitchKey<Self> {
        let mut res0 = RNSGadgetProductRhsOperand::new_with_digits(C.get_ring(), digits.to_owned());
        let mut res1 = RNSGadgetProductRhsOperand::new_with_digits(C.get_ring(), digits.to_owned());
        for (i, digit) in digits.iter().enumerate() {
            let (c0, c1) = Self::enc_sym_zero(C, &mut rng, new_sk, noise_sigma);
            let factor = C.base_ring().get_ring().from_congruence((0..C.base_ring().len()).map(|i2| {
                let Fp = C.base_ring().at(i2);
                if digit.contains(&i2) { Fp.one() } else { Fp.zero() } 
            }));
            let mut payload = C.clone_el(&old_sk);
            C.inclusion().mul_assign_ref_map(&mut payload, &factor);
            C.add_assign_ref(&mut payload, &c0);
            res0.set_component(C.get_ring(), i, payload);
            res1.set_component(C.get_ring(), i, c1);
        }
        return (res0, res1);
    }
    
    ///
    /// Using a key-switch key, computes an encryption encrypting the same message as the
    /// given ciphertext under a different secret key.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is a valid
    /// BFV encryptions w.r.t. the given plaintext modulus.
    /// 
    /// As opposed to BGV, hybrid key switching is currently not implemented for BFV.
    /// You can achieve the same effect by manually modulus-switching ciphertext to a higher
    /// modulus before calling `key_switch()`.
    /// 
    #[instrument(skip_all)]
    fn key_switch(C: &CiphertextRing<Self>, ct: Ciphertext<Self>, switch_key: &KeySwitchKey<Self>) -> Ciphertext<Self> {
        let (c0, c1) = ct;
        let (s0, s1) = switch_key;
        let op = RNSGadgetProductLhsOperand::from_element_with(C.get_ring(), &c1, switch_key.0.gadget_vector_digits());
        return (
            C.add_ref_snd(c0, &op.gadget_product(s0, C.get_ring())),
            op.gadget_product(s1, C.get_ring())
        );
    }
    
    ///
    /// Modulus-switches from `R/qR` to `R/tR`, where the latter one is given as a plaintext ring.
    /// In particular, this is necessary during bootstrapping.
    /// 
    #[instrument(skip_all)]
    fn mod_switch_to_plaintext(target: &PlaintextRing<Self>, C: &CiphertextRing<Self>, ct: Ciphertext<Self>) -> (El<PlaintextRing<Self>>, El<PlaintextRing<Self>>) {
        // this is not very performance-critical, so implement it using big integers
        let ZZbig_to_target = target.base_ring().can_hom(&ZZbig).unwrap();
        let t = int_cast(target.base_ring().integer_ring().clone_el(target.base_ring().modulus()), ZZbig, target.base_ring().integer_ring());
        let rescale = |x| target.from_canonical_basis(C.wrt_canonical_basis(x).iter().map(|a|
            ZZbig_to_target.map(ZZbig.rounded_div(ZZbig.mul_ref_snd(C.base_ring().smallest_lift(a), &t), C.base_ring().modulus()))
        ));
        (rescale(&ct.0), rescale(&ct.1))
    }

    ///
    /// Modulus-switches a ciphertext.
    /// 
    /// More concretely, we have the ring `Cold = R/qR` and `Cnew = R/q'R`.
    /// Given a ciphertext `ct` over `R/qR`, this function then computes a ciphertext 
    /// encrypting the same message over `R/q'R` (w.r.t. the secret key `sk mod q'`).
    /// 
    #[instrument(skip_all)]
    fn mod_switch_ct(_P: &PlaintextRing<Self>, Cnew: &CiphertextRing<Self>, Cold: &CiphertextRing<Self>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        let mod_switch = RNSRescaling::new_with_alloc(
            Cold.base_ring().as_iter().map(|Zp| *Zp).collect(),
            Cnew.base_ring().as_iter().map(|Zp| *Zp).collect(),
            Global
        );
        assert!(Cold.base_ring().as_iter().zip(mod_switch.input_rings()).all(|(l, r)| l.get_ring() == r.get_ring()));
        assert!(Cnew.base_ring().as_iter().zip(mod_switch.output_rings()).all(|(l, r)| l.get_ring() == r.get_ring()));
        return (
            perform_rns_op(Cnew.get_ring(), Cold.get_ring(), &ct.0, &mod_switch),
            perform_rns_op(Cnew.get_ring(), Cold.get_ring(), &ct.1, &mod_switch)
        );
    }
    
    ///
    /// Modulus-switches a secret key.
    /// 
    /// This requires that in coefficient norm, the secret key is bounded by `q/4`.
    /// Since the secret key for BFV must be small anyway, this should never a problem.
    /// 
    #[instrument(skip_all)]
    fn mod_switch_sk(_P: &PlaintextRing<Self>, Cnew: &CiphertextRing<Self>, Cold: &CiphertextRing<Self>, sk: &SecretKey<Self>) -> SecretKey<Self> {
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
    /// Generates a Galois key, usable for homomorphically applying the Galois automorphisms
    /// defined by the given element of the Galois group.
    /// 
    /// The parameter `digits` defined the RNS-based gadget vector to use for the gadget product
    /// during key-switching. More concretely, when performing key-switching, the ciphertext
    /// will be decomposed into multiple small parts, which are then multiplied with the components
    /// of the key-switching key. Thus, a large number of small digits will result in lower (additive)
    /// noise growth during key-switching, at the cost of higher performance.
    /// 
    /// The noise is chosen according to the rounded Gaussian distribution with standard deviation `noise_sigma`.
    /// 
    #[instrument(skip_all)]
    fn gen_gk<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, rng: R, sk: &SecretKey<Self>, g: &GaloisGroupEl, digits: &RNSGadgetVectorDigitIndices, noise_sigma: f64) -> KeySwitchKey<Self> {
        Self::gen_switch_key(C, rng, &C.get_ring().apply_galois_action(sk, g), sk, digits, noise_sigma)
    }
    
    ///
    /// Computes an encryption of `sigma(x)`, where `x` is the message encrypted by the given ciphertext
    /// and `sigma` is the given Galois automorphism.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is a valid
    /// BFV encryptions w.r.t. the given plaintext modulus.
    /// 
    /// As opposed to BGV, hybrid key switching is currently not implemented for BFV.
    /// You can achieve the same effect by manually modulus-switching ciphertext to a higher
    /// modulus before calling `hom_galois()`.
    /// 
    #[instrument(skip_all)]
    fn hom_galois(C: &CiphertextRing<Self>, ct: Ciphertext<Self>, g: &GaloisGroupEl, gk: &KeySwitchKey<Self>) -> Ciphertext<Self> {
        Self::key_switch(C, (
            C.get_ring().apply_galois_action(&ct.0, g),
            C.get_ring().apply_galois_action(&ct.1, g)
        ), gk)
    }
    
    ///
    /// Homomorphically applies multiple Galois automorphisms at once.
    /// Functionally, this is equivalent to calling [`BFVInstantiation::hom_galois()`]
    /// multiple times, but can be faster.
    /// 
    /// All used Galois keys must use the same digits, i.e. the same RNS-based
    /// gadget vector.
    /// 
    /// This function does not perform any semantic checks. In particular, it is up to the
    /// caller to ensure that the ciphertext is defined over the given ring, and is a valid
    /// BFV encryptions w.r.t. the given plaintext modulus.
    /// 
    /// As opposed to BGV, hybrid key switching is currently not implemented for BFV.
    /// You can achieve the same effect by manually modulus-switching ciphertext to a higher
    /// modulus before calling `hom_galois()`.
    /// 
    #[instrument(skip_all)]
    fn hom_galois_many<'b, V>(C: &CiphertextRing<Self>, ct: Ciphertext<Self>, gs: &[GaloisGroupEl], gks: V) -> Vec<Ciphertext<Self>>
        where V: VectorFn<&'b KeySwitchKey<Self>>,
            Self: 'b
    {
        let digits = gks.at(0).0.gadget_vector_digits();
        let has_same_digits = |gk: &RNSGadgetProductRhsOperand<_>| gk.gadget_vector_digits().len() == digits.len() && gk.gadget_vector_digits().iter().zip(digits.iter()).all(|(l, r)| l == r);
        assert!(gks.iter().all(|gk| has_same_digits(&gk.0) && has_same_digits(&gk.1)));
        let (c0, c1) = ct;
        let c1_op = RNSGadgetProductLhsOperand::from_element_with(C.get_ring(), &c1, digits);
        let c1_op_gs = c1_op.apply_galois_action_many(C.get_ring(), gs);
        let c0_gs = C.get_ring().apply_galois_action_many(&c0, gs).into_iter();
        assert_eq!(gks.len(), c1_op_gs.len());
        assert_eq!(gks.len(), c0_gs.len());
        return c0_gs.zip(c1_op_gs.iter()).enumerate().map(|(i, (c0_g, c1_g))| {
            let (s0, s1) = gks.at(i);
            let r0 = c1_g.gadget_product(s0, C.get_ring());
            let r1 = c1_g.gadget_product(s1, C.get_ring());
            return (C.add_ref(&r0, &c0_g), r1);
        }).collect();
    }

    ///
    /// Returns an implementation of the function `R/qR -> R/qq'R` that maps every `x` in `R/qR`
    /// to a short element of `R/qq'R` congruent to `x` modulo `q`.
    /// 
    /// It is returned as a function object, which allows it to store data that is used for the
    /// rescaling. This function is used by the default implementations of multiplication, i.e.
    /// [`BFVInstantiation::hom_mul()`] and [`BFVInstantiation::hom_square()`].
    /// 
    /// The function is behind a trait object, so that concrete instantiations can use a different
    /// implementation which is more performant on their concrete choice of rings.
    /// 
    fn lift_to_Cmul<'a>(C: &'a CiphertextRing<Self>, C_mul: &'a CiphertextRing<Self>) -> Box<dyn 'a + for<'b> FnMut(&'b El<CiphertextRing<Self>>) -> El<CiphertextRing<Self>>> {
        let C_delta = RingValue::from(C_mul.get_ring().drop_rns_factor(&RNSFactorIndexList::from(0..C.base_ring().len(), C_mul.base_ring().len())));
        let lift = UsedBaseConversion::new(
            C.base_ring().as_iter().cloned().collect::<Vec<_>>(),
            C_delta.base_ring().as_iter().cloned().collect::<Vec<_>>()
        );
        let mut tmp_in = OwnedMatrix::zero(C.base_ring().len(), C_mul.get_ring().small_generating_set_len(), C_mul.base_ring().at(0));
        let mut tmp_out = OwnedMatrix::zero(C_mul.base_ring().len() - C.base_ring().len(), C_mul.get_ring().small_generating_set_len(), C_mul.base_ring().at(0));
        return Box::new(move |c| {
            C.get_ring().as_representation_wrt_small_generating_set(c, tmp_in.data_mut());
            lift.apply(tmp_in.data(), tmp_out.data_mut());
            let delta = C_delta.get_ring().from_representation_wrt_small_generating_set(tmp_out.data());
            return C_mul.add(
                C_mul.get_ring().add_rns_factor_element(C.get_ring(), &RNSFactorIndexList::from(C.base_ring().len()..C_mul.base_ring().len(), C_mul.base_ring().len()), c),
                C_mul.get_ring().add_rns_factor_element(&C_delta.get_ring(), &RNSFactorIndexList::from(0..C.base_ring().len(), C_mul.base_ring().len()), &delta)
            );
        });
    }

    ///
    /// Returns an implementation of the function `R/qq'R -> R/qR` that maps every `x` in `R/qq'R`
    /// to an element of `R/qR` close to `smallest_lift(tx/q)`.
    /// 
    /// It is returned as a function object, which allows it to store data that is used for the
    /// rescaling. This function is used by the default implementations of multiplication, i.e.
    /// [`BFVInstantiation::hom_mul()`] and [`BFVInstantiation::hom_square()`].
    /// 
    /// The function is behind a trait object, so that concrete instantiations can use a different
    /// implementation which is more performant on their concrete choice of rings.
    /// 
    fn rescale_to_C<'a>(P: &PlaintextRing<Self>, C: &'a CiphertextRing<Self>, C_mul: &'a CiphertextRing<Self>) -> Box<dyn 'a + for<'b> FnMut(&'b El<CiphertextRing<Self>>) -> El<CiphertextRing<Self>>> {
        assert!(C.number_ring() == C_mul.number_ring());
        assert_eq!(C.get_ring().small_generating_set_len(), C_mul.get_ring().small_generating_set_len());

        let ZZ = P.base_ring().integer_ring();
        // we treat the case that Zt can be represented using zn_64::Zn separately, since it is 
        // common and can be implemented more efficiently
        if let Some(Zt) = t_fits_zn_64(ZZ, P.base_ring().modulus()) {
            let rescale = RNSRescalingConversion::new_with_alloc(
                C_mul.base_ring().as_iter().cloned().collect(), 
                C.base_ring().as_iter().cloned().collect(),
                vec![Zt], 
                (0..C.base_ring().len()).collect(),
                Global
            );
            let result = move |c: &El<CiphertextRing<Self>>| perform_rns_op(C.get_ring(), C_mul.get_ring(), &*c, &rescale);
            Box::new(result)
        } else {
            let to_extended = temporarily_extend_rns_base(C_mul.base_ring(), ZZ.abs_log2_ceil(P.base_ring().modulus()).unwrap());
            let rescale = RNSRescalingConversion::new_with_alloc(
                to_extended.output_rings().to_owned(), 
                C.base_ring().as_iter().cloned().collect(),
                Vec::new(), 
                (0..C.base_ring().len()).collect(),
                Global
            );
            let t_mod_extended = to_extended.output_rings().iter().map(|ring| ring.coerce(ZZ, ZZ.clone_el(P.base_ring().modulus()))).collect::<Vec<_>>();
            let mut tmp_in_out = OwnedMatrix::zero(C_mul.base_ring().len(), C_mul.get_ring().small_generating_set_len(), C_mul.base_ring().at(0));
            let mut tmp_extended = OwnedMatrix::zero(to_extended.output_rings().len(), C_mul.get_ring().small_generating_set_len(), C_mul.base_ring().at(0));
            let result = move |c: &El<CiphertextRing<Self>>| {
                C_mul.get_ring().as_representation_wrt_small_generating_set(c, tmp_in_out.data_mut());
                to_extended.apply(tmp_in_out.data(), tmp_extended.data_mut());
                for (ring, (row, factor)) in to_extended.output_rings().iter().zip(tmp_extended.data_mut().row_iter().zip(t_mod_extended.iter())) {
                    for x in row {
                        ring.mul_assign_ref(x, factor);
                    }
                }
                let mut tmp = tmp_in_out.data_mut().restrict_rows(0..C.base_ring().len());
                rescale.apply(tmp_extended.data(), tmp.reborrow());
                return C.get_ring().from_representation_wrt_small_generating_set(tmp.as_const());
            };
            Box::new(result)
        }
    }
}

///
/// Instantiation of BFV in power-of-two cyclotomic rings `Z[X]/(X^N + 1)` for `N`
/// a power of two.
/// 
/// For these rings, using a `DoubleRNSRing` as ciphertext ring is always the best
/// (i.e. fastest) solution.
/// 
#[derive(Debug)]
pub struct Pow2BFV<A: Allocator + Clone  = DefaultCiphertextAllocator, N: FheanorNegacyclicNTT<Zn> = DefaultNegacyclicNTT> {
    number_ring: Pow2CyclotomicNumberRing<N>,
    ciphertext_allocator: A
}

impl Pow2BFV {

    pub fn new(m: usize) -> Self {
        Self::new_with_ntt(m, DefaultCiphertextAllocator::default())
    }
}

impl<A: Allocator + Clone , N: FheanorNegacyclicNTT<Zn>> Pow2BFV<A, N> {

    #[instrument(skip_all)]
    pub fn new_with_ntt(m: usize, allocator: A) -> Self {
        return Self {
            number_ring: Pow2CyclotomicNumberRing::new_with_ntt(m as u64),
            ciphertext_allocator: allocator
        }
    }
    
    pub fn ciphertext_allocator(&self) -> &A {
        &self.ciphertext_allocator
    }
}

impl<A: Allocator + Clone , C: FheanorNegacyclicNTT<Zn>> Display for Pow2BFV<A, C> {

    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BFV({:?})", self.number_ring)
    }
}

impl<A: Allocator + Clone , C: FheanorNegacyclicNTT<Zn>> Clone for Pow2BFV<A, C> {

    fn clone(&self) -> Self {
        Self {
            number_ring: self.number_ring.clone(),
            ciphertext_allocator: self.ciphertext_allocator.clone()
        }
    }
}

impl<A: Allocator + Clone , C: FheanorNegacyclicNTT<Zn>> BFVInstantiation for Pow2BFV<A, C> {

    type NumberRing = Pow2CyclotomicNumberRing<C>;
    type CiphertextRing = ManagedDoubleRNSRingBase<Pow2CyclotomicNumberRing<C>, A>;
    type PlaintextRing = NumberRingQuotientByIntBase<Pow2CyclotomicNumberRing<C>, Zn>;
    type PlaintextZnRing = ZnBase;

    #[instrument(skip_all)]
    fn number_ring(&self) -> &Pow2CyclotomicNumberRing<C> {
        &self.number_ring
    }

    #[instrument(skip_all)]
    fn create_plaintext_ring(&self, t: El<BigIntRing>) -> PlaintextRing<Self> {
        NumberRingQuotientByIntBase::new(self.number_ring().clone(), Zn::new(int_cast(t, ZZi64, ZZbig) as u64))
    }

    #[instrument(skip_all)]
    fn create_ciphertext_rings(&self, log2_q: Range<usize>) -> (CiphertextRing<Self>, CiphertextRing<Self>) {
        let number_ring = self.number_ring();
        let required_root_of_unity = number_ring.mod_p_required_root_of_unity() as i64;
        let next_prime = |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64));
        let C_rns_base_primes = sample_primes(log2_q.start, log2_q.end, SAMPLE_PRIMES_SIZE, &next_prime).unwrap();
        let C_rns_base = zn_rns::Zn::new(C_rns_base_primes.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect::<Vec<_>>(), ZZbig);

        let Cmul_modulus_size = 2 * ZZbig.abs_log2_ceil(C_rns_base.modulus()).unwrap() + number_ring.small_basis_product_expansion_factor().log2().ceil() as usize;
        let Cmul_rns_base_primes = extend_sampled_primes(&C_rns_base_primes, Cmul_modulus_size + SAMPLE_PRIMES_MINOFFSET, Cmul_modulus_size + SAMPLE_PRIMES_MAXOFFSET, SAMPLE_PRIMES_SIZE, &next_prime).unwrap();
        let Cmul_rns_base = zn_rns::Zn::new(Cmul_rns_base_primes.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect(), ZZbig);

        let C_mul = ManagedDoubleRNSRingBase::new_with_alloc(
            number_ring.clone(),
            Cmul_rns_base,
            self.ciphertext_allocator.clone()
        );

        let dropped_indices = RNSFactorIndexList::from((0..C_mul.base_ring().len()).filter(|i| C_rns_base.as_iter().all(|Zp| Zp.get_ring() != C_mul.base_ring().at(*i).get_ring())), C_mul.base_ring().len());
        let C = RingValue::from(C_mul.get_ring().drop_rns_factor(&dropped_indices));
        assert!(C.base_ring().get_ring() == C_rns_base.get_ring());
        return (C, C_mul);
    }

    #[instrument(skip_all)]
    fn encode_plain_multiplicant(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>) -> El<CiphertextRing<Self>> {
        let ZZ_to_Zq = C.base_ring().can_hom(P.base_ring().integer_ring()).unwrap();
        let result = C.from_canonical_basis(P.wrt_canonical_basis(m).iter().map(|c| ZZ_to_Zq.map(P.base_ring().smallest_lift(c))));
        return force_double_rns_repr::<Self, _, _>(C, result);
    }
    
    fn lift_to_Cmul<'a>(C: &'a CiphertextRing<Self>, C_mul: &'a CiphertextRing<Self>) -> Box<dyn 'a + for<'b> FnMut(&'b El<CiphertextRing<Self>>) -> El<CiphertextRing<Self>>> {
        let C_delta = RingValue::from(C_mul.get_ring().drop_rns_factor(&RNSFactorIndexList::from(0..C.base_ring().len(), C_mul.base_ring().len())));
        let lift = UsedBaseConversion::new(
            C.base_ring().as_iter().cloned().collect::<Vec<_>>(),
            C_delta.base_ring().as_iter().cloned().collect::<Vec<_>>()
        );
        let mut tmp_in = OwnedMatrix::zero(C.base_ring().len(), C_mul.get_ring().small_generating_set_len(), C_mul.base_ring().at(0));
        let mut tmp_out = OwnedMatrix::zero(C_mul.base_ring().len() - C.base_ring().len(), C_mul.get_ring().small_generating_set_len(), C_mul.base_ring().at(0));
        return Box::new(move |c| {
            C.get_ring().as_representation_wrt_small_generating_set(c, tmp_in.data_mut());
            lift.apply(tmp_in.data(), tmp_out.data_mut());
            let delta = force_double_rns_repr::<Self, _, _>(&C_delta, C_delta.get_ring().from_representation_wrt_small_generating_set(tmp_out.data()));
            return C_mul.get_ring().collect_rns_factors(
                (0..C.base_ring().len()).map(|i| RNSFactorCongruence::CongruentTo(C.get_ring(), i, c)).chain(
                    (0..C_delta.base_ring().len()).map(|i| RNSFactorCongruence::CongruentTo(C_delta.get_ring(), i, &delta))
                )
            );
        });
    }
}

///
/// Instantiation of BFV over odd, composite cyclotomic rings `Z[X]/(Phi_m(X))`
/// with `m = m1 * m2` and `m2, m2` odd, coprime and squarefree integers. Ciphertexts are represented
/// in double-RNS form. If single-RNS form is instead requires, use [`CompositeSingleRNSBFV`].
/// 
#[derive(Clone, Debug)]
pub struct CompositeBFV<A: Allocator + Clone  = DefaultCiphertextAllocator> {
    number_ring: CompositeCyclotomicNumberRing,
    ciphertext_allocator: A
}

impl<A: Allocator + Clone > Display for CompositeBFV<A> {

    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BFV({:?})", self.number_ring)
    }
}

impl CompositeBFV {

    pub fn new(m1: usize, m2: usize) -> Self {
        Self::new_with_alloc(m1, m2, DefaultCiphertextAllocator::default())
    }
}

impl<A: Allocator + Clone > CompositeBFV<A> {

    #[instrument(skip_all)]
    pub fn new_with_alloc(m1: usize, m2: usize, allocator: A) -> Self {
        Self { 
            number_ring: CompositeCyclotomicNumberRing::new(m1, m2), 
            ciphertext_allocator: allocator
        }
    }

    pub fn ciphertext_allocator(&self) -> &A {
        &self.ciphertext_allocator
    }

    pub fn m1(&self) -> usize {
        self.number_ring.m1() as usize
    }

    pub fn m2(&self) -> usize {
        self.number_ring.m2() as usize
    }
}

impl<A: Allocator + Clone > BFVInstantiation for CompositeBFV<A> {

    type NumberRing = CompositeCyclotomicNumberRing;
    type CiphertextRing = ManagedDoubleRNSRingBase<CompositeCyclotomicNumberRing, A>;
    type PlaintextRing = NumberRingQuotientByIntBase<CompositeCyclotomicNumberRing, Zn>;
    type PlaintextZnRing = ZnBase;

    #[instrument(skip_all)]
    fn number_ring(&self) -> &CompositeCyclotomicNumberRing {
        &self.number_ring
    }

    #[instrument(skip_all)]
    fn create_plaintext_ring(&self, t: El<BigIntRing>) -> PlaintextRing<Self> {
        NumberRingQuotientByIntBase::new(self.number_ring().clone(), Zn::new(int_cast(t, ZZi64, ZZbig) as u64))
    }
    
    #[instrument(skip_all)]
    fn create_ciphertext_rings(&self, log2_q: Range<usize>) -> (CiphertextRing<Self>, CiphertextRing<Self>) {
        let number_ring = self.number_ring();
        let required_root_of_unity = number_ring.mod_p_required_root_of_unity() as i64;
        let next_prime = |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64));
        let C_rns_base_primes = sample_primes(log2_q.start, log2_q.end, SAMPLE_PRIMES_SIZE, &next_prime).unwrap();
        let C_rns_base = zn_rns::Zn::new(C_rns_base_primes.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect::<Vec<_>>(), ZZbig);

        let Cmul_modulus_size = 2 * ZZbig.abs_log2_ceil(C_rns_base.modulus()).unwrap() + number_ring.small_basis_product_expansion_factor().log2().ceil() as usize;
        let Cmul_rns_base_primes = extend_sampled_primes(&C_rns_base_primes, Cmul_modulus_size + SAMPLE_PRIMES_MINOFFSET, Cmul_modulus_size + SAMPLE_PRIMES_MAXOFFSET, SAMPLE_PRIMES_SIZE, &next_prime).unwrap();
        let Cmul_rns_base = zn_rns::Zn::new(Cmul_rns_base_primes.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect(), ZZbig);

        let C_mul = ManagedDoubleRNSRingBase::new_with_alloc(
            number_ring.clone(),
            Cmul_rns_base,
            self.ciphertext_allocator.clone()
        );

        let dropped_indices = RNSFactorIndexList::from((0..C_mul.base_ring().len()).filter(|i| C_rns_base.as_iter().all(|Zp| Zp.get_ring() != C_mul.base_ring().at(*i).get_ring())), C_mul.base_ring().len());
        let C = RingValue::from(C_mul.get_ring().drop_rns_factor(&dropped_indices));
        assert!(C.base_ring().get_ring() == C_rns_base.get_ring());
        return (C, C_mul);
    }

    #[instrument(skip_all)]
    fn encode_plain_multiplicant(P: &PlaintextRing<Self>, C: &CiphertextRing<Self>, m: &El<PlaintextRing<Self>>) -> El<CiphertextRing<Self>> {
        let ZZ_to_Zq = C.base_ring().can_hom(P.base_ring().integer_ring()).unwrap();
        return force_double_rns_repr::<Self, _, _>(C, C.from_canonical_basis(P.wrt_canonical_basis(m).iter().map(|c| ZZ_to_Zq.map(P.base_ring().smallest_lift(c)))));
    }

    fn lift_to_Cmul<'a>(C: &'a CiphertextRing<Self>, C_mul: &'a CiphertextRing<Self>) -> Box<dyn 'a + for<'b> FnMut(&'b El<CiphertextRing<Self>>) -> El<CiphertextRing<Self>>> {
        let C_delta = RingValue::from(C_mul.get_ring().drop_rns_factor(&RNSFactorIndexList::from(0..C.base_ring().len(), C_mul.base_ring().len())));
        let lift = UsedBaseConversion::new(
            C.base_ring().as_iter().cloned().collect::<Vec<_>>(),
            C_delta.base_ring().as_iter().cloned().collect::<Vec<_>>()
        );
        let mut tmp_in = OwnedMatrix::zero(C.base_ring().len(), C_mul.get_ring().small_generating_set_len(), C_mul.base_ring().at(0));
        let mut tmp_out = OwnedMatrix::zero(C_mul.base_ring().len() - C.base_ring().len(), C_mul.get_ring().small_generating_set_len(), C_mul.base_ring().at(0));
        return Box::new(move |c| {
            C.get_ring().as_representation_wrt_small_generating_set(c, tmp_in.data_mut());
            lift.apply(tmp_in.data(), tmp_out.data_mut());
            let delta = force_double_rns_repr::<Self, _, _>(&C_delta, C_delta.get_ring().from_representation_wrt_small_generating_set(tmp_out.data()));
            return C_mul.get_ring().collect_rns_factors(
                (0..C.base_ring().len()).map(|i| RNSFactorCongruence::CongruentTo(C.get_ring(), i, c)).chain(
                    (0..C_delta.base_ring().len()).map(|i| RNSFactorCongruence::CongruentTo(C_delta.get_ring(), i, &delta))
                )
            );
        });
    }
}

///
/// Instantiation of BFV over odd, composite cyclotomic rings `Z[X]/(Phi_m(X))`
/// with `m = m1 m2` and `m2, m2` odd coprime integers. Ciphertexts are represented
/// in single-RNS form. If double-RNS form is instead requires, use [`CompositeBFV`].
/// 
/// This takes a type `C` as last generic argument, which is the type of the convolution
/// algorithm to use to instantiate the ciphertext ring. This has a major impact on 
/// performance.
/// 
#[derive(Debug)]
pub struct CompositeSingleRNSBFV<A: Allocator + Clone  = DefaultCiphertextAllocator, C: FheanorConvolution<Zn> = DefaultConvolution> {
    number_ring: CompositeCyclotomicNumberRing,
    ciphertext_allocator: A,
    convolution: PhantomData<C>
}

impl CompositeSingleRNSBFV {

    pub fn new(m1: usize, m2: usize) -> Self {
        Self::new_with_alloc(m1, m2, DefaultCiphertextAllocator::default())
    }
}

impl<A: Allocator + Clone , C: FheanorConvolution<Zn>> CompositeSingleRNSBFV<A, C> {

    #[instrument(skip_all)]
    pub fn new_with_alloc(m1: usize, m2: usize, alloc: A) -> Self {
        Self {
            number_ring: CompositeCyclotomicNumberRing::new(m1, m2),
            ciphertext_allocator: alloc,
            convolution: PhantomData::<C>
        }
    }

    pub fn ciphertext_allocator(&self) -> &A {
        &self.ciphertext_allocator
    }
}

impl<A: Allocator + Clone , C: FheanorConvolution<Zn>> Clone for CompositeSingleRNSBFV<A, C> {

    fn clone(&self) -> Self {
        Self {
            number_ring: self.number_ring.clone(),
            ciphertext_allocator: self.ciphertext_allocator.clone(),
            convolution: self.convolution
        }
    }
}

impl<A: Allocator + Clone , C: FheanorConvolution<Zn>> Display for CompositeSingleRNSBFV<A, C> {

    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BFV({:?})", self.number_ring)
    }
}

impl<A: Allocator + Clone , C: FheanorConvolution<Zn>> BFVInstantiation for CompositeSingleRNSBFV<A, C> {

    type NumberRing = CompositeCyclotomicNumberRing;
    type CiphertextRing = SingleRNSRingBase<CompositeCyclotomicNumberRing, A, C>;
    type PlaintextRing = NumberRingQuotientByIntBase<CompositeCyclotomicNumberRing, Zn>;
    type PlaintextZnRing = ZnBase;

    #[instrument(skip_all)]
    fn number_ring(&self) -> &CompositeCyclotomicNumberRing {
        &self.number_ring
    }

    #[instrument(skip_all)]
    fn create_plaintext_ring(&self, t: El<BigIntRing>) -> PlaintextRing<Self> {
        NumberRingQuotientByIntBase::new(self.number_ring().clone(), Zn::new(int_cast(t, ZZi64, ZZbig) as u64))
    }

    #[instrument(skip_all)]
    fn create_ciphertext_rings(&self, log2_q: Range<usize>) -> (CiphertextRing<Self>, CiphertextRing<Self>) {
        let number_ring = self.number_ring();
        let required_root_of_unity = 1 << ZZi64.abs_log2_ceil(&(number_ring.m() as i64 * 4)).unwrap();
        let next_prime = |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64));
        let C_rns_base_primes = sample_primes(log2_q.start, log2_q.end, SAMPLE_PRIMES_SIZE, &next_prime).unwrap();
        let C_rns_base = zn_rns::Zn::new(C_rns_base_primes.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect::<Vec<_>>(), ZZbig);

        let Cmul_modulus_size = 2 * ZZbig.abs_log2_ceil(C_rns_base.modulus()).unwrap() + number_ring.small_basis_product_expansion_factor().log2().ceil() as usize;
        let Cmul_rns_base_primes = extend_sampled_primes(&C_rns_base_primes, Cmul_modulus_size + SAMPLE_PRIMES_MINOFFSET, Cmul_modulus_size + SAMPLE_PRIMES_MAXOFFSET, SAMPLE_PRIMES_SIZE, &next_prime).unwrap();
        let Cmul_rns_base = zn_rns::Zn::new(Cmul_rns_base_primes.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect(), ZZbig);

        let max_log2_n = 1 + ZZi64.abs_log2_ceil(&(self.number_ring().m() as i64)).unwrap();
        let C_convolutions = C_rns_base.as_iter().map(|Zp| C::new(*Zp, max_log2_n)).map(Arc::new).collect::<Vec<_>>();
        let Cmul_convolutions = Cmul_rns_base.as_iter().map(|Zp| match C_rns_base.as_iter().enumerate().filter(|(_, C_Zp)| C_Zp.get_ring() == Zp.get_ring()).next() {
            Some((i, _)) => C_convolutions.at(i).clone(),
            None => Arc::new(C::new(*Zp, max_log2_n))
        }).collect();

        let C_mul = SingleRNSRingBase::new_with_alloc(
            number_ring.clone(),
            zn_rns::Zn::new(Cmul_rns_base.as_iter().cloned().collect(), ZZbig),
            self.ciphertext_allocator.clone(),
            Cmul_convolutions
        );

        let dropped_indices = RNSFactorIndexList::from((0..C_mul.base_ring().len()).filter(|i| C_rns_base.as_iter().all(|Zp| Zp.get_ring() != C_mul.base_ring().at(*i).get_ring())), C_mul.base_ring().len());
        let C = RingValue::from(C_mul.get_ring().drop_rns_factor(&dropped_indices));
        assert!(C.base_ring().get_ring() == C_rns_base.get_ring());
        return (C, C_mul);
    }
}

///
/// Forces a ring element to be internally stored in double-RNS representation.
/// 
/// Use in benchmarks, when you want to control which representation the inputs
/// to the benchmarked code have.
/// 
pub fn force_double_rns_repr<Params, NumberRing, A>(C: &CiphertextRing<Params>, x: El<CiphertextRing<Params>>) -> El<CiphertextRing<Params>>
    where Params: BFVInstantiation<CiphertextRing = ManagedDoubleRNSRingBase<NumberRing, A>>,
        NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    C.get_ring().into_doublerns(x).map(|x| C.get_ring().from_double_rns_repr(x)).unwrap_or(C.zero())
}

fn t_fits_zn_64<I>(ZZ: I, t: &El<I>) -> Option<Zn>
    where I: RingStore,
        I::Type: IntegerRing
{
    if ZZ.abs_log2_ceil(t).unwrap() <= 50 {
        Some(Zn::new(int_cast(ZZ.clone_el(t), ZZi64, ZZ) as u64))
    } else {
        None
    }
}

fn temporarily_extend_rns_base<'a>(current: &'a zn_rns::Zn<Zn, BigIntRing>, by_bits: usize) -> RNSSharedBaseConversion {
    let current_log2_modulus = ZZbig.abs_log2_ceil(current.modulus()).unwrap();
    let new_log2_modulus = current_log2_modulus + by_bits;

    let extended_rns_base = extend_sampled_primes(
        &current.as_iter().map(|ring| int_cast(*ring.modulus() as i64, ZZbig, ZZi64)).collect::<Vec<_>>(),
        new_log2_modulus + 10,
        new_log2_modulus + 67,
        57,
        |bound| prev_prime(ZZbig, bound)
    ).unwrap().into_iter().map(|modulus| Zn::new(int_cast(modulus, ZZi64, ZZbig) as u64)).collect::<Vec<_>>();

    let to_extended = RNSSharedBaseConversion::new_with_alloc(
        extended_rns_base[..current.len()].iter().cloned().collect::<Vec<_>>(),
        Vec::new(),
        extended_rns_base[current.len()..].iter().cloned().collect::<Vec<_>>(),
        Global
    );

    to_extended
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
pub fn test_setup_bfv<Params: BFVInstantiation>(params: Params) -> (PlaintextRing<Params>, CiphertextRing<Params>, CiphertextRing<Params>, SecretKey<Params>, RelinKey<Params>, El<PlaintextRing<Params>>, Ciphertext<Params>) {
    let P = params.create_plaintext_ring(int_cast(17, ZZbig, ZZi64));
    assert!(P.number_ring().galois_group().m() >= 100);
    assert!(P.number_ring().galois_group().m() < 1000);
    let (C, C_mul) = params.create_ciphertext_rings(790..800);
    let sk = Params::gen_sk(&C, rand::rng(), SecretKeyDistribution::UniformTernary);
    let rk = Params::gen_rk(&C, rand::rng(), &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2);
    let m = P.int_hom().map(2);
    let ct = Params::enc_sym(&P, &C, rand::rng(), &m, &sk, 3.2);
    return (P, C, C_mul, sk, rk, m, ct);
}

#[test]
fn test_pow2_enc_dec() {
    let (P, C, _C_mul, sk, _rk, m, ct) = test_setup_bfv(Pow2BFV::new(1 << 8));
    assert_el_eq!(&P, m, Pow2BFV::dec(&P, &C, ct, &sk));
}

#[test]
fn test_pow2_hom_galois() {
    let (P, C, _C_mul, sk, rk, _, _) = test_setup_bfv(Pow2BFV::new(1 << 8));
    let gk = Pow2BFV::gen_gk(&C, rand::rng(), &sk, &P.acting_galois_group().from_representative(3), rk.0.gadget_vector_digits(), 3.2);

    let m = P.canonical_gen();
    let ct = Pow2BFV::enc_sym(&P, &C, rand::rng(), &m, &sk, 3.2);
    let res = Pow2BFV::hom_galois(&C, ct, &P.acting_galois_group().from_representative(3), &gk);
    assert_el_eq!(&P, &P.pow(P.canonical_gen(), 3), Pow2BFV::dec(&P, &C, res, &sk));
}

#[test]
fn test_composite_hom_galois() {
    let (P, C, _C_mul, sk, rk, _, _) = test_setup_bfv(CompositeSingleRNSBFV::new(17, 31));
    let gk = CompositeSingleRNSBFV::gen_gk(&C, rand::rng(), &sk, &P.acting_galois_group().from_representative(3), rk.0.gadget_vector_digits(), 3.2);

    let m = P.canonical_gen();
    let ct = CompositeSingleRNSBFV::enc_sym(&P, &C, rand::rng(), &m, &sk, 3.2);
    let res = CompositeSingleRNSBFV::hom_galois(&C, ct, &P.acting_galois_group().from_representative(3), &gk);
    assert_el_eq!(&P, &P.pow(P.canonical_gen(), 3), CompositeSingleRNSBFV::dec(&P, &C, res, &sk));
}

#[test]
fn test_pow2_mul() {
    let (P, C, C_mul, sk, rk, _, ct) = test_setup_bfv(Pow2BFV::new(1 << 8));
    let res = Pow2BFV::hom_mul(&P, &C, &C_mul, Pow2BFV::clone_ct(&C, &ct), ct, &rk);
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BFV::dec(&P, &C, res, &sk));
}

#[test]
fn test_composite_mul() {
    let (P, C, C_mul, sk, rk, _, ct) = test_setup_bfv(CompositeBFV::new(17, 31));
    let res = CompositeBFV::hom_mul(&P, &C, &C_mul, CompositeBFV::clone_ct(&C, &ct), ct, &rk);
    assert_el_eq!(&P, &P.int_hom().map(4), &CompositeBFV::dec(&P, &C, res, &sk));

    let (P, C, C_mul, sk, rk, _, ct) = test_setup_bfv(CompositeSingleRNSBFV::new(17, 31));
    let res = CompositeSingleRNSBFV::hom_mul(&P, &C, &C_mul, CompositeSingleRNSBFV::clone_ct(&C, &ct), ct, &rk);
    assert_el_eq!(&P, &P.int_hom().map(4), &CompositeSingleRNSBFV::dec(&P, &C, res, &sk));
}

#[test]
fn test_pow2_large_t() {    
    let instantiation = Pow2BFV::new(1 << 11);
    let P = instantiation.create_plaintext_ring(ZZbig.power_of_two(50));
    let (C, C_mul) = instantiation.create_ciphertext_rings(500..520);
    let sk = Pow2BFV::gen_sk(&C, rand::rng(), SecretKeyDistribution::UniformTernary);
    let rk = Pow2BFV::gen_rk(&C, rand::rng(), &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2);

    let m = P.inclusion().compose(P.base_ring().can_hom(&ZZbig).unwrap()).map(ZZbig.add(ZZbig.power_of_two(49), ZZbig.one()));
    let ct = Pow2BFV::enc_sym(&P, &C, rand::rng(), &m, &sk, 3.2);
    let res = Pow2BFV::hom_mul(&P, &C, &C_mul, Pow2BFV::clone_ct(&C, &ct), Pow2BFV::clone_ct(&C, &ct), &rk);

    assert_el_eq!(&P, &P.one(), Pow2BFV::dec(&P, &C, res, &sk));
}

#[test]
#[ignore]
fn measure_time_pow2_bfv_basic_ops() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    tracing_subscriber::registry().with(chrome_layer).init();

    let mut rng = rand::rng();
    
    let params = Pow2BFV::new(1 << 16);
    
    let P = log_time::<_, _, true, _>("CreatePtxtRing", |[]|
        params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64))
    );
    let (C, C_mul) = log_time::<_, _, true, _>("CreateCtxtRing", |[]|
        params.create_ciphertext_rings(790..800)
    );

    let sk = log_time::<_, _, true, _>("GenSK", |[]| 
        Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary)
    );

    let m = P.int_hom().map(2);
    let ct = log_time::<_, _, true, _>("EncSym", |[]|
        Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2)
    );

    let res = log_time::<_, _, true, _>("HomAddPlain", |[]| 
        Pow2BFV::hom_add_plain(&P, &C, &m, Pow2BFV::clone_ct(&C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BFV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomAdd", |[]| 
        Pow2BFV::hom_add(&C, Pow2BFV::clone_ct(&C, &ct), &ct)
    );
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BFV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomMulPlain", |[]| 
        Pow2BFV::hom_mul_plain(&P, &C, &m, Pow2BFV::clone_ct(&C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BFV::dec(&P, &C, res, &sk));

    let rk = log_time::<_, _, true, _>("GenRK", |[]| 
        Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2)
    );
    let ct2 = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res = log_time::<_, _, true, _>("HomMul", |[]| 
        Pow2BFV::hom_mul(&P, &C, &C_mul, ct, ct2, &rk)
    );
    assert_el_eq!(&P, &P.int_hom().map(4), &Pow2BFV::dec(&P, &C, res, &sk));
}

#[test]
#[ignore]
fn measure_time_double_rns_composite_bfv_basic_ops() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    tracing_subscriber::registry().with(chrome_layer).init();

    let mut rng = rand::rng();
    
    let params = CompositeBFV::new(127, 337);
    
    let P = log_time::<_, _, true, _>("CreatePtxtRing", |[]|
        params.create_plaintext_ring(int_cast(4, ZZbig, ZZi64))
    );
    let (C, C_mul) = log_time::<_, _, true, _>("CreateCtxtRing", |[]|
        params.create_ciphertext_rings(1090..1100)
    );

    let sk = log_time::<_, _, true, _>("GenSK", |[]| 
        CompositeBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary)
    );
    
    let m = P.int_hom().map(3);
    let ct = log_time::<_, _, true, _>("EncSym", |[]|
        CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2)
    );
    assert_el_eq!(&P, &P.int_hom().map(3), &CompositeBFV::dec(&P, &C, CompositeBFV::clone_ct(&C, &ct), &sk));

    let res = log_time::<_, _, true, _>("HomAdd", |[]| 
        CompositeBFV::hom_add(&C, CompositeBFV::clone_ct(&C, &ct), &ct)
    );
    assert_el_eq!(&P, &P.int_hom().map(2), &CompositeBFV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomAddPlain", |[]| 
        CompositeBFV::hom_add_plain(&P, &C, &m, CompositeBFV::clone_ct(&C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(2), &CompositeBFV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomMulPlain", |[]| 
        CompositeBFV::hom_mul_plain(&P, &C, &m, CompositeBFV::clone_ct(&C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeBFV::dec(&P, &C, res, &sk));

    let rk = log_time::<_, _, true, _>("GenRK", |[]| 
        CompositeBFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2)
    );
    let ct2 = CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res = log_time::<_, _, true, _>("HomMul", |[]| 
        CompositeBFV::hom_mul(&P, &C, &C_mul, ct, ct2, &rk)
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeBFV::dec(&P, &C, res, &sk));
}

#[test]
#[ignore]
fn measure_time_single_rns_composite_bfv_basic_ops() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    tracing_subscriber::registry().with(chrome_layer).init();

    let mut rng = rand::rng();
    
    let params = CompositeSingleRNSBFV::new(127, 337);

    let P = log_time::<_, _, true, _>("CreatePtxtRing", |[]|
        params.create_plaintext_ring(int_cast(4, ZZbig, ZZi64))
    );
    let (C, C_mul) = log_time::<_, _, true, _>("CreateCtxtRing", |[]|
        params.create_ciphertext_rings(1090..1100)
    );

    let sk = log_time::<_, _, true, _>("GenSK", |[]| 
        CompositeSingleRNSBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary)
    );

    let m = P.int_hom().map(3);
    let ct = log_time::<_, _, true, _>("EncSym", |[]|
        CompositeSingleRNSBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2)
    );

    let res = log_time::<_, _, true, _>("HomAddPlain", |[]| 
        CompositeSingleRNSBFV::hom_add_plain(&P, &C, &m, CompositeSingleRNSBFV::clone_ct(&C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(2), &CompositeSingleRNSBFV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomAdd", |[]| 
        CompositeSingleRNSBFV::hom_add(&C, CompositeSingleRNSBFV::clone_ct(&C, &ct), &ct)
    );
    assert_el_eq!(&P, &P.int_hom().map(2), &CompositeSingleRNSBFV::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomMulPlain", |[]| 
        CompositeSingleRNSBFV::hom_mul_plain(&P, &C, &m, CompositeSingleRNSBFV::clone_ct(&C, &ct))
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeSingleRNSBFV::dec(&P, &C, res, &sk));

    let rk = log_time::<_, _, true, _>("GenRK", |[]| 
        CompositeSingleRNSBFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2)
    );
    let ct2 = CompositeSingleRNSBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res = log_time::<_, _, true, _>("HomMul", |[]| 
        CompositeSingleRNSBFV::hom_mul(&P, &C, &C_mul, ct, ct2, &rk)
    );
    assert_el_eq!(&P, &P.int_hom().map(1), &CompositeSingleRNSBFV::dec(&P, &C, res, &sk));
}