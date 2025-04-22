
use std::alloc::Allocator;
use std::alloc::Global;
use std::ops::Range;

use encoding::CLPXBaseEncoding;
use feanor_math::ring::*;
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::poly::PolyRingStore;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::primitive_int::StaticRing;
use feanor_math::integer::*;
use feanor_math::ordered::*;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::seq::*;
use feanor_math::rings::finite::FiniteRingStore;
use tracing::instrument;

use crate::ciphertext_ring::{perform_rns_op, BGFVCiphertextRing};
use crate::number_ring::*;
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
use crate::cyclotomic::*;
use crate::gadget_product::{GadgetProductLhsOperand, GadgetProductRhsOperand};
use crate::ciphertext_ring::double_rns_managed::*;
use crate::ntt::HERingNegacyclicNTT;
use crate::number_ring::odd_cyclotomic::*;
use crate::rnsconv::bfv_rescale::AlmostExactRescalingConvert;
use crate::rnsconv::shared_lift::AlmostExactSharedBaseConversion;
use crate::bfv::{Pow2BFV, CompositeBFV};
use crate::{DefaultCiphertextAllocator, DefaultNegacyclicNTT};
use encoding::*;

use rand::{Rng, CryptoRng};
use rand_distr::StandardNormal;

///
/// Implementation of the isomorphism `Z[X]/(Phi_n(X), t(X^n2), p) ~ Fp[X]/(Phi_n2(X))`
/// that CLPX/GBFV is based on.
/// 
pub mod encoding;

const ZZi64: StaticRing<i64> = StaticRing::RING;
const ZZbig: BigIntRing = BigIntRing::RING;

pub type NumberRing<Params: CLPXCiphertextParams> = <Params::CiphertextRing as BGFVCiphertextRing>::NumberRing;
pub type SecretKey<Params: CLPXCiphertextParams> = El<CiphertextRing<Params>>;
pub type KeySwitchKey<'a, Params: CLPXCiphertextParams> = (GadgetProductOperand<'a, Params>, GadgetProductOperand<'a, Params>);
pub type RelinKey<'a, Params: CLPXCiphertextParams> = KeySwitchKey<'a, Params>;
pub type CiphertextRing<Params: CLPXCiphertextParams> = RingValue<Params::CiphertextRing>;
pub type Ciphertext<Params: CLPXCiphertextParams> = (El<CiphertextRing<Params>>, El<CiphertextRing<Params>>);
pub type GadgetProductOperand<'a, Params: CLPXCiphertextParams> = GadgetProductRhsOperand<Params::CiphertextRing>;

///
/// Trait for types that represent an instantiation of CLPX/GBFV.
/// 
/// The design is very similar to [`super::bfv::BFVCiphertextParams`], for details
/// have a look at that. In particular, the plaintext modulus is not a part
/// of the [`super::bfv::BFVCiphertextParams`], but the (initial) ciphertext modulus size
/// is.
/// 
/// For a few more details on how this works, see [`crate::examples::clpx_basics`].
/// 
pub trait CLPXCiphertextParams {

    type CiphertextRing: BGFVCiphertextRing + CyclotomicRing + FiniteRing;
    
    fn ciphertext_modulus_bits(&self) -> Range<usize>;

    fn number_ring(&self) -> NumberRing<Self>;
     
    fn create_ciphertext_rings(&self) -> (CiphertextRing<Self>, CiphertextRing<Self>);

    #[instrument(skip_all)]
    fn create_encoding<const LOG: bool>(&self, n1: usize, ZZi64X: DensePolyRing<StaticRing<i64>>, t: El<DensePolyRing<StaticRing<i64>>>, p: El<BigIntRing>) -> CLPXEncoding {
        let number_ring = self.number_ring();
        assert!(number_ring.n() % n1 == 0);
        let n2 = number_ring.n() / n1;
        let base_encoding = CLPXBaseEncoding::new::<LOG>(n1, ZZi64X, t, p);
        return CLPXEncoding::new::<LOG>(n2, base_encoding);
    }
    
    #[instrument(skip_all)]
    fn gen_sk<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, mut rng: R, hwt: Option<usize>) -> SecretKey<Self> {
        assert!(hwt.is_none() || hwt.unwrap() * 3 <= C.rank() * 2, "it does not make sense to take more than 2/3 of secret key entries in {{-1, 1}}");
        if let Some(hwt) = hwt {
            let mut result_data = (0..C.rank()).map(|_| 0).collect::<Vec<_>>();
            for _ in 0..hwt {
                let mut i = rng.next_u32() as usize % C.rank();
                while result_data[i] != 0 {
                    i = rng.next_u32() as usize % C.rank();
                }
                result_data[i] = (rng.next_u32() % 2) as i32 * 2 - 1;
            }
            let result = C.from_canonical_basis(result_data.into_iter().map(|c| C.base_ring().int_hom().map(c)));
            return result;
        } else {
            let result = C.from_canonical_basis((0..C.rank()).map(|_| C.base_ring().int_hom().map((rng.next_u32() % 3) as i32 - 1)));
            return result;
        }
    }

    #[instrument(skip_all)]
    fn enc_sym_zero<R: Rng + CryptoRng>(C: &CiphertextRing<Self>, mut rng: R, sk: &SecretKey<Self>) -> Ciphertext<Self> {
        let a = C.random_element(|| rng.next_u64());
        let mut b = C.negate(C.mul_ref(&a, &sk));
        let e = C.from_canonical_basis((0..C.rank()).map(|_| C.base_ring().int_hom().map((rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32)));
        C.add_assign(&mut b, e);
        return (b, a);
    }
    
    #[instrument(skip_all)]
    fn transparent_zero(C: &CiphertextRing<Self>) -> Ciphertext<Self> {
        (C.zero(), C.zero())
    }

    #[instrument(skip_all)]
    fn enc_sym<R: Rng + CryptoRng>(P: &CLPXEncoding, C: &CiphertextRing<Self>, rng: R, m: &El<IsomorphicRing>, sk: &SecretKey<Self>) -> Ciphertext<Self> {
        Self::hom_add_plain(P, C, m, Self::enc_sym_zero(C, rng, sk))
    }

    #[instrument(skip_all)]
    fn dec(P: &CLPXEncoding, C: &CiphertextRing<Self>, ct: Ciphertext<Self>, sk: &SecretKey<Self>) -> El<IsomorphicRing> {
        let (c0, c1) = ct;
        let noisy_m = C.add(c0, C.mul_ref_snd(c1, sk));
        return P.decode(C, &noisy_m);
    }

    #[instrument(skip_all)]
    fn dec_println(P: &CLPXEncoding, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>, sk: &SecretKey<Self>) {
        let m = Self::dec(P, C, Self::clone_ct(C, ct), sk);
        println!("ciphertext (noise budget: {}):", Self::noise_budget(P, C, ct, sk));
        P.plaintext_ring().println(&m);
        println!();
    }

    #[instrument(skip_all)]
    fn hom_add(C: &CiphertextRing<Self>, lhs: Ciphertext<Self>, rhs: &Ciphertext<Self>) -> Ciphertext<Self> {
        let (lhs0, lhs1) = lhs;
        let (rhs0, rhs1) = rhs;
        return (C.add_ref(&lhs0, &rhs0), C.add_ref(&lhs1, &rhs1));
    }
    
    #[instrument(skip_all)]
    fn hom_sub(C: &CiphertextRing<Self>, lhs: Ciphertext<Self>, rhs: &Ciphertext<Self>) -> Ciphertext<Self> {
        let (lhs0, lhs1) = lhs;
        let (rhs0, rhs1) = rhs;
        return (C.sub_ref(&lhs0, rhs0), C.sub_ref(&lhs1, rhs1));
    }
    
    #[instrument(skip_all)]
    fn clone_ct(C: &CiphertextRing<Self>, ct: &Ciphertext<Self>) -> Ciphertext<Self> {
        (C.clone_el(&ct.0), C.clone_el(&ct.1))
    }

    #[instrument(skip_all)]
    fn hom_add_plain(P: &CLPXEncoding, C: &CiphertextRing<Self>, m: &El<IsomorphicRing>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        let m = P.encode(C, m);
        return (C.add(ct.0, m), ct.1);
    }
    
    #[instrument(skip_all)]
    fn hom_mul_plain(P: &CLPXEncoding, C: &CiphertextRing<Self>, m: &El<IsomorphicRing>, ct: Ciphertext<Self>) -> Ciphertext<Self> {
        let m = P.small_preimage(m);
        assert!(P.ZZX().degree(&m).unwrap_or(0) < C.rank());
        let mod_Q =  C.base_ring().can_hom(&ZZbig).unwrap();
        let m_in_C = C.from_canonical_basis(
            (0..C.rank()).map(|i| ZZbig.clone_el(P.ZZX().coefficient_at(&m, i)))
                .map(|c| mod_Q.map(c))
        );
        return (C.mul_ref_snd(ct.0, &m_in_C), C.mul(ct.1, m_in_C));
    }

    #[instrument(skip_all)]
    fn noise_budget(P: &CLPXEncoding, C: &CiphertextRing<Self>, ct: &Ciphertext<Self>, sk: &SecretKey<Self>) -> usize {
        let (c0, c1) = Self::clone_ct(C, ct);
        let noisy_m = C.add(c0, C.mul_ref_snd(c1, sk));
        let best_repr = P.encode(C, &P.decode(C, &noisy_m));
        let noise = C.sub(noisy_m, best_repr);
        let noise_coeffs = C.wrt_canonical_basis(&noise);
        let log2_size_of_noise: usize = (0..C.rank()).map(|i| C.base_ring().integer_ring().abs_log2_ceil(&C.base_ring().smallest_lift(noise_coeffs.at(i))).unwrap_or(0)).max().unwrap();
        let log2_can_norm_t_estimate = P.ZZX().terms(P.t()).map(|(c, _)| ZZbig.abs_log2_ceil(c).unwrap()).max().unwrap() + C.get_ring().number_ring().inf_to_can_norm_expansion_factor().log2().ceil() as usize;
        return ZZbig.abs_log2_ceil(C.base_ring().modulus()).unwrap().saturating_sub(log2_size_of_noise + log2_can_norm_t_estimate);
    }

    #[instrument(skip_all)]
    fn gen_rk<'a, R: Rng + CryptoRng>(C: &'a CiphertextRing<Self>, rng: R, sk: &SecretKey<Self>, digits: usize) -> RelinKey<'a, Self>
        where Self: 'a
    {
        Self::gen_switch_key(C, rng, &C.pow(C.clone_el(sk), 2), sk, digits)
    }

    #[instrument(skip_all)]
    fn gen_switch_key<'a, R: Rng + CryptoRng>(C: &'a CiphertextRing<Self>, mut rng: R, old_sk: &SecretKey<Self>, new_sk: &SecretKey<Self>, digits: usize) -> KeySwitchKey<'a, Self>
        where Self: 'a
    {
        let mut res0 = GadgetProductRhsOperand::new(C.get_ring(), digits);
        let mut res1 = GadgetProductRhsOperand::new(C.get_ring(), digits);
        for digit_i in 0..digits {
            let (c0, c1) = Self::enc_sym_zero(C, &mut rng, new_sk);
            let digit_range = res0.gadget_vector_digits().at(digit_i).clone();
            let factor = C.base_ring().get_ring().from_congruence((0..C.base_ring().len()).map(|i2| {
                let Fp = C.base_ring().at(i2);
                if digit_range.contains(&i2) { Fp.one() } else { Fp.zero() } 
            }));
            let mut payload = C.clone_el(&old_sk);
            C.inclusion().mul_assign_ref_map(&mut payload, &factor);
            C.add_assign_ref(&mut payload, &c0);
            res0.set_rns_factor(C.get_ring(), digit_i, payload);
            res1.set_rns_factor(C.get_ring(), digit_i, c1);
        }
        return (res0, res1);
    }
    
    #[instrument(skip_all)]
    fn hom_mul<'a>(P: &CLPXEncoding, C: &CiphertextRing<Self>, C_mul: &CiphertextRing<Self>, lhs: Ciphertext<Self>, rhs: Ciphertext<Self>, rk: &RelinKey<'a, Self>) -> Ciphertext<Self>
        where Self: 'a
    {
        let (c00, c01) = lhs;
        let (c10, c11) = rhs;

        let lift_to_Cmul = Self::create_lift_to_C_mul(C, C_mul);
        let lift = |c| perform_rns_op(C_mul.get_ring(), C.get_ring(), &c, &lift_to_Cmul);
        let c00_lifted = lift(c00);
        let c01_lifted = lift(c01);
        let c10_lifted = lift(c10);
        let c11_lifted = lift(c11);

        let [mut lifted0, mut lifted1, mut lifted2] = C_mul.get_ring().two_by_two_convolution([&c00_lifted, &c01_lifted], [&c10_lifted, &c11_lifted]);

        let t_in_C_mul = Self::create_t_in_C_mul(P, C_mul);
        C_mul.mul_assign_ref(&mut lifted0, &t_in_C_mul);
        C_mul.mul_assign_ref(&mut lifted1, &t_in_C_mul);
        C_mul.mul_assign_ref(&mut lifted2, &t_in_C_mul);

        let scale_down_to_C = Self::create_scale_down_to_C(P, C, C_mul);
        let scale_down = |c: El<CiphertextRing<Self>>| perform_rns_op(C.get_ring(), C_mul.get_ring(), &c, &scale_down_to_C);
        let res0 = scale_down(lifted0);
        let res1 = scale_down(lifted1);
        let res2 = scale_down(lifted2);

        let op = GadgetProductLhsOperand::from_element_with(C.get_ring(), &res2, rk.0.gadget_vector_digits());
        let (s0, s1) = rk;
        return (C.add_ref(&res0, &op.gadget_product(s0, C.get_ring())), C.add_ref(&res1, &op.gadget_product(s1, C.get_ring())));
    }
    
    #[instrument(skip_all)]
    fn hom_square<'a>(P: &CLPXEncoding, C: &CiphertextRing<Self>, C_mul: &CiphertextRing<Self>, val: Ciphertext<Self>, rk: &RelinKey<'a, Self>) -> Ciphertext<Self>
        where Self: 'a
    {
        let (c0, c1) = val;

        let lift_to_Cmul = Self::create_lift_to_C_mul(C, C_mul);
        let lift = |c| perform_rns_op(C_mul.get_ring(), C.get_ring(), &c, &lift_to_Cmul);
        let c0_lifted = lift(c0);
        let c1_lifted = lift(c1);

        let [mut lifted0, mut lifted1, mut lifted2] = C_mul.get_ring().two_by_two_convolution([&c0_lifted, &c1_lifted], [&c0_lifted, &c1_lifted]);

        let t_in_C_mul = Self::create_t_in_C_mul(P, C_mul);
        C_mul.mul_assign_ref(&mut lifted0, &t_in_C_mul);
        C_mul.mul_assign_ref(&mut lifted1, &t_in_C_mul);
        C_mul.mul_assign_ref(&mut lifted2, &t_in_C_mul);

        let scale_down_to_C = Self::create_scale_down_to_C(P, C, C_mul);
        let scale_down = |c: El<CiphertextRing<Self>>| perform_rns_op(C.get_ring(), C_mul.get_ring(), &c, &scale_down_to_C);
        let res0 = scale_down(lifted0);
        let res1 = scale_down(lifted1);
        let res2 = scale_down(lifted2);

        let op = GadgetProductLhsOperand::from_element_with(C.get_ring(), &res2, rk.0.gadget_vector_digits());
        let (s0, s1) = rk;
        return (C.add_ref(&res0, &op.gadget_product(s0, C.get_ring())), C.add_ref(&res1, &op.gadget_product(s1, C.get_ring())));
    }

    #[instrument(skip_all)]
    fn key_switch<'a>(C: &CiphertextRing<Self>, ct: Ciphertext<Self>, switch_key: &KeySwitchKey<'a, Self>) -> Ciphertext<Self>
        where Self: 'a
    {
        let (c0, c1) = ct;
        let (s0, s1) = switch_key;
        let op = GadgetProductLhsOperand::from_element_with(C.get_ring(), &c1, switch_key.0.gadget_vector_digits());
        return (
            C.add_ref_snd(c0, &op.gadget_product(s0, C.get_ring())),
            op.gadget_product(s1, C.get_ring())
        );
    }
    
    fn create_lift_to_C_mul(C: &CiphertextRing<Self>, C_mul: &CiphertextRing<Self>) -> AlmostExactSharedBaseConversion {
        AlmostExactSharedBaseConversion::new_with(
            C.base_ring().as_iter().map(|R| Zn::new(*R.modulus() as u64)).collect::<Vec<_>>(), 
            Vec::new(),
            C_mul.base_ring().as_iter().skip(C.base_ring().len()).map(|R| Zn::new(*R.modulus() as u64)).collect::<Vec<_>>(),
            Global
        )
    }

    fn create_scale_down_to_C(_P: &CLPXEncoding, C: &CiphertextRing<Self>, C_mul: &CiphertextRing<Self>) -> AlmostExactRescalingConvert {
        AlmostExactRescalingConvert::new_with(
            C_mul.base_ring().as_iter().map(|R| Zn::new(*R.modulus() as u64)).collect::<Vec<_>>(), 
            Vec::new(), 
            (0..C.base_ring().len()).collect(),
            Global
        )
    }

    fn create_t_in_C_mul(P: &CLPXEncoding, C_mul: &CiphertextRing<Self>) -> El<CiphertextRing<Self>> {
        let ZZ_to_Zq = C_mul.base_ring().can_hom(&ZZi64).unwrap();
        C_mul.from_canonical_basis((0..C_mul.rank()).map(|i| if ZZbig.is_zero(P.ZZX().coefficient_at(P.t(), i)) {
            0
        } else {
            int_cast(ZZbig.clone_el(P.ZZX().coefficient_at(P.t(), i)), ZZi64, ZZbig)
        }).map(|c| ZZ_to_Zq.map(c)))
    }
}

pub type Pow2CLPX<A = DefaultCiphertextAllocator, C = DefaultNegacyclicNTT> = Pow2BFV<A, C>;

impl<A: Allocator + Clone + Send + Sync, C: Send + Sync + HERingNegacyclicNTT<Zn>> CLPXCiphertextParams for Pow2CLPX<A, C> {

    type CiphertextRing = ManagedDoubleRNSRingBase<Pow2CyclotomicNumberRing<C>, A>;

    fn number_ring(&self) -> NumberRing<Self> {
        Pow2CyclotomicNumberRing::new_with(2 << self.log2_N)
    }

    fn ciphertext_modulus_bits(&self) -> Range<usize> {
        assert!(self.log2_q_min < self.log2_q_max);
        self.log2_q_min..self.log2_q_max
    }

    #[instrument(skip_all)]
    fn create_ciphertext_rings(&self) -> (CiphertextRing<Self>, CiphertextRing<Self>)  {
        let log2_q = self.ciphertext_modulus_bits();
        let number_ring = self.number_ring();
        let required_root_of_unity = number_ring.mod_p_required_root_of_unity() as i64;

        let mut C_rns_base = sample_primes(log2_q.start, log2_q.end, 56, |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64))).unwrap();
        C_rns_base.sort_unstable_by(|l, r| ZZbig.cmp(l, r));

        let mut Cmul_rns_base = extend_sampled_primes(&C_rns_base, log2_q.end * 2 + 10, log2_q.end * 2 + 67, 57, |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64))).unwrap();
        assert!(ZZbig.is_gt(&Cmul_rns_base[Cmul_rns_base.len() - 1], &C_rns_base[C_rns_base.len() - 1]));
        Cmul_rns_base.sort_unstable_by(|l, r| ZZbig.cmp(l, r));

        let C_rns_base = zn_rns::Zn::new(C_rns_base.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect::<Vec<_>>(), ZZbig);
        let Cmul_rns_base = zn_rns::Zn::new(Cmul_rns_base.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect(), ZZbig);

        let C_mul = ManagedDoubleRNSRingBase::new_with(
            number_ring,
            Cmul_rns_base,
            self.ciphertext_allocator.clone()
        );

        let dropped_indices = (0..C_mul.base_ring().len()).filter(|i| C_rns_base.as_iter().all(|Zp| Zp.get_ring() != C_mul.base_ring().at(*i).get_ring())).collect::<Vec<_>>();
        let C = RingValue::from(C_mul.get_ring().drop_rns_factor(&dropped_indices));
        debug_assert!(C.base_ring().get_ring() == C_rns_base.get_ring());
        return (C, C_mul);
    }
}

pub type CompositeCLPX<A = DefaultCiphertextAllocator> = CompositeBFV<A>;

impl<A: Allocator + Clone + Send + Sync> CLPXCiphertextParams for CompositeCLPX<A> {

    type CiphertextRing = ManagedDoubleRNSRingBase<CompositeCyclotomicNumberRing, A>;
    
    fn ciphertext_modulus_bits(&self) -> Range<usize> {
        self.log2_q_min..self.log2_q_max
    }

    fn number_ring(&self) -> CompositeCyclotomicNumberRing {
        CompositeCyclotomicNumberRing::new(self.n1, self.n2)
    }

    #[instrument(skip_all)]
    fn create_ciphertext_rings(&self) -> (CiphertextRing<Self>, CiphertextRing<Self>)  {
        let log2_q = self.ciphertext_modulus_bits();
        let number_ring = self.number_ring();
        let required_root_of_unity = number_ring.mod_p_required_root_of_unity() as i64;

        let mut C_rns_base = sample_primes(log2_q.start, log2_q.end, 56, |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64))).unwrap();
        C_rns_base.sort_unstable_by(|l, r| ZZbig.cmp(l, r));

        let Cmul_rns_base = extend_sampled_primes(&C_rns_base, log2_q.end * 2, log2_q.end * 2 + 57, 57, |bound| largest_prime_leq_congruent_to_one(int_cast(bound, ZZi64, ZZbig), required_root_of_unity).map(|p| int_cast(p, ZZbig, ZZi64))).unwrap();
        assert!(ZZbig.is_gt(&Cmul_rns_base[Cmul_rns_base.len() - 1], &C_rns_base[C_rns_base.len() - 1]));

        let C_rns_base = zn_rns::Zn::new(C_rns_base.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect::<Vec<_>>(), ZZbig);
        let Cmul_rns_base = zn_rns::Zn::new(Cmul_rns_base.iter().map(|p| Zn::new(int_cast(ZZbig.clone_el(p), ZZi64, ZZbig) as u64)).collect(), ZZbig);

        let C_mul = ManagedDoubleRNSRingBase::new_with(
            number_ring,
            Cmul_rns_base,
            self.ciphertext_allocator.clone()
        );

        let dropped_indices = (0..C_mul.base_ring().len()).filter(|i| C_rns_base.as_iter().all(|Zp| Zp.get_ring() != C_mul.base_ring().at(*i).get_ring())).collect::<Vec<_>>();
        let C = RingValue::from(C_mul.get_ring().drop_rns_factor(&dropped_indices));
        debug_assert!(C.base_ring().get_ring() == C_rns_base.get_ring());
        return (C, C_mul);
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::log_time;
#[cfg(test)]
use rand::thread_rng;
#[cfg(test)]
use std::marker::PhantomData;

#[test]
fn test_composite_clpx_mul() {
    let mut rng = thread_rng();
    let ZZi64X = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZi64X.with_wrapped_indeterminate(|X| [X - 2]);
    let params = CompositeCLPX {
        log2_q_min: 400,
        log2_q_max: 420,
        n1: 17,
        n2: 5,
        ciphertext_allocator: Global
    };
    let p = ZZbig.int_hom().map(131071);

    let P = params.create_encoding::<false>(params.n1, ZZi64X.clone(), t, p);
    let (C, C_mul) = params.create_ciphertext_rings();

    let sk = CompositeCLPX::gen_sk(&C, &mut rng, None);
    let m = P.plaintext_ring().int_hom().map(2);
    let ct = CompositeCLPX::enc_sym(&P, &C, &mut rng, &m, &sk);

    assert_el_eq!(P.plaintext_ring(), &m, &CompositeCLPX::dec(&P, &C, CompositeCLPX::clone_ct(&C, &ct), &sk));

    let rk = CompositeCLPX::gen_rk(&C, &mut rng, &sk, 3);
    let sqr_ct = CompositeCLPX::hom_square(&P, &C, &C_mul, ct, &rk);
    
    assert_el_eq!(P.plaintext_ring(), P.plaintext_ring().int_hom().map(4), &CompositeCLPX::dec(&P, &C, CompositeCLPX::clone_ct(&C, &sqr_ct), &sk));

    let [t] = ZZi64X.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    let params = CompositeCLPX {
        log2_q_min: 400,
        log2_q_max: 420,
        n1: 17,
        n2: 5,
        ciphertext_allocator: Global
    };
    let p = ZZbig.int_hom().map(43691);
    let mut rng = thread_rng();

    let P = params.create_encoding::<false>(params.n1, ZZi64X, t, p);
    let (C, C_mul) = params.create_ciphertext_rings();

    let sk = CompositeCLPX::gen_sk(&C, &mut rng, None);
    let m = P.plaintext_ring().int_hom().map(210);
    let ct = CompositeCLPX::enc_sym(&P, &C, &mut rng, &m, &sk);

    assert_el_eq!(P.plaintext_ring(), &m, &CompositeCLPX::dec(&P, &C, CompositeCLPX::clone_ct(&C, &ct), &sk));

    let rk = CompositeCLPX::gen_rk(&C, &mut rng, &sk, 3);
    let sqr_ct = CompositeCLPX::hom_square(&P, &C, &C_mul, ct, &rk);
    
    assert_el_eq!(P.plaintext_ring(), P.plaintext_ring().int_hom().map(409), &CompositeCLPX::dec(&P, &C, CompositeCLPX::clone_ct(&C, &sqr_ct), &sk));
}


#[test]
fn test_pow2_clpx_mul() {
    let mut rng = thread_rng();
    let ZZi64X = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZi64X.with_wrapped_indeterminate(|X| [X.pow_ref(3) - 2]);
    let params = Pow2CLPX {
        log2_q_min: 400,
        log2_q_max: 420,
        log2_N: 7,
        ciphertext_allocator: Global,
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };
    let p = int_cast(5704689200685129054721, ZZbig, StaticRing::<i128>::RING);

    let P = params.create_encoding::<false>(2 << params.log2_N, ZZi64X.clone(), t, p);
    let (C, C_mul) = params.create_ciphertext_rings();

    let sk = Pow2CLPX::gen_sk(&C, &mut rng, None);
    let m1 = P.plaintext_ring().inclusion().map(P.plaintext_ring().base_ring().coerce(&ZZbig, ZZbig.power_of_two(35)));
    let ct1 = Pow2CLPX::enc_sym(&P, &C, &mut rng, &m1, &sk);
    let m2 = P.plaintext_ring().inclusion().map(P.plaintext_ring().base_ring().coerce(&ZZbig, ZZbig.power_of_two(36)));
    let ct2 = Pow2CLPX::enc_sym(&P, &C, &mut rng, &m2, &sk);

    let rk = Pow2CLPX::gen_rk(&C, &mut rng, &sk, 3);
    let ct_res = Pow2CLPX::hom_mul(&P, &C, &C_mul, ct1, ct2, &rk);
    let res = Pow2CLPX::dec(&P, &C, Pow2CLPX::clone_ct(&C, &ct_res), &sk);
    assert_el_eq!(ZZbig, ZZbig.power_of_two(71), &P.plaintext_ring().base_ring().smallest_positive_lift(P.plaintext_ring().wrt_canonical_basis(&res).at(0)));
}

#[test]
#[ignore]
fn measure_time_composite_clpx() {
    let mut rng = thread_rng();
    let ZZi64X = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZi64X.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    let params = CompositeCLPX {
        log2_q_min: 790,
        log2_q_max: 800,
        n1: 127,
        n2: 337,
        ciphertext_allocator: Global
    };
    let p = ZZbig.coerce(&StaticRing::<i128>::RING, 56713727820156410577229101238628035243);
    let digits = 3;
    
    let P = log_time::<_, _, true, _>("CreateEncoding", |[]|
        params.create_encoding::<false>(params.n1, ZZi64X, t, p)
    );
    let int_to_P = P.plaintext_ring().inclusion().compose(P.plaintext_ring().base_ring().can_hom(&StaticRing::<i128>::RING).unwrap());
    let (C, C_mul) = log_time::<_, _, true, _>("CreateCtxtRing", |[]|
        params.create_ciphertext_rings()
    );

    let sk = log_time::<_, _, true, _>("GenSK", |[]| 
        CompositeCLPX::gen_sk(&C, &mut rng, None)
    );

    let m = int_to_P.map(1 << 63);
    let ct = log_time::<_, _, true, _>("EncSym", |[]|
        CompositeCLPX::enc_sym(&P, &C, &mut rng, &m, &sk)
    );

    let res = log_time::<_, _, true, _>("HomAddPlain", |[]| 
        CompositeCLPX::hom_add_plain(&P, &C, &m, CompositeCLPX::clone_ct(&C, &ct))
    );
    assert_el_eq!(P.plaintext_ring(), &int_to_P.map(1 << 64), &CompositeCLPX::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomAdd", |[]| 
        CompositeCLPX::hom_add(&C, CompositeCLPX::clone_ct(&C, &ct), &ct)
    );
    assert_el_eq!(P.plaintext_ring(), &int_to_P.map(1 << 64), &CompositeCLPX::dec(&P, &C, res, &sk));

    let res = log_time::<_, _, true, _>("HomMulPlain", |[]| 
        CompositeCLPX::hom_mul_plain(&P, &C, &m, CompositeCLPX::clone_ct(&C, &ct))
    );
    assert_el_eq!(P.plaintext_ring(), &int_to_P.map(1 << 126), &CompositeCLPX::dec(&P, &C, res, &sk));

    let rk = log_time::<_, _, true, _>("GenRK", |[]| 
        CompositeCLPX::gen_rk(&C, &mut rng, &sk, digits)
    );
    let res = log_time::<_, _, true, _>("HomMul", |[]| 
        CompositeCLPX::hom_mul(&P, &C, &C_mul, CompositeCLPX::clone_ct(&C, &ct), CompositeCLPX::clone_ct(&C, &ct), &rk)
    );
    assert_el_eq!(P.plaintext_ring(), &int_to_P.map(1 << 126), &CompositeCLPX::dec(&P, &C, res, &sk));
}