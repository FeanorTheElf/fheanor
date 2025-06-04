#![allow(non_snake_case)]

// For a guided explanation of this example, see the doc
#![doc = include_str!("Readme.md")]

use std::time::Instant;

use feanor_math::ring::*;
use feanor_math::rings::zn::*;
use feanor_math::integer::*;
use fheanor::number_ring::pow2_cyclotomic::*;
use fheanor::number_ring::quotient::*;
use feanor_math::homomorphism::*;
use feanor_math::seq::VectorFn;
use feanor_math::rings::finite::FiniteRingStore;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
use feanor_math::pid::EuclideanRingStore;
use rand::{Rng, RngCore, thread_rng};
use rand_distr::StandardNormal;
use feanor_math::primitive_int::*;
use feanor_math::assert_el_eq;

type NumberRing = Pow2CyclotomicNumberRing;
type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;

fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
    return <CiphertextRing as RingStore>::Type::new(
        Pow2CyclotomicNumberRing::new(ring_degree * 2), 
        zn_big::Zn::new(BigIntRing::RING, q)
    );
}

fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
    return <PlaintextRing as RingStore>::Type::new(
        Pow2CyclotomicNumberRing::new(ring_degree * 2), 
        zn_64::Zn::new(t)
    ); 
}

fn key_gen(ciphertext_ring: &CiphertextRing) -> El<CiphertextRing> {
    let mut rng = thread_rng();
    let sk = ciphertext_ring.from_canonical_basis(
        (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
            (rng.next_u32() as i32 % 3) - 1
        ))
    );
    return sk;
}

fn rlwe_sample(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
    let mut rng = thread_rng();
    let a = ciphertext_ring.random_element(|| rng.next_u64());
    let e = ciphertext_ring.from_canonical_basis(
        (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
            (rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32
        ))
    );
    return (ciphertext_ring.add(e, ciphertext_ring.mul_ref(&a, sk)), ciphertext_ring.negate(a));
}

fn enc_sym(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, x: &El<PlaintextRing>, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
    let (b, a) = rlwe_sample(ciphertext_ring, sk);

    let q = ciphertext_ring.base_ring().modulus();
    let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
    let Δ = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap().map(BigIntRing::RING.rounded_div(BigIntRing::RING.clone_el(q), &t));

    let x_mod_q = ciphertext_ring.from_canonical_basis(
        plaintext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().int_hom().map(
            plaintext_ring.base_ring().smallest_lift(c) as i32
        ))
    );
    return (ciphertext_ring.add(ciphertext_ring.inclusion().mul_map(x_mod_q, Δ), b), a);
}

fn dec(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, ct: &(El<CiphertextRing>, El<CiphertextRing>), sk: &El<CiphertextRing>) -> El<PlaintextRing> {
    let decryption_with_noise = ciphertext_ring.add_ref_fst(&ct.0, ciphertext_ring.mul_ref(&ct.1, sk));

    let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
    let modulo_t = plaintext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    // next, we have to compute the scaling-by-`t/q`, which includes a rounding at the end
    return plaintext_ring.from_canonical_basis(
        ciphertext_ring.wrt_canonical_basis(&decryption_with_noise).iter().map(|c| modulo_t.map(BigIntRing::RING.rounded_div(
            BigIntRing::RING.mul_ref_fst(&t, ciphertext_ring.base_ring().smallest_lift(c)),
            ciphertext_ring.base_ring().modulus()
        )))
    );
}

fn hom_mul_three_component(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, lhs: &(El<CiphertextRing>, El<CiphertextRing>), rhs: &(El<CiphertextRing>, El<CiphertextRing>)) -> (El<CiphertextRing>, El<CiphertextRing>, El<CiphertextRing>) {
    let multiplication_ring = FreeAlgebraImpl::new(
        BigIntRing::RING,
        ciphertext_ring.rank(),
        // we give the modulus as the coefficients of `X^(phi(m))) mod Phi_m`
        [BigIntRing::RING.neg_one()]
    );

    let lift_ciphertext_ring_el = |x: &El<CiphertextRing>| multiplication_ring.from_canonical_basis(
        ciphertext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().smallest_lift(c))
    );
    let lhs_lifted = (lift_ciphertext_ring_el(&lhs.0), lift_ciphertext_ring_el(&lhs.1));
    let rhs_lifted = (lift_ciphertext_ring_el(&rhs.0), lift_ciphertext_ring_el(&rhs.1));

    let product = (
        multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.0),
        multiplication_ring.add(multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.1), multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.0)),
        multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.1)
    );

    let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
    let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    let scale_down_multiplication_ring_el = |x: &El<FreeAlgebraImpl<_, [_; 1]>>| ciphertext_ring.from_canonical_basis(
        multiplication_ring.wrt_canonical_basis(x).iter().map(|c| modulo_q.map(BigIntRing::RING.rounded_div(
            BigIntRing::RING.mul_ref_snd(c, &t),
            ciphertext_ring.base_ring().modulus()
        )))
    );

    return (
        scale_down_multiplication_ring_el(&product.0),
        scale_down_multiplication_ring_el(&product.1),
        scale_down_multiplication_ring_el(&product.2)
    );
}

fn gadget_vector(B: &El<BigIntRing>, digits: usize) -> Vec<El<BigIntRing>> {
    (0..digits).map(|i| BigIntRing::RING.pow(BigIntRing::RING.clone_el(B), i)).collect()
}

fn gadget_decompose(mut x: El<BigIntRing>, B: &El<BigIntRing>, digits: usize) -> Vec<El<BigIntRing>> {
    let mut result = Vec::with_capacity(digits);
    for _ in 0..digits {
        let (quotient, remainder) = BigIntRing::RING.euclidean_div_rem(x, B);
        x = quotient;
        result.push(remainder);
    }
    return result;
}

fn gen_relin_key(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>, B: &El<BigIntRing>, digits: usize) -> Vec<(El<CiphertextRing>, El<CiphertextRing>)> {
    let sk_sqr = ciphertext_ring.pow(ciphertext_ring.clone_el(sk), 2);
    let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    return gadget_vector(B, digits).iter().map(|factor| {
        let (b, a) = rlwe_sample(ciphertext_ring, sk);
        return (ciphertext_ring.add(b, ciphertext_ring.inclusion().mul_ref_map(&sk_sqr, &modulo_q.map_ref(factor))), a);
    }).collect();
}

fn relinearize(ciphertext_ring: &CiphertextRing, three_component_ciphertext: &(El<CiphertextRing>, El<CiphertextRing>, El<CiphertextRing>), relin_key: &[(El<CiphertextRing>, El<CiphertextRing>)], B: &El<BigIntRing>, digits: usize) -> (El<CiphertextRing>, El<CiphertextRing>) {
    let mut c2_decomposition = (0..digits).map(|_| (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().zero()).collect::<Vec<_>>()).collect::<Vec<_>>();
    let c2_wrt_basis = ciphertext_ring.wrt_canonical_basis(&three_component_ciphertext.2);
    let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    for i in 0..c2_wrt_basis.len() {
        let mut coeff_decomposition = gadget_decompose(ciphertext_ring.base_ring().smallest_lift(c2_wrt_basis.at(i)), B, digits).into_iter();
        for j in 0..digits {
            c2_decomposition[j][i] = modulo_q.map(coeff_decomposition.next().unwrap());
        }
    }
    let c2_decomposition = c2_decomposition.into_iter().map(|coefficients| ciphertext_ring.from_canonical_basis(coefficients)).collect::<Vec<_>>();

    return (
        ciphertext_ring.add_ref_fst(&three_component_ciphertext.0, ciphertext_ring.sum(c2_decomposition.iter().zip(relin_key.iter()).map(|(c, (rk0, _))| ciphertext_ring.mul_ref(c, rk0)))),
        ciphertext_ring.add_ref_fst(&three_component_ciphertext.1, ciphertext_ring.sum(c2_decomposition.iter().zip(relin_key.iter()).map(|(c, (_, rk1))| ciphertext_ring.mul_ref(c, rk1))))
    );
}

fn main() {
    let log2_N = 8;
    let C = create_ciphertext_ring(1 << log2_N, BigIntRing::RING.power_of_two(100));
    let P = create_plaintext_ring(1 << log2_N, 5);
    let B = BigIntRing::RING.power_of_two(20);
    let digits = 5;
    let sk = key_gen(&C);
    let relin_key = gen_relin_key(&C, &sk, &B, digits);
    
    let message = P.int_hom().map(2);
    let ciphertext = enc_sym(&P, &C, &message, &sk);
    
    let start = Instant::now();
    let ciphertext_sqr = hom_mul_three_component(&P, &C, &ciphertext, &ciphertext);
    let ciphertext_sqr_relin = relinearize(&C, &ciphertext_sqr, &relin_key, &B, digits);
    let end = Instant::now();
    println!("bfv_impl_v1: Multiplication done in dimension N = {} within {} ms", C.rank(), (end - start).as_millis());

    let result = dec(&P, &C, &ciphertext_sqr_relin, &sk);
    assert_el_eq!(&P, P.pow(message, 2), result);
}