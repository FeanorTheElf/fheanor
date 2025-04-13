#![allow(non_snake_case)]
#![feature(allocator_api)]

// For a guided explanation of this example, see the doc
#![doc = include_str!("Readme.md")]

use std::alloc::Global;
use std::time::Instant;
use feanor_math::ring::*;
use feanor_math::rings::zn::*;
use feanor_math::assert_el_eq;
use feanor_math::homomorphism::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::integer::*;
use feanor_math::seq::VectorFn;
use feanor_math::seq::VectorView;
use feanor_math::rings::finite::FiniteRingStore;
use feanor_math::primitive_int::StaticRing;
use rand::{Rng, RngCore, thread_rng};
use rand_distr::StandardNormal;
use he_ring::number_ring::*;
use he_ring::rnsconv::bfv_rescale::AlmostExactRescalingConvert;
use he_ring::gadget_product::*;
use he_ring::rnsconv::RNSOperation;
use he_ring::number_ring::pow2_cyclotomic::*;
use he_ring::ciphertext_ring::double_rns_ring::*;
use he_ring::number_ring::quotient::*;
use he_ring::rnsconv::lift::AlmostExactBaseConversion;

type NumberRing = Pow2CyclotomicNumberRing;
type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
type CiphertextRing = DoubleRNSRing<NumberRing>;
type RelinKey = (GadgetProductRhsOperand<<CiphertextRing as RingStore>::Type>, GadgetProductRhsOperand<<CiphertextRing as RingStore>::Type>);

fn create_ciphertext_ring(ring_degree: usize, bitlength_of_q: usize) -> CiphertextRing {
    let number_ring = Pow2CyclotomicNumberRing::new(ring_degree * 2);
    let rns_factors = sample_primes(
        bitlength_of_q - 10, 
        bitlength_of_q, 
        57, 
        |bound| largest_prime_leq_congruent_to_one(int_cast(bound, StaticRing::<i64>::RING, BigIntRing::RING), number_ring. mod_p_required_root_of_unity() as i64).map(|p| int_cast(p, BigIntRing::RING, StaticRing::<i64>::RING))
    ).unwrap();
    return <CiphertextRing as RingStore>::Type::new(
        number_ring,
        zn_rns::Zn::new(rns_factors.into_iter().map(|p| zn_64::Zn::new(int_cast(p, StaticRing::<i64>::RING, BigIntRing::RING) as u64)). collect(), BigIntRing::RING)
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

fn enc_sym(
    plaintext_ring: &PlaintextRing, 
    ciphertext_ring: &CiphertextRing, 
    x: &El<PlaintextRing>, 
    sk: &El<CiphertextRing>
) -> (El<CiphertextRing>, El<CiphertextRing>) {
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

fn dec(
    plaintext_ring: &PlaintextRing, 
    ciphertext_ring: &CiphertextRing, 
    ct: &(El<CiphertextRing>, El<CiphertextRing>), 
    sk: &El<CiphertextRing>
) -> El<PlaintextRing> {
    let decryption_with_noise = ciphertext_ring.add_ref_fst(&ct.0, ciphertext_ring.mul_ref(&ct.1, sk));
    let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
    let modulo_t = plaintext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    return plaintext_ring.from_canonical_basis(
        ciphertext_ring.wrt_canonical_basis(&decryption_with_noise).iter().map(|c| modulo_t.map(BigIntRing::RING.rounded_div(
            BigIntRing::RING.mul_ref_fst(&t, ciphertext_ring.base_ring().smallest_lift(c)),
            ciphertext_ring.base_ring().modulus()
        )))
    );
}

#[allow(unused)]
fn hom_add(
    ciphertext_ring: &CiphertextRing, 
    lhs: &(El<CiphertextRing>, El<CiphertextRing>), 
    rhs: &(El<CiphertextRing>, El<CiphertextRing>)
) -> (El<CiphertextRing>, El<CiphertextRing>) {
    return (ciphertext_ring.add_ref(&lhs.0, &rhs.0), ciphertext_ring.add_ref(&lhs.1, &rhs.1));
}

fn create_multiplication_ring(ciphertext_ring: &CiphertextRing) -> CiphertextRing {
    let number_ring = ciphertext_ring.get_ring().number_ring().clone();
    let rns_factors = extend_sampled_primes(
        &ciphertext_ring.base_ring().as_iter().map(|RNS_factor| int_cast(*RNS_factor.modulus(), BigIntRing::RING, StaticRing::<i64>::RING)).collect::<Vec<_>>(),
        BigIntRing::RING.abs_log2_ceil(ciphertext_ring.base_ring().modulus()).unwrap() * 2 + StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.rank() as i64)).unwrap() + 10, 
        BigIntRing::RING.abs_log2_ceil(ciphertext_ring.base_ring().modulus()).unwrap() * 2 + StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.rank() as i64)).unwrap() + 67, 
        57, 
        |bound| largest_prime_leq_congruent_to_one(int_cast(bound, StaticRing::<i64>::RING, BigIntRing::RING), number_ring.mod_p_required_root_of_unity() as i64).map(|p| int_cast(p, BigIntRing::RING, StaticRing::<i64>::RING))
    ).unwrap().into_iter().map(|p| 
        int_cast(p, StaticRing::<i64>::RING, BigIntRing::RING)
    ).collect::<Vec<_>>();
    return <CiphertextRing as RingStore>::Type::new(
        number_ring,
        zn_rns::Zn::new(rns_factors.into_iter().map(|p| zn_64::Zn::new(p as u64)).collect(), BigIntRing::RING)
    );
}

fn hom_mul_three_component(
    plaintext_ring: &PlaintextRing, 
    ciphertext_ring: &CiphertextRing, 
    multiplication_ring: &CiphertextRing,
    lhs: &(SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>), 
    rhs: &(SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>)
) -> (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>) {
    let (c0, c1) = (&lhs.0, &lhs.1);
    let (c0_prime, c1_prime) = (&rhs.0, &rhs.1);

    let lift_to_multiplication_ring_rnsconv = AlmostExactBaseConversion::new_with(
        ciphertext_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(), 
        multiplication_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(),
        Global
    );
    debug_assert!(lift_to_multiplication_ring_rnsconv.input_rings().iter().zip(ciphertext_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
    debug_assert!(lift_to_multiplication_ring_rnsconv.output_rings().iter().zip(multiplication_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
    let lift_to_multiplication_ring = |x: &SmallBasisEl<_, _>| {
        let mut result = multiplication_ring.get_ring().zero_non_fft();
        lift_to_multiplication_ring_rnsconv.apply(ciphertext_ring.get_ring().as_matrix_wrt_small_basis(&x), multiplication_ring.get_ring().as_matrix_wrt_small_basis_mut(&mut result));
        return multiplication_ring.get_ring().do_fft(result);
    };

    let unscaled_result = (
        multiplication_ring.mul(lift_to_multiplication_ring(&c0), lift_to_multiplication_ring(&c0_prime)),
        multiplication_ring.add(
            multiplication_ring.mul(lift_to_multiplication_ring(&c0), lift_to_multiplication_ring(&c1_prime)),
            multiplication_ring.mul(lift_to_multiplication_ring(&c1), lift_to_multiplication_ring(&c0_prime))
        ),
        multiplication_ring.mul(lift_to_multiplication_ring(&c1), lift_to_multiplication_ring(&c1_prime))
    );

    let scale_down_rnsconv = AlmostExactRescalingConvert::new_with(
        multiplication_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(), 
        vec![ zn_64::Zn::new(*plaintext_ring.base_ring().modulus() as u64) ], 
        ciphertext_ring.base_ring().as_iter().map(|Zp| multiplication_ring.base_ring().as_iter().position(|Zp2| Zp2.modulus() == Zp.modulus()).unwrap()).collect::<Vec<_>>(),
        Global
    );
    debug_assert!(scale_down_rnsconv.input_rings().iter().zip(multiplication_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
    debug_assert!(scale_down_rnsconv.output_rings().iter().zip(ciphertext_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
    let scale_down = |x: El<CiphertextRing>| {
        let mut result = ciphertext_ring.get_ring().zero_non_fft();
        scale_down_rnsconv.apply(multiplication_ring.get_ring().as_matrix_wrt_small_basis(&multiplication_ring.get_ring().undo_fft(x)), ciphertext_ring.get_ring().as_matrix_wrt_small_basis_mut(&mut result));
        return result;
    };

    return (
        scale_down(unscaled_result.0),
        scale_down(unscaled_result.1),
        scale_down(unscaled_result.2)
    );
}

fn gen_relin_key(
    ciphertext_ring: &CiphertextRing, 
    sk: &El<CiphertextRing>, 
    digits: usize
) -> RelinKey {
    let sk_sqr = ciphertext_ring.pow(ciphertext_ring.clone_el(sk), 2);
    let mut result0 = GadgetProductRhsOperand::new(ciphertext_ring.get_ring(), digits);
    let mut result1 = GadgetProductRhsOperand::new(ciphertext_ring.get_ring(), digits);
    
    let gadget_vector_len = result0.gadget_vector(ciphertext_ring.get_ring()).len();
    for i in 0..gadget_vector_len {
        let (b, a) = rlwe_sample(ciphertext_ring, sk);
        let factor = result0.gadget_vector(ciphertext_ring.get_ring()).at(i);
        let (key0, key1) = (ciphertext_ring.add(b, ciphertext_ring.inclusion().mul_ref_map(&sk_sqr, &factor)), a);
        result0.set_rns_factor(ciphertext_ring.get_ring(), i, key0);
        result1.set_rns_factor(ciphertext_ring.get_ring(), i, key1);
    }
    return (result0, result1);
}

fn relinearize(
    ciphertext_ring: &CiphertextRing, 
    three_component_ciphertext: (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>), 
    relin_key: &RelinKey
) -> (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>) {
    let c2_decomposition = GadgetProductLhsOperand::from_double_rns_ring_with(ciphertext_ring.get_ring(), &three_component_ciphertext.2, relin_key.0.gadget_vector_digits());
    let mut result0 = three_component_ciphertext.0;
    ciphertext_ring.get_ring().add_assign_non_fft(&mut result0, &ciphertext_ring.get_ring().undo_fft(c2_decomposition.gadget_product(&relin_key.0, ciphertext_ring.get_ring())));
    let mut result1 = three_component_ciphertext.1;
    ciphertext_ring.get_ring().add_assign_non_fft(&mut result1, &ciphertext_ring.get_ring().undo_fft(c2_decomposition.gadget_product(&relin_key.1, ciphertext_ring.get_ring())));
    return (result0, result1);
}

fn main() {
    let log2_N = 8;
    let C = create_ciphertext_ring(1 << log2_N, 100);
    let C_mul = create_multiplication_ring(&C);
    let P = create_plaintext_ring(1 << log2_N, 5);
    let digits = 2;
    let sk = key_gen(&C);
    let relin_key = gen_relin_key(&C, &sk, digits);
    
    let message = P.int_hom().map(2);
    let ciphertext = enc_sym(&P, &C, &message, &sk);
    
    // we now have to explicity change from double-RNS to small-basis representation to use hom-mul
    let ciphertext = (C.get_ring().undo_fft(ciphertext.0), C.get_ring().undo_fft(ciphertext.1));
    let start = Instant::now();
    let ciphertext_sqr = hom_mul_three_component(&P, &C, &C_mul, &ciphertext, &ciphertext);
    let ciphertext_sqr_relin = relinearize(&C, ciphertext_sqr, &relin_key);
    let end = Instant::now();
    println!("bfv_impl_v2: Multiplication done in dimension N = {} within {} ms", C.rank(), (end - start).as_millis());
    
    // finally, we have to explicitly change representation back
    let ciphertext_sqr_relin = (C.get_ring().do_fft(ciphertext_sqr_relin.0), C.get_ring().do_fft(ciphertext_sqr_relin.1));
    let result = dec(&P, &C, &ciphertext_sqr_relin, &sk);
    assert_el_eq!(&P, P.pow(message, 2), result);
}