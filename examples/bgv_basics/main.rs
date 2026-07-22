// Fheanor completely relies on unstable Rust features
#![allow(non_snake_case)]

// For a guided explanation of this example, see the doc
#![doc = include_str!("Readme.md")]

use fheanor::bgv::*;
use fheanor::number_ring::NumberRingQuotientStore;
use fheanor::bgv::modswitch::drop_rns_factors_balanced;
use fheanor::number_ring::galois::CyclotomicGaloisGroupOps;
use fheanor::gadget_product::digits::*;
use rand::{SeedableRng, rngs::StdRng};
use feanor_math::integer::*;
use feanor_math::primitive_int::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnRingStore;
use feanor_math::ring::RingStore;
use feanor_math::algorithms::eea::signed_gcd;
use feanor_math::seq::*;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::assert_el_eq;

fn main() {
    let params = Pow2BGV::new(1 << 14);
    let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);

    let plaintext_modulus = int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING);
    let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(BigIntRing::RING.clone_el(&plaintext_modulus));
    assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), plaintext_modulus, BigIntRing::RING)));

    println!("N        = {}", C_initial.rank());
    println!("m        = {}", C_initial.acting_galois_group().m());
    println!("log2(q)  = {}", BigIntRing::RING.abs_log2_ceil(C_initial.base_ring().modulus()).unwrap());

    let mut rng = StdRng::from_seed([1; 32]);
    let sk = Pow2BGV::gen_sk(&C_initial, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BGV::gen_rk(&P, &C_initial, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(2, C_initial.base_ring().len()), 3.2);

    let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
        P.base_ring().int_hom().map(i)
    ));
    let enc_x = Pow2BGV::enc_sym(&P, &C_initial, &mut rng, &x, &sk, 3.2);

    let enc_x_sqr = Pow2BGV::hom_square(&P, &C_initial, &C_initial, enc_x, &rk);
    
    let num_digits_to_drop = 1;
    let to_drop = drop_rns_factors_balanced(rk.gadget_vector_digits(), num_digits_to_drop);
    let C_new = Pow2BGV::mod_switch_down_C(&C_initial, &to_drop);
    
    println!("log2(q') = {}", BigIntRing::RING.abs_log2_ceil(C_new.base_ring().modulus()).unwrap());
    
    let enc_x_modswitch = Pow2BGV::mod_switch_ct(&P, &C_new, &C_initial, enc_x_sqr);
    let sk_modswitch = Pow2BGV::mod_switch_sk(&C_new, &C_initial, &sk);
    let rk_modswitch = Pow2BGV::mod_switch_down_rk(&C_new, &C_initial, &rk);
    
    let enc_x_pow4 = Pow2BGV::hom_square(&P, &C_new, &C_new, enc_x_modswitch, &rk_modswitch);
    assert_eq!(22, Pow2BGV::noise_budget(&P, &C_new, &enc_x_pow4, &sk_modswitch));
    let dec_x_pow4 = Pow2BGV::dec(&P, &C_new, enc_x_pow4, &sk_modswitch);
    assert_el_eq!(&P, P.pow(P.clone_el(&x), 4), &dec_x_pow4);
    println!("done");
}