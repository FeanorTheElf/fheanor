// Fheanor completely relies on unstable Rust features
#![feature(allocator_api)]
#![allow(non_snake_case)]

// For a guided explanation of this example, see the doc
#![doc = include_str!("Readme.md")]

use fheanor::bgv::{BGVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BGV, KeySwitchKeyParams};
use fheanor::cyclotomic::CyclotomicRingStore;
use fheanor::DefaultNegacyclicNTT;
use fheanor::bgv::modswitch::recommended_rns_factors_to_drop;
use rand::{SeedableRng, rngs::StdRng};
use std::alloc::Global;
use std::marker::PhantomData;
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

    type ChosenBGVParamType = Pow2BGV;
    let params = ChosenBGVParamType {
        ciphertext_allocator: Global,
        log2_N: 13,
        log2_q_min: 210,
        log2_q_max: 220,
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };

    let C_initial: CiphertextRing<ChosenBGVParamType> = params.create_initial_ciphertext_ring();

    let plaintext_modulus = 17;
    let P: PlaintextRing<ChosenBGVParamType> = params.create_plaintext_ring(plaintext_modulus);
    assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(plaintext_modulus, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));

    println!("N        = {}", C_initial.rank());
    println!("n        = {}", C_initial.n());
    println!("log2(q)  = {}", BigIntRing::RING.abs_log2_ceil(C_initial.base_ring().modulus()).unwrap());

    let mut rng = StdRng::from_seed([1; 32]);
    let sk = ChosenBGVParamType::gen_sk(&C_initial, &mut rng, None);
    let rk = ChosenBGVParamType::gen_rk(&P, &C_initial, &mut rng, &sk, &KeySwitchKeyParams::default(2, 0, C_initial.base_ring().len()));

    let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
        P.base_ring().int_hom().map(i)
    ));
    let enc_x = ChosenBGVParamType::enc_sym(&P, &C_initial, &mut rng, &x, &sk);

    let enc_x_sqr = ChosenBGVParamType::hom_mul(&P, &C_initial, &C_initial, ChosenBGVParamType::clone_ct(&P, &C_initial, &enc_x), enc_x, &rk);
    
    let num_digits_to_drop = 1;
    let to_drop = recommended_rns_factors_to_drop(rk.params(), num_digits_to_drop);
    let C_new = ChosenBGVParamType::mod_switch_down_C(&C_initial, &to_drop);
    
    println!("log2(q') = {}", BigIntRing::RING.abs_log2_ceil(C_new.base_ring().modulus()).unwrap());
    
    let enc_x_modswitch = ChosenBGVParamType::mod_switch_down_ct(&P, &C_new, &C_initial, &to_drop, enc_x_sqr);
    let sk_modswitch = ChosenBGVParamType::mod_switch_down_sk(&C_new, &C_initial, &to_drop, &sk);
    let rk_modswitch = ChosenBGVParamType::mod_switch_down_rk(&C_new, &C_initial, &to_drop, &rk);
    
    let enc_x_pow4 = ChosenBGVParamType::hom_mul(&P, &C_new, &C_new, ChosenBGVParamType::clone_ct(&P, &C_initial, &enc_x_modswitch), enc_x_modswitch, &rk_modswitch);
    assert_eq!(22, ChosenBGVParamType::noise_budget(&P, &C_new, &enc_x_pow4, &sk_modswitch));
    let dec_x_pow4 = ChosenBGVParamType::dec(&P, &C_new, enc_x_pow4, &sk_modswitch);
    assert_el_eq!(&P, P.pow(P.clone_el(&x), 4), &dec_x_pow4);
    println!("done");
}