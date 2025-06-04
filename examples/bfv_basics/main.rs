// Fheanor completely relies on unstable Rust features
#![feature(allocator_api)]
#![allow(non_snake_case)]

// For a guided explanation of this example, see the doc
#![doc = include_str!("Readme.md")]

use std::{alloc::Global, marker::PhantomData};

use feanor_math::assert_el_eq;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::{BigIntRing, IntegerRingStore};
use feanor_math::ring::{RingExtensionStore, RingStore};
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::zn::ZnRingStore;
use fheanor::bfv::{BFVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BFV};
use fheanor::cyclotomic::CyclotomicRingStore;
use fheanor::DefaultNegacyclicNTT;
use rand::thread_rng;

fn main() {

    type ChosenBFVParamType = Pow2BFV;
    
    let params = ChosenBFVParamType {
        ciphertext_allocator: Global,
        log2_N: 12,
        log2_q_min: 105,
        log2_q_max: 110,
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };

    let (C, C_for_multiplication): (CiphertextRing<ChosenBFVParamType>, CiphertextRing<ChosenBFVParamType>) = params.create_ciphertext_rings();

    println!("N        = {}", C.rank());
    println!("m        = {}", C.m());
    println!("log2(q)  = {}", BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap());
    println!("log2(q') = {}", BigIntRing::RING.abs_log2_ceil(C_for_multiplication.base_ring().modulus()).unwrap());

    let plaintext_modulus = 17;
    let P: PlaintextRing<ChosenBFVParamType> = params.create_plaintext_ring(plaintext_modulus);
    
    let mut rng = thread_rng();

    let sk = ChosenBFVParamType::gen_sk(&C, &mut rng, None);
    let digits = 2;
    let rk = ChosenBFVParamType::gen_rk(&C, &mut rng, &sk, digits);

    let x = P.from_canonical_basis((0..(1 << 12)).map(|i| 
        P.base_ring().int_hom().map(i)
    ));
    let enc_x = ChosenBFVParamType::enc_sym(&P, &C, &mut rng, &x, &sk);
    
    let enc_x_sqr = ChosenBFVParamType::hom_mul(&P, &C, &C_for_multiplication, ChosenBFVParamType::clone_ct(&C, &enc_x), enc_x, &rk);
    let dec_x_sqr = ChosenBFVParamType::dec(&P, &C, enc_x_sqr, &sk);
    assert_el_eq!(&P, P.pow(P.clone_el(&x), 2), dec_x_sqr);
    println!("done");
}