#![allow(non_snake_case)]

// For a guided explanation of this example, see the doc
#![doc = include_str!("Readme.md")]

use feanor_math::assert_el_eq;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::{BigIntRing, IntegerRingStore};
use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::{RingExtensionStore, RingStore};
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::seq::VectorView;
use feanor_math::integer::*;
use feanor_math::rings::zn::ZnRingStore;
use anonymizedhelibrary::number_ring::NumberRingQuotientStore;
use anonymizedhelibrary::bfv::*;
use anonymizedhelibrary::number_ring::galois::CyclotomicGaloisGroupOps;
use anonymizedhelibrary::gadget_product::digits::RNSGadgetVectorDigitIndices;

fn main() {    
    let params = Pow2BFV::new(1 << 13);

    let (C, C_for_multiplication): (CiphertextRing<Pow2BFV>, CiphertextRing<Pow2BFV>) = params.create_ciphertext_rings(105..110);

    println!("N        = {}", C.rank());
    println!("m        = {}", C.acting_galois_group().m());
    println!("log2(q)  = {}", BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap());
    println!("log2(q') = {}", BigIntRing::RING.abs_log2_ceil(C_for_multiplication.base_ring().modulus()).unwrap());

    let P: PlaintextRing<Pow2BFV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
    
    let mut rng = rand::rng();

    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(2, C.base_ring().len()), 3.2);

    let x = P.from_canonical_basis((0..(1 << 12)).map(|i| 
        P.base_ring().int_hom().map(i)
    ));
    let enc_x = Pow2BFV::enc_sym(&P, &C, &mut rng, &x, &sk, 3.2);
    
    let enc_x_sqr = Pow2BFV::hom_mul(&P, &C, &C_for_multiplication, Pow2BFV::clone_ct(&C, &enc_x), enc_x, &rk);
    let dec_x_sqr = Pow2BFV::dec(&P, &C, enc_x_sqr, &sk);
    assert_el_eq!(&P, P.pow(P.clone_el(&x), 2), dec_x_sqr);
    println!("done");
}