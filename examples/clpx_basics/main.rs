// Fheanor completely relies on unstable Rust features
#![feature(allocator_api)]
#![allow(non_snake_case)]

// For a guided explanation of this example, see the doc
#![doc = include_str!("Readme.md")]

use std::{alloc::Global, marker::PhantomData};

use fheanor::clpx::{CLPXCiphertextParams, CiphertextRing, Pow2CLPX};
use fheanor::cyclotomic::CyclotomicRingStore;
use fheanor::DefaultNegacyclicNTT;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::poly::*;
use feanor_math::integer::*;
use feanor_math::homomorphism::*;
use feanor_math::primitive_int::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::zn::ZnRingStore;
use feanor_math::ring::*;
use feanor_math::assert_el_eq;
use feanor_math::seq::VectorFn;
use rand::thread_rng;

fn main() {
    
    type ChosenCLPXParamType = Pow2CLPX;

    let params = ChosenCLPXParamType {
        ciphertext_allocator: Global,
        log2_N: 12,
        log2_q_min: 105,
        log2_q_max: 110,
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };

    let (C, C_for_multiplication): (CiphertextRing<ChosenCLPXParamType>, CiphertextRing<ChosenCLPXParamType>) = params.create_ciphertext_rings();
    let N = C.rank();
    println!("N        = {}", N);
    println!("n        = {}", C.n());
    println!("log2(q)  = {}", BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap());

    let ZZX = DensePolyRing::new(StaticRing::<i64>::RING, "X");
    let n1 = 512;
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X + 2]);
    let p = BigIntRing::RING.get_ring().parse("93461639715357977769163558199606896584051237541638188580280321", 10).unwrap();
    println!("t        = {}", ZZX.format(&ZZX.evaluate(&t, &ZZX.pow(ZZX.indeterminate(), 2 * N / n1), ZZX.inclusion())));
    println!("p        = {}", BigIntRing::RING.format(&p));

    let P = params.create_encoding::<false>(n1, ZZX, t, p);

    let FpX = DensePolyRing::new(P.plaintext_ring().base_ring(), "X");
    println!("G(X)     = {}", FpX.format(&P.plaintext_ring().generating_poly(&FpX, FpX.base_ring().identity())));

    let mut rng = thread_rng();
    let sk = ChosenCLPXParamType::gen_sk(&C, &mut rng, None);
    let rk = ChosenCLPXParamType::gen_rk(&C, &mut rng, &sk, 2);
    
    let m = P.plaintext_ring().inclusion().map(P.plaintext_ring().base_ring().coerce(&BigIntRing::RING, BigIntRing::RING.power_of_two(100)));
    let ct = ChosenCLPXParamType::enc_sym(&P, &C, &mut rng, &m, &sk);
    let ct_sqr = ChosenCLPXParamType::hom_square(&P, &C, &C_for_multiplication, ct, &rk);
    let res = ChosenCLPXParamType::dec(&P, &C, ct_sqr, &sk);
    
    let res_constant_coeff = P.plaintext_ring().wrt_canonical_basis(&res).at(0);
    assert_el_eq!(BigIntRing::RING, BigIntRing::RING.power_of_two(200), P.plaintext_ring().base_ring().smallest_positive_lift(res_constant_coeff));
    println!("done");
}