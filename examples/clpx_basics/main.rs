#![allow(non_snake_case)]

// For a guided explanation of this example, see the doc
#![doc = include_str!("Readme.md")]

use fheanor::clpx::{CLPXInstantiation, CiphertextRing, Pow2CLPX, SecretKeyDistribution};
use fheanor::gadget_product::digits::RNSGadgetVectorDigitIndices;
use fheanor::number_ring::*;
use fheanor::number_ring::galois::CyclotomicGaloisGroupOps;
use feanor_math::group::AbelianGroupStore;

use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::poly::*;
use feanor_math::integer::*;
use feanor_math::homomorphism::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::zn::ZnRingStore;
use feanor_math::ring::*;
use feanor_math::assert_el_eq;
use feanor_math::seq::*;

fn main() {
    let params = Pow2CLPX::new(1 << 13);

    let (C, C_for_multiplication): (CiphertextRing<Pow2CLPX>, CiphertextRing<Pow2CLPX>) = params.create_ciphertext_rings(105..110, 10);
    let N = C.rank();
    println!("N        = {}", N);
    println!("m        = {}", C.acting_galois_group().m());
    println!("log2(q)  = {}", BigIntRing::RING.abs_log2_ceil(C.base_ring().modulus()).unwrap());

    let ZZX = DensePolyRing::new(BigIntRing::RING, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(16) + 2]);
    let p = BigIntRing::RING.get_ring().parse("93461639715357977769163558199606896584051237541638188580280321", 10).unwrap();
    println!("t        = {}", ZZX.format(&t));
    println!("p        = {}", BigIntRing::RING.format(&p));

    let galois_group = params.number_ring().galois_group();
    let acting_galois_group = galois_group.get_group().clone().subgroup([galois_group.from_representative(513)]);
    let P = params.create_plaintext_ring::<true>(ZZX, t, p, acting_galois_group);

    let FpX = DensePolyRing::new(P.base_ring(), "X");
    println!("G(X)     = {}", FpX.format(&P.generating_poly(&FpX, FpX.base_ring().identity())));

    let mut rng = rand::rng();
    let sk = Pow2CLPX::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2CLPX::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(2, C.base_ring().len()), 3.2);
    
    let m = P.inclusion().map(P.base_ring().coerce(&BigIntRing::RING, BigIntRing::RING.power_of_two(100)));
    let ct = Pow2CLPX::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let ct_sqr = Pow2CLPX::hom_square(&P, &C, &C_for_multiplication, ct, &rk);
    let res = Pow2CLPX::dec(&P, &C, ct_sqr, &sk);
    
    let res_constant_coeff = P.wrt_canonical_basis(&res).at(0);
    assert_el_eq!(BigIntRing::RING, BigIntRing::RING.power_of_two(200), P.base_ring().smallest_positive_lift(res_constant_coeff));
    println!("done");
}