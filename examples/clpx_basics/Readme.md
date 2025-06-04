# Homomorphic operations using the CLPX scheme in Fheanor

CLPX was proposed in "High-Precision Arithmetic in Homomorphic Encryption" by Chen, Laine, Player and Xia (<https://ia.cr/2017/809>), and can be described as a variant of BFV that supports computations with large integers.
As such, its use is very similar to BFV, and we recommend the reader to first have a look at [`crate::examples::bfv_basics`].
In this example, we will then focus on the points that are different from standard BFV.

## Setting up CLPX

The design of CLPX is exactly as for BFV (or BGV), so we start by choosing a ciphertext ring instantiation (i.e. a type implementing [`crate::clpx::CLPXCiphertextParams`], which determines the type of the ciphertext ring that will be used) and use it to set up the ciphertext ring.
```rust
#![feature(allocator_api)]
# use fheanor::clpx::{CLPXCiphertextParams, CiphertextRing, Pow2CLPX};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
type ChosenCLPXParamType = Pow2CLPX;
let params = ChosenCLPXParamType {
    ciphertext_allocator: Global,
    log2_N: 12,
    log2_q_min: 105,
    log2_q_max: 110,
    negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
};
let (C, C_for_multiplication): (CiphertextRing<ChosenCLPXParamType>, CiphertextRing<ChosenCLPXParamType>) = params.create_ciphertext_rings();
```
It turns out that a lot of functionality of CLPX is exactly as in BFV, and the type [`crate::clpx::Pow2CLPX`] is actually just type aliases to its BFV equivalent.

Next, we create the plaintext ring(s).
```rust,should_panic
#![feature(allocator_api)]
# use fheanor::clpx::{CLPXCiphertextParams, CiphertextRing, Pow2CLPX};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
# type ChosenCLPXParamType = Pow2CLPX;
# let params = ChosenCLPXParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenCLPXParamType>, CiphertextRing<ChosenCLPXParamType>) = params.create_ciphertext_rings();
let P = params.create_encoding::</* LOG = */ true>(todo!(), todo!(), todo!(), todo!());
```
This time, the relevant function is called `create_encoding()` instead of `create_plaintext_ring()`, and indeed, it does not produce a ring. 
The reason is that, while CLPX has the "natural" plaintext ring `Z[X]/(Phi_m(X), t(X))` for a polynomial `t(X)`, this is not the representation one usually wants to work with.
The whole point of using CLPX is to perform computations with large integers, and this can indeed be done using this ring, by observing that we have the isomorphism
```text
  Z[X]/(p, Phi_m(X), t(X)) ~ Z[X]/(p, G(X))
```
where `p` is a large prime (concretely, it should be a prime factor of `Res(t(X), Phi_m(X))`) and `G(X)` is some (for now irrelevant) polynomial.
As an example, consider the following possible choices of `m`, `p` and `t(X)`:

| `m`       | `t(X)`      | `p`                                                                |
| --------- | ----------- | ------------------------------------------------------------------ |
| `2^12`    | `X^128 + 2` | `65537`                                                            |
| `2^12`    | `X^32 + 2`  | `67280421310721`                                                   |
| `2^12`    | `X^8 + 2`   | `93461639715357977769163558199606896584051237541638188580280321`   |
| `17 * 5`  | `X - 2`     | `9520972806333758431`                                              |
| `17 * 31` | `X^31 - 2`  | `131071`                                                           |
| `17 * 31` | `X^17 - 2`  | `2147483647`                                                       |
| `17 * 31` | `X - 2`     | *a number so large that we cant easily find its prime factors...*  |

Indeed, as this table shows, a suitable choice of `t` means that we can effectively perform arithmetic modulo some very large modulus.
As users, this means we want to work in the ring `Z[X]/(p, G(X))`, but since the scheme naturally works only over an isomorphic ring with different representation, we need a way to compute this isomorphism - and that is exactly what the "encoding" is for.

More concretely, `create_encoding()` will provide an object of type [`crate::clpx::encoding::CLPXEncoding`], which makes available the ring `Z[X]/(p, G(X))` through the function `plaintext_ring()`.
It also supports computing the isomorphism `Z[X]/(p, G(X)) ~ Z[X]/(p, Phi_m(X), t(X))`, which will be used when encrypting values of this ring.
Hence, we can use CLPX as follows:
```rust
#![feature(allocator_api)]
# use fheanor::clpx::{CLPXCiphertextParams, CiphertextRing, Pow2CLPX};
# use fheanor::DefaultNegacyclicNTT;
# use feanor_math::rings::poly::dense_poly::DensePolyRing;
# use feanor_math::rings::poly::*;
# use feanor_math::integer::*;
# use feanor_math::homomorphism::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::*;
# use feanor_math::assert_el_eq;
# use std::alloc::Global;
# use rand::thread_rng;
# use std::marker::PhantomData;
# type ChosenCLPXParamType = Pow2CLPX;
# let params = ChosenCLPXParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenCLPXParamType>, CiphertextRing<ChosenCLPXParamType>) = params.create_ciphertext_rings();
let ZZX = DensePolyRing::new(StaticRing::<i64>::RING, "X");
let p = BigIntRing::RING.get_ring().parse("93461639715357977769163558199606896584051237541638188580280321", 10).unwrap();
// we consider the polynomial X^8 + 2, but write it as `t(X^(2048/m1))` with `t = X + 2`;
// the reasons for this will be explained shortly
let m1 = 512;
let [t] = ZZX.with_wrapped_indeterminate(|X| [X + 2]);
let P = params.create_encoding::<true>(m1, ZZX, t, p);

let mut rng = thread_rng();
let sk = ChosenCLPXParamType::gen_sk(&C, &mut rng, None);
let m = P.plaintext_ring().inclusion().map(P.plaintext_ring().base_ring().coerce(&BigIntRing::RING, BigIntRing::RING.power_of_two(100)));
let ct = ChosenCLPXParamType::enc_sym(&P, &C, &mut rng, &m, &sk);
let res = ChosenCLPXParamType::dec(&P, &C, ct, &sk);
assert_el_eq!(P.plaintext_ring(), &m, &res);
```
Applying homomorphic operations is just as easy as for BFV as well. 
```rust
#![feature(allocator_api)]
# use fheanor::clpx::{CLPXCiphertextParams, CiphertextRing, Pow2CLPX};
# use fheanor::DefaultNegacyclicNTT;
# use feanor_math::rings::poly::dense_poly::DensePolyRing;
# use feanor_math::rings::poly::*;
# use feanor_math::integer::*;
# use feanor_math::homomorphism::*;
# use feanor_math::primitive_int::*;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::*;
# use feanor_math::assert_el_eq;
# use feanor_math::seq::VectorFn;
# use std::alloc::Global;
# use rand::thread_rng;
# use std::marker::PhantomData;
# type ChosenCLPXParamType = Pow2CLPX;
# let params = ChosenCLPXParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenCLPXParamType>, CiphertextRing<ChosenCLPXParamType>) = params.create_ciphertext_rings();
# let ZZX = DensePolyRing::new(StaticRing::<i64>::RING, "X");
# let m1 = 512;
# let [t] = ZZX.with_wrapped_indeterminate(|X| [X + 2]);
# let p = BigIntRing::RING.get_ring().parse("93461639715357977769163558199606896584051237541638188580280321", 10).unwrap();
# let P = params.create_encoding::<true>(m1, ZZX, t, p);
let mut rng = thread_rng();
let sk = ChosenCLPXParamType::gen_sk(&C, &mut rng, None);
let rk = ChosenCLPXParamType::gen_rk(&C, &mut rng, &sk, 2);
let m = P.plaintext_ring().inclusion().map(P.plaintext_ring().base_ring().coerce(&BigIntRing::RING, BigIntRing::RING.power_of_two(100)));
let ct = ChosenCLPXParamType::enc_sym(&P, &C, &mut rng, &m, &sk);
let ct_sqr = ChosenCLPXParamType::hom_square(&P, &C, &C_for_multiplication, ct, &rk);
let res = ChosenCLPXParamType::dec(&P, &C, ct_sqr, &sk);
let res_constant_coeff = P.plaintext_ring().wrt_canonical_basis(&res).at(0);
assert_el_eq!(BigIntRing::RING, BigIntRing::RING.power_of_two(200), P.plaintext_ring().base_ring().smallest_positive_lift(res_constant_coeff));
```

## Choosing t from a subfield of `R`

In the original paper, it was proposed to choose `t = X - a`, for a small integer `a`.
It is not hard to see that in this case, the modulus we are working with is `Res(X - a, Phi_m(X)) = Phi_m(a)` (or one of its prime factors), and `G(X)` will be a degree-1 polynomial.
Since `Phi_m` has degree `phi(m)`, even for `a = 2`, this modulus will we of size about `phi(m)` bits - for FHE-suitable parameters, this means many thousands bits.
This is usually much larger than required for most applications.

As investigated by Robin Geelen and Frederik Vercauteren in "Fully Homomorphic Encryption for Cyclotomic Prime Moduli", we can instead choose `t` to live in a subfield of the `m`-th cyclotomic number field `Q(𝝵)`.
In these cases, Fheanor makes the restriction that this subfield should also be a cyclotomic field, i.e. `t = t(𝝵^m2)` for some `m2 | m`.
In such a case, we find that `G(X)` will have degree `[Q(𝝵) : Q(𝝵^m2)]`, which is between `phi(m2)` and `m2`.
Observe that all parameter sets displayed in above table - except the last - are of this form.
In particular, this is also why we created the encoding as
```rust
#![feature(allocator_api)]
# use fheanor::clpx::{CLPXCiphertextParams, CiphertextRing, Pow2CLPX};
# use fheanor::DefaultNegacyclicNTT;
# use feanor_math::rings::poly::dense_poly::DensePolyRing;
# use feanor_math::rings::poly::*;
# use feanor_math::integer::*;
# use feanor_math::homomorphism::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::*;
# use feanor_math::assert_el_eq;
# use std::alloc::Global;
# use rand::thread_rng;
# use std::marker::PhantomData;
# type ChosenCLPXParamType = Pow2CLPX;
# let params = ChosenCLPXParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenCLPXParamType>, CiphertextRing<ChosenCLPXParamType>) = params.create_ciphertext_rings();
# let p = BigIntRing::RING.get_ring().parse("93461639715357977769163558199606896584051237541638188580280321", 10).unwrap();
# let ZZX = DensePolyRing::new(StaticRing::<i64>::RING, "X");
let m1 = 512;
let [t] = ZZX.with_wrapped_indeterminate(|X| [X + 2]);
let P = params.create_encoding::<true>(m1, ZZX, t, p);
```
More concretely, here we tell the encoding that `t` lives in the `m1`-th cyclotomic number field, i.e. is `t(𝝵_m1) = t(𝝵_m^m2)` for `m2 = m / m1`.
While it would be possible to figure out which subfield `t` belongs to at runtime, this would actually be quite involved, and is unnecessary in most practical scenarios.