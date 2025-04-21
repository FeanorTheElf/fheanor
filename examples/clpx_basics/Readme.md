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
The reason is that, while CLPX has the "natural" plaintext ring `Z[X]/(Phi_n(X), t(X2))` for a polynomial `t(X)`, this is not the representation one usually wants to work with.
The whole point of using CLPX is to perform computations with large integers, and this can indeed be done using this ring, by observing that we have the isomorphism
```text
  Z[X]/(p, Phi_n(X), t(X)) ~ Z[X]/(p, F(X))
```
where `p` is a large prime (concretely, it should be a prime factor of `Res(t(X), Phi_n(X))`) and `F(X)` some (for now irrelevant) polynomial.
As an example, consider the following possible choices of `n`, `p` and `t(X)`:

| `n`       | `t(X)`      | `p`                                                                |
| --------- | ----------- | ------------------------------------------------------------------ |
| `2^12`    | `X^128 + 2` | `65537`                                                            |
| `2^12`    | `X^32 + 2`  | `67280421310721`                                                   |
| `2^12`    | `X^8 + 2`   | `93461639715357977769163558199606896584051237541638188580280321`   |
| `17 * 5`  | `X - 2`     | `9520972806333758431`                                              |
| `17 * 31` | `X^31 - 2`  | `131071`                                                           |
| `17 * 31` | `X^17 - 2`  | `2147483647`                                                       |
| `17 * 31` | `X - 2`     | *a number so large that we cant easily find its prime factors...*  |

Indeed, as this table shows, a suitable choice of `t` means that we can effectively perform arithmetic modulo some very large modulus.
As users, this means we want to work in the ring `Z[X]/(p, F(X))`, but since the scheme naturally works only over an isomorphic ring with different representation, we need a way to compute this isomorphism - and that is exactly what the "encoding" is for.

More concretely, `create_encoding()` will provide an object of type [`crate::clpx::encoding::CLPXEncoding`], which makes available the ring `Z[X]/(p, F(X))` through the function `plaintext_ring()`.
Hence, we can use CLPX as follows:
```rust
#![feature(allocator_api)]
# use fheanor::clpx::{CLPXCiphertextParams, CiphertextRing, Pow2CLPX};
# use fheanor::DefaultNegacyclicNTT;
# use feanor_math::rings::poly::dense_poly::DensePolyRing;
# use feanor_math::rings::poly::*;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::*;
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
let ZZX = DensePolyRing::new(StaticRing::<i64>::RING, "X");

// we consider the polynomial X^8 + 2, but write it as `t(X^(2048/n1))` with `t = X + 2`;
// the reasons for this will be explained shortly
let n1 = 512;
let [t] = ZZX.with_wrapped_indeterminate(|X| [X + 2]);
let p = BigIntRing::RING.get_ring().parse("93461639715357977769163558199606896584051237541638188580280321", 10).unwrap();
let P = params.create_encoding::<true>(n1, ZZX, t, p);
```