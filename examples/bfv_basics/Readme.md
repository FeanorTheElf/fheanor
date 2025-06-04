# Homomorphic operations using the BFV scheme in Fheanor

BFV was proposed in "Somewhat practical fully homomorphic encryption" by Fan and Vercauteren (<https://ia.cr/2012/144>), and has become one of the most popular and often implemented HE schemes.
In this example, we will show how to use the provided implementation of BFV, without going far into the details of the scheme itself.
For more details on how BFV works and can be implemented, see the original paper, or our example [`crate::examples::bfv_impl_v1`] on how to implement BFV.

## Setting up BFV

In many libraries, there is a central context object that stores all parameters and data associated to the currently used HE scheme.
In Fheanor, we intentionally avoid this approach, and instead have the user manage these parts themselves - don't worry, it's not that much.
More concretely, an instantiation of BFV consists of the following:
 - A ciphertext ring
 - An extended-modulus ciphertext ring, which is only used for intermediate results during homomorphic multiplication
 - One (or multiple) plaintext rings
 - Keys, possibly including a secret key, a relinearization key and Galois keys

While there is no central object storing all of this, Fheanor does provide a simple way of creating these objects from a set of parameters.
There are multiple structs that represent a set of parameters for BFV each, since each of them will lead to a different type for the involved rings.
For example, to setup BFV in a power-of-two cyclotomic number ring `Z[X]/(X^N + 1)`, we could proceed as follows:
```rust
#![feature(allocator_api)]
# use fheanor::bfv::{BFVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BFV};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
type ChosenBFVParamType = Pow2BFV;
let params = ChosenBFVParamType {
    ciphertext_allocator: Global,
    log2_N: 12,
    log2_q_min: 105,
    log2_q_max: 110,
    negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
};
```
Here, we set the RLWE dimension to `2^log2_N = 2^12 = 4096` and the size of the RLWE modulus `q` to be between `105` and `110` bits - these choices give 128 bits of security, according to "Security Guidelines for Implementing Homomorphic Encryption" <https://ia.cr/2024/463>.
Furthermore, we can also specify an allocator - here simply the global allocator [`std::alloc::Global`] - that will be used to allocate memory for ciphertexts, and the type of the NTT implementation to use.
Here, we choose [`crate::DefaultNegacyclicNTT`], which will point either to the (somewhat slow) native NTT, or the HEXL-based NTT (if the feature `use_hexl`) is enabled.

Once we setup the parameters, we can create plaintext and ciphertext rings:
```rust
#![feature(allocator_api)]
# use fheanor::bfv::{BFVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BFV};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# type ChosenBFVParamType = Pow2BFV;
# let params = ChosenBFVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
let (C, C_for_multiplication): (CiphertextRing<ChosenBFVParamType>, CiphertextRing<ChosenBFVParamType>) = params.create_ciphertext_rings();
let plaintext_modulus = 17;
let P: PlaintextRing<ChosenBFVParamType> = params.create_plaintext_ring(plaintext_modulus);
```
Note here that the plaintext modulus `t` was not part of the BFV parameters - the rationale behind this is that a BFV ciphertext often is a valid ciphertext (encrypting a different message) for multiple different plaintext moduli.

After we set this up, we actually won't need the parameter object anymore - to demonstrate this, we delete it here.
```rust
#![feature(allocator_api)]
# use fheanor::bfv::{BFVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BFV};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
# type ChosenBFVParamType = Pow2BFV;
# let params = ChosenBFVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenBFVParamType>, CiphertextRing<ChosenBFVParamType>) = params.create_ciphertext_rings();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBFVParamType> = params.create_plaintext_ring(plaintext_modulus);
drop(params);
```
Next, let's generate the keys we will require later.
Since the type of the ciphertext ring depends on the type of the chosen parameters, all further functions are associated functions of `ChosenBFVParamType`.
While it would be preferable for the BFV implementation not to be tied to any specific parameter object, not doing this would cause problems, see the doc of [`crate::bfv::BFVCiphertextParams`].
```rust
#![feature(allocator_api)]
# use fheanor::bfv::{BFVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BFV};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
# use rand::thread_rng;
# type ChosenBFVParamType = Pow2BFV;
# let params = ChosenBFVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenBFVParamType>, CiphertextRing<ChosenBFVParamType>) = params.create_ciphertext_rings();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBFVParamType> = params.create_plaintext_ring(plaintext_modulus);
# drop(params);
let mut rng = thread_rng();
let sk = ChosenBFVParamType::gen_sk(&C, &mut rng, None);
let digits = 2;
let rk = ChosenBFVParamType::gen_rk(&C, &mut rng, &sk, digits);
```
To generate the keys (as well as for encryption), we require a source of randomness.
Fheanor is internally completely deterministic, hence it takes this source as parameter - in form of a [`rand::CryptoRng`].
Furthermore, we have to decide on a number of "digits" to use when creating the relinearization key.
This is a parameter that is necessary for all forms of key-switching (i.e. also Galois keys), and it refers to the number of parts an element is "decomposed into" when performing a gadget product:
 - A higher number of `digits` will make key generation and key-switching slower, but cause less (additive) noise growth.
 - A low number of `digits` will be faster, but cause higher noise growth. In particular, setting `digits = 1` will lead to immediate noise overflow.

Note that the noise growth during key-switching is additive, i.e. will have a very large impact on very-low-noise ciphertexts, but a negligible impact on ciphertexts that already have a significant level of noise.
Hence, it would be optimal to use a high value for `digits` for the first operations, and a lower value for `digits` later on - however, this might be impractical, since the number of digits is fixed once the key is generated.

Hybrid key switching is less relevant in BFV than in BGV, although using it correctly can give some performance benefits.
Hence, it is currently not implemented for BFV, and we can't specify a special modulus when creating the relinearization key.

## Encryption and Decryption

Next, let's encrypt a message.
The plaintext space of BFV is the ring `R_t = Z[X]/(Phi_m(X), t)`, which we already have created previously.
To encrypt, we now need to encode whatever data we have as an element of this ring (e.g. via [`feanor_math::rings::extension::FreeAlgebra::from_canonical_basis()`] ), and can then encrypt it as follows:
```rust
#![feature(allocator_api)]
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::homomorphism::*;
# use feanor_math::assert_el_eq;
# use feanor_math::ring::*;
# use fheanor::bfv::{BFVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BFV};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
# use rand::thread_rng;
# type ChosenBFVParamType = Pow2BFV;
# let params = ChosenBFVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenBFVParamType>, CiphertextRing<ChosenBFVParamType>) = params.create_ciphertext_rings();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBFVParamType> = params.create_plaintext_ring(plaintext_modulus);
# drop(params);
# let mut rng = thread_rng();
# let sk = ChosenBFVParamType::gen_sk(&C, &mut rng, None);
# let digits = 2;
# let rk = ChosenBFVParamType::gen_rk(&C, &mut rng, &sk, digits);
let x = P.from_canonical_basis((0..(1 << 12)).map(|i| 
    P.base_ring().int_hom().map(i)
));
let enc_x = ChosenBFVParamType::enc_sym(&P, &C, &mut rng, &x, &sk);
let dec_x = ChosenBFVParamType::dec(&P, &C, ChosenBFVParamType::clone_ct(&C, &enc_x), &sk);
assert_el_eq!(&P, &x, &dec_x);
```
For more info on how to create and operate on ring elements, see `feanor-math`.

## Homomorphic operations

BFV supports three types of homomorphic operations on ciphertexts:
 - Addition
 - Multiplication, requires a relinearization key
 - Galois automorphisms, requires a corresponding Galois key

Since we already have a relinearization key, we can perform a homomorphic multiplication.
```rust
#![feature(allocator_api)]
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::homomorphism::*;
# use feanor_math::assert_el_eq;
# use feanor_math::ring::*;
# use fheanor::bfv::{BFVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BFV};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
# use rand::thread_rng;
# type ChosenBFVParamType = Pow2BFV;
# let params = ChosenBFVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenBFVParamType>, CiphertextRing<ChosenBFVParamType>) = params.create_ciphertext_rings();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBFVParamType> = params.create_plaintext_ring(plaintext_modulus);
# drop(params);
# let mut rng = thread_rng();
# let sk = ChosenBFVParamType::gen_sk(&C, &mut rng, None);
# let digits = 2;
# let rk = ChosenBFVParamType::gen_rk(&C, &mut rng, &sk, digits);
# let x = P.from_canonical_basis((0..(1 << 12)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = ChosenBFVParamType::enc_sym(&P, &C, &mut rng, &x, &sk);
# let dec_x = ChosenBFVParamType::dec(&P, &C, ChosenBFVParamType::clone_ct(&C, &enc_x), &sk);
let enc_x_sqr = ChosenBFVParamType::hom_mul(&P, &C, &C_for_multiplication, ChosenBFVParamType::clone_ct(&C, &enc_x), enc_x, &rk);
let dec_x_sqr = ChosenBFVParamType::dec(&P, &C, enc_x_sqr, &sk);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 2), dec_x_sqr);
```
Note that the plaintext ring is actually quite large - we chose `N = 4096` - so printing the result, e.g. via
```rust
#![feature(allocator_api)]
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::homomorphism::*;
# use feanor_math::assert_el_eq;
# use feanor_math::ring::*;
# use fheanor::bfv::{BFVCiphertextParams, CiphertextRing, PlaintextRing, Pow2BFV};
# use fheanor::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
# use rand::thread_rng;
# type ChosenBFVParamType = Pow2BFV;
# let params = ChosenBFVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 12,
#     log2_q_min: 105,
#     log2_q_max: 110,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let (C, C_for_multiplication): (CiphertextRing<ChosenBFVParamType>, CiphertextRing<ChosenBFVParamType>) = params.create_ciphertext_rings();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBFVParamType> = params.create_plaintext_ring(plaintext_modulus);
# drop(params);
# let mut rng = thread_rng();
# let sk = ChosenBFVParamType::gen_sk(&C, &mut rng, None);
# let digits = 2;
# let rk = ChosenBFVParamType::gen_rk(&C, &mut rng, &sk, digits);
# let x = P.from_canonical_basis((0..(1 << 12)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = ChosenBFVParamType::enc_sym(&P, &C, &mut rng, &x, &sk);
# let dec_x = ChosenBFVParamType::dec(&P, &C, ChosenBFVParamType::clone_ct(&C, &enc_x), &sk);
let enc_x_sqr = ChosenBFVParamType::hom_mul(&P, &C, &C_for_multiplication, ChosenBFVParamType::clone_ct(&C, &enc_x), enc_x, &rk);
let dec_x_sqr = ChosenBFVParamType::dec(&P, &C, enc_x_sqr, &sk);
println!("{}", P.format(&dec_x_sqr));
```
will result in quite a long response.