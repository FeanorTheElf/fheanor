# Homomorphic operations using the BFV scheme

BFV was proposed in "Somewhat practical fully homomorphic encryption" by Fan and Vercauteren (<https://ia.cr/2012/144>), and has become one of the most popular and often implemented HE schemes.
In this example, we will show how to use the provided implementation of BFV, without going far into the details of the scheme itself.
For more details on how BFV works and can be implemented, see the original paper, or our example [`crate::examples::bfv_impl_v1`] on how to implement BFV.

## Setting up BFV

In many libraries, there is a central context object that stores all parameters and data associated to the currently used HE scheme.
In this crate, we intentionally avoid this approach, and instead have the user manage these parts themselves - don't worry, it's not that much.
More concretely, an instantiation of BFV consists of the following:
 - A ciphertext ring
 - An extended-modulus ciphertext ring, which is only used for intermediate results during homomorphic multiplication
 - One (or multiple) plaintext rings
 - Keys, possibly including a secret key, a relinearization key and Galois keys

While there is no central object storing all of this, this crate does use structs to represent an instantiation of BFV over a specific number ring.
For example, to setup BFV in a power-of-two cyclotomic number ring `Z[X]/(X^N + 1)`, we could proceed as follows:
```rust
# use anonymizedhelibrary::bfv::{BFVInstantiation, CiphertextRing, PlaintextRing, Pow2BFV};
# use std::marker::PhantomData;
let log2_N = 12;
let params = Pow2BFV::new(2 << log2_N);
```
Here, we set the RLWE dimension to `2^log2_N = 2^12 = 4096`.

Once we setup the parameters, we can create plaintext and ciphertext rings:
```rust
# use anonymizedhelibrary::bfv::*;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# let log2_N = 12;
# let params = Pow2BFV::new(2 << log2_N);
let (C, C_for_multiplication): (CiphertextRing<Pow2BFV>, CiphertextRing<Pow2BFV>) = params.create_ciphertext_rings(105..110);
let P: PlaintextRing<Pow2BFV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
```
Here we create the ciphertext ring with modulus between `105` and `110` bits - these choices give 128 bits of security, according to "Security Guidelines for Implementing Homomorphic Encryption" <https://ia.cr/2024/463> (assuming we use `3.2` as the standard deviation of the RLWE noise).
We also choose the plaintext modulus `t = 17`.

Next, let's generate the keys we will require later.
Since the type of the ciphertext ring depends on the type of the chosen parameters, all further functions are associated functions of [`Pow2BFV`].
While it would be preferable for the BFV implementation not to be tied to any specific parameter object, not doing this would prevent some optimizations, see the doc of [`BFVInstantiation`].
```rust
# use feanor_math::seq::VectorView;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::primitive_int::StaticRing;
# use feanor_math::integer::*;
# use anonymizedhelibrary::gadget_product::digits::RNSGadgetVectorDigitIndices;
# use anonymizedhelibrary::bfv::*;
# use std::marker::PhantomData;
# let log2_N = 12;
# let params = Pow2BFV::new(2 << log2_N);
# let (C, C_for_multiplication): (CiphertextRing<Pow2BFV>, CiphertextRing<Pow2BFV>) = params.create_ciphertext_rings(105..110);
# let P: PlaintextRing<Pow2BFV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
let mut rng = rand::rng();
let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(2, C.base_ring().len()), 3.2);
```
To generate the keys (as well as for encryption), we require a source of randomness.
This crate is internally completely deterministic, hence it takes this source as parameter - in form of a [`rand::CryptoRng`].

Furthermore, for the so-called "relinearization key" `rk`, which is required for multiplications, we have to choose a standard deviation of the included RLWE noise (`3.2` is the standard choice) and a decomposition of all RNS factors into "digits". 
A large number of small digits will cause low noise growth, but larger key-switching keys and slower key-switching.
The function [`RNSGadgetVectorDigitIndices::select_digits()`] will equally distribute all RNS factors across the given number of digits which is usually a reasonable choice.
Here, we choose 2 digits, which might be too low for complex scenarios, but is sufficient for this example.

## Encryption and Decryption

Next, let's encrypt a message.
The plaintext space of BFV is the ring `R_t = Z[X]/(Phi_m(X), t)`, which we already have created previously.
To encrypt, we now need to encode whatever data we have as an element of this ring (e.g. via [`FreeAlgebra::from_canonical_basis()`] ), and can then encrypt it as follows:
```rust
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::homomorphism::*;
# use feanor_math::assert_el_eq;
# use feanor_math::ring::*;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::StaticRing;
# use feanor_math::seq::VectorView;
# use anonymizedhelibrary::gadget_product::digits::RNSGadgetVectorDigitIndices;
# use anonymizedhelibrary::bfv::*;
# use std::marker::PhantomData;
# let log2_N = 12;
# let params = Pow2BFV::new(2 << log2_N);
# let (C, C_for_multiplication): (CiphertextRing<Pow2BFV>, CiphertextRing<Pow2BFV>) = params.create_ciphertext_rings(105..110);
# let P: PlaintextRing<Pow2BFV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# let mut rng = rand::rng();
# let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(2, C.base_ring().len()), 3.2);
let x = P.from_canonical_basis((0..(1 << 12)).map(|i| 
    P.base_ring().int_hom().map(i)
));
let enc_x = Pow2BFV::enc_sym(&P, &C, &mut rng, &x, &sk, 3.2);
let dec_x = Pow2BFV::dec(&P, &C, Pow2BFV::clone_ct(&C, &enc_x), &sk);
assert_el_eq!(&P, &x, &dec_x);
```
For the encryption, we again choose the standard deviation of the RLWE noise to be `3.2`. 

For more info on how to create and operate on ring elements, see `feanor-math`.

## Homomorphic operations

BFV supports three types of homomorphic operations on ciphertexts:
 - Addition
 - Multiplication, requires a relinearization key
 - Galois automorphisms, requires a corresponding Galois key

Since we already have a relinearization key, we can perform a homomorphic multiplication.
```rust
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::homomorphism::*;
# use feanor_math::assert_el_eq;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::StaticRing;
# use feanor_math::ring::*;
# use feanor_math::seq::VectorView;
# use anonymizedhelibrary::gadget_product::digits::RNSGadgetVectorDigitIndices;
# use anonymizedhelibrary::bfv::*;
# use std::marker::PhantomData;
# let log2_N = 12;
# let params = Pow2BFV::new(2 << log2_N);
# let (C, C_for_multiplication): (CiphertextRing<Pow2BFV>, CiphertextRing<Pow2BFV>) = params.create_ciphertext_rings(105..110);
# let P: PlaintextRing<Pow2BFV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# let mut rng = rand::rng();
# let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(2, C.base_ring().len()), 3.2);
# let x = P.from_canonical_basis((0..(1 << 12)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = Pow2BFV::enc_sym(&P, &C, &mut rng, &x, &sk, 3.2);
# let dec_x = Pow2BFV::dec(&P, &C, Pow2BFV::clone_ct(&C, &enc_x), &sk);
let enc_x_sqr = Pow2BFV::hom_mul(&P, &C, &C_for_multiplication, Pow2BFV::clone_ct(&C, &enc_x), enc_x, &rk);
let dec_x_sqr = Pow2BFV::dec(&P, &C, enc_x_sqr, &sk);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 2), dec_x_sqr);
```
Note that the plaintext ring is actually quite large - we chose `N = 4096` - so printing the result, e.g. via
```rust
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::homomorphism::*;
# use feanor_math::assert_el_eq;
# use feanor_math::ring::*;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::StaticRing;
# use feanor_math::seq::VectorView;
# use anonymizedhelibrary::gadget_product::digits::RNSGadgetVectorDigitIndices;
# use anonymizedhelibrary::bfv::*;
# use std::marker::PhantomData;
# let log2_N = 12;
# let params = Pow2BFV::new(2 << log2_N);
# let (C, C_for_multiplication): (CiphertextRing<Pow2BFV>, CiphertextRing<Pow2BFV>) = params.create_ciphertext_rings(105..110);
# let P: PlaintextRing<Pow2BFV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# let mut rng = rand::rng();
# let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(2, C.base_ring().len()), 3.2);
# let x = P.from_canonical_basis((0..(1 << 12)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = Pow2BFV::enc_sym(&P, &C, &mut rng, &x, &sk, 3.2);
# let dec_x = Pow2BFV::dec(&P, &C, Pow2BFV::clone_ct(&C, &enc_x), &sk);
let enc_x_sqr = Pow2BFV::hom_mul(&P, &C, &C_for_multiplication, Pow2BFV::clone_ct(&C, &enc_x), enc_x, &rk);
let dec_x_sqr = Pow2BFV::dec(&P, &C, enc_x_sqr, &sk);
println!("{}", P.format(&dec_x_sqr));
```
will result in quite a long response.

[`BFVInstantiation`]: crate::bfv::BFVInstantiation
[`Pow2BFV`]: crate::bfv::Pow2BFV
[`RNSGadgetVectorDigitIndices`]: crate::gadget_product::digits::RNSGadgetVectorDigitIndices
[`RNSGadgetVectorDigitIndices::select_digits()`]: crate::gadget_product::digits::RNSGadgetVectorDigitIndices::select_digits()
[`FreeAlgebra`]: feanor_math::rings::extension::FreeAlgebra
[`FreeAlgebra::from_canonical_basis()`]: feanor_math::rings::extension::FreeAlgebra::from_canonical_basis()