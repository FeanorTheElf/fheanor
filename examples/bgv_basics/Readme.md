# Homomorphic operations using the BGV scheme in HE-Ring

BGV was proposed in "Leveled fully homomorphic encryption without bootstrapping" by Z. Brakerski, C. Gentry, and V. Vaikuntanathan (<https://dl.acm.org/doi/10.1145/2090236.2090262>), and is the foundation of the family of "second generation" HE schemes.
In this example, we will show how to use the provided implementation of BGV, without going deep into the mathematical details of the scheme.
In comparison to BFV (for a short introduction, see [`crate::examples::bfv_basics`]), BGV allows for a somewhat more efficient implementation, but the necessity for the user to manually manage the modulus chain introduces significant additional complexity.
We note that some libraries (like HElib) support automatic management of the modulus chain, but this is not implemented in HE-Ring.

## Some BGV basics, modulus-switching and the modulus chain

When one encrypts a message to get a BGV ciphertext, a noise term `e` is always included - this is necessary for security.
This noise term is small compared to the ciphertext modulus `q`, and as long as it stays this way, the message can be retrieved through decryption.
However, homomorphic operations increase the size of `e`.
In the case of addition or multiplication with a plaintext, these operations are just applied to `e`, hence the *relative error* `|e| / q` increases at most by a constant factor.
The same is the case for homomorphic multiplication in BFV, i.e. multiplying two ciphertexts with noise terms `e` and `e'` results in a ciphertext with noise of size `C (|e| + |e'|)`, for a (rather large) constant `C`.

However, without further action, in BGV the noise of homomorphic multiplication result will have size `|e| |e'|`, i.e. it grows multiplicatively.
Once `|e|` resp. `|e'|` get somewhat large, this results in catastrophic noise growth, and decryption failures.
Fortunately, this can be fixed - using modulus-switching as proposed by the original authors.
More concretely, modulus-switching reduces the absolute size of `e` while keeping the relative noise `|e| / q` constant - by changing the ciphertext modulus `q` to some smaller ciphertext modulus `q'`.
The goal is then that `|e|` remains a small constant, and instead `q` progressively shrinks.
When done correctly, the relative noise of a homomorphic multiplication result becomes again linear in the relative input noise, i.e. `C (|e|/q + |e'|/q)`.

This is great, but means we have to manage the "chain" of ciphertext moduli `q > q' > q'' > ...`, and perform modulus-switching at the right places.
In most cases, this means we modulus-switch before every multiplication (except the first one), but this is not always the optimal strategy.
In HE-Ring, this task is currently left to the user, which means that using BGV introduces more complexity than BFV.

## Setting up BGV

In many libraries, there is a central context object that stores all parameters and data associated to the currently used HE scheme.
In HE-Ring, we intentionally avoid this approach, and instead have the use manage these parts themselves.
More concretely, an instantiation of BGV consists of the following:
 - One Ciphertext ring for each modulus `q` in the ciphertext modulus chain `q > q' > q'' > ...`
 - One (or multiple) plaintext rings
 - Keys, possibly including a secret key, a relinearization key and Galois keys

While there is no central object storing all of this, HE-Ring does provide a simple way of creating these objects from a set of parameters.
There are multiple structs that represent a set of parameters for BGV each, since each of them will lead to a different type for the involved rings.
For example, to setup BGV in a power-of-two cyclotomic number ring `Z[X]/(X^N + 1)`, we could proceed as follows:
```rust
#![feature(allocator_api)]
# use he_ring::bgv::*;
# use he_ring::DefaultNegacyclicNTT;
# use std::alloc::Global;
# use std::marker::PhantomData;
type ChosenBGVParamType = Pow2BGV;
let params = ChosenBGVParamType {
    ciphertext_allocator: Global,
    log2_N: 13,
    log2_q_min: 210,
    log2_q_max: 220,
    negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
};
```
Here, we set the RLWE dimension to `2^log2_N = 2^13 = 8192` and the size of the RLWE modulus `q` to be between `210` and `220` bits - these choices give 128 bits of security, according to "Security Guidelines for Implementing Homomorphic Encryption" <https://ia.cr/2024/463>.
Furthermore, we can also specify an allocator - here simply the global allocator [`std::alloc::Global`] - that will be used to allocate memory for ciphertexts, and the type of the NTT implementation to use.
Moreover, we choose [`crate::DefaultNegacyclicNTT`], which will point either to the (somewhat slow) native NTT, or the HEXL-based NTT (if the feature `use_hexl`) is enabled.
Finally, `log2_q_min` and `log2_q_max` refer to the allowed range for the bitlength of the largest ciphertext modulus `q`, i.e. the first one in the modulus chain `q > q' > q'' > ...`.
We will later derive the other moduli `q', q'', ...` from `q` by "dropping" factors of `q`.
This works, since `q` is chosen as a product of many approximately 57 bit long primes.

Using this, we can now create the plaintext ring and initial ciphertext ring via
```rust
#![feature(allocator_api)]
# use he_ring::bgv::*;
# use he_ring::DefaultNegacyclicNTT;
# use rand::{SeedableRng, rngs::StdRng};
# use std::alloc::Global;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# type ChosenBGVParamType = Pow2BGV;
# let params = ChosenBGVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 13,
#     log2_q_min: 210,
#     log2_q_max: 220,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
let C_initial: CiphertextRing<ChosenBGVParamType> = params.create_initial_ciphertext_ring();
let plaintext_modulus = 17;
let P: PlaintextRing<ChosenBGVParamType> = params.create_plaintext_ring(plaintext_modulus);
assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(plaintext_modulus, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
```
Note here that the plaintext modulus `t` was not part of the BGV parameters - the rationale behind this is that a BGV ciphertext often is a valid ciphertext (encrypting a different message) for multiple different plaintext moduli.
Moreover, it is important that `t` must be coprime to `q`, otherwise there is no security.
However, since `q` is sampled using large primes of up to 56 bits, this is unlikely to be a problem.

Next, let's generate the keys we will require later.
Since the type of the ciphertext ring depends on the type of the chosen parameters, all further functions are associated functions of `ChosenBGVParamType`.
While it would be preferable for the BFV implementation not to be tied to any specific parameter object, not doing this would cause problems, see the doc of [`crate::bfv::BFVParams`].
```rust
#![feature(allocator_api)]
# use he_ring::bgv::*;
# use he_ring::DefaultNegacyclicNTT;
# use he_ring::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
# use std::alloc::Global;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# use feanor_math::seq::VectorView;
# type ChosenBGVParamType = Pow2BGV;
# let params = ChosenBGVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 13,
#     log2_q_min: 210,
#     log2_q_max: 220,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let C_initial: CiphertextRing<ChosenBGVParamType> = params.create_initial_ciphertext_ring();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBGVParamType> = params.create_plaintext_ring(plaintext_modulus);
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(plaintext_modulus, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
let mut rng = StdRng::from_seed([1; 32]);
let sk = ChosenBGVParamType::gen_sk(&C_initial, &mut rng, None);
let rk_digits = RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len());
let rk_params = KeySwitchKeyParams {
    digits: &rk_digits,
    special_modulus_factor_count: 0
};
let rk = ChosenBGVParamType::gen_rk(&P, &C_initial, &mut rng, &sk, rk_params);
```
To generate the keys (as well as for encryption), we require a source of randomness.
HE-Ring is internally completely deterministic, hence it takes this source as parameter - in form of a [`rand::CryptoRng`].
Furthermore, there are two parameters that influence performance and noise growth of key-switching:
 - the number of "digits" used for the gadget decomposition. A high number will cause low noise growth, but larger key-switching keys and slower key-switching.
 - the number of RNS factors that constitute the "special modulus". This should be at most the size of the largest involved digit. In the simplest case, this is zero (no "hybrid key switching" is used), which means that the "special ciphertext ring" is equal to the normal ciphertext ring. However, this will negatively affect noise growth of key-switching after the first key-switch.

## Encryption and Decryption

Next, let's encrypt a message.
The plaintext space of BGV is the ring `R_t = Z[X]/(Phi_n(X), t)`, which we already have created previously.
To encrypt, we now need to encode whatever data we have as an element of this ring (e.g. via [`feanor_math::rings::extension::FreeAlgebra::from_canonical_basis()`] ), and can then encrypt it as follows:
```rust
#![feature(allocator_api)]
# use he_ring::bgv::*;
# use he_ring::DefaultNegacyclicNTT;
# use he_ring::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
# use std::alloc::Global;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# use feanor_math::homomorphism::Homomorphism;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::assert_el_eq;
# use feanor_math::seq::VectorView;
# type ChosenBGVParamType = Pow2BGV;
# let params = ChosenBGVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 13,
#     log2_q_min: 210,
#     log2_q_max: 220,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let C_initial: CiphertextRing<ChosenBGVParamType> = params.create_initial_ciphertext_ring();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBGVParamType> = params.create_plaintext_ring(plaintext_modulus);
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(plaintext_modulus, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = ChosenBGVParamType::gen_sk(&C_initial, &mut rng, None);
# let rk_digits = RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len());
# let rk_params = KeySwitchKeyParams {
#     digits: &rk_digits,
#     special_modulus_factor_count: 0
# };
# let rk = ChosenBGVParamType::gen_rk(&P, &C_initial, &mut rng, &sk, rk_params);
let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
    P.base_ring().int_hom().map(i)
));
let enc_x = ChosenBGVParamType::enc_sym(&P, &C_initial, &mut rng, &x, &sk);
let dec_x = ChosenBGVParamType::dec(&P, &C_initial, ChosenBGVParamType::clone_ct(&P, &C_initial, &enc_x), &sk);
assert_el_eq!(&P, &x, &dec_x);
```
For more info on how to create and operate on ring elements, see `feanor-math`.

## Homomorphic operations

BGV supports three types of homomorphic operations on ciphertexts:
 - Addition
 - Multiplication, requires a relinearization key
 - Galois automorphisms, requires a corresponding Galois key

Since we already have a relinearization key, we can perform a homomorphic multiplication.
```rust
#![feature(allocator_api)]
# use he_ring::bgv::*;
# use he_ring::DefaultNegacyclicNTT;
# use he_ring::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
# use std::alloc::Global;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# use feanor_math::homomorphism::Homomorphism;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::assert_el_eq;
# use feanor_math::seq::VectorView;
# type ChosenBGVParamType = Pow2BGV;
# let params = ChosenBGVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 13,
#     log2_q_min: 210,
#     log2_q_max: 220,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let C_initial: CiphertextRing<ChosenBGVParamType> = params.create_initial_ciphertext_ring();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBGVParamType> = params.create_plaintext_ring(plaintext_modulus);
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(plaintext_modulus, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = ChosenBGVParamType::gen_sk(&C_initial, &mut rng, None);
# let rk_digits = RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len());
# let rk_params = KeySwitchKeyParams {
#     digits: &rk_digits,
#     special_modulus_factor_count: 0
# };
# let rk = ChosenBGVParamType::gen_rk(&P, &C_initial, &mut rng, &sk, rk_params);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = ChosenBGVParamType::enc_sym(&P, &C_initial, &mut rng, &x, &sk);
let enc_x_sqr = ChosenBGVParamType::hom_mul(&P, &C_initial, &C_initial, ChosenBGVParamType::clone_ct(&P, &C_initial, &enc_x), enc_x, &rk);
let dec_x_sqr = ChosenBGVParamType::dec(&P, &C_initial, enc_x_sqr, &sk);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 2), &dec_x_sqr);
```
Note that the two ciphertext ring parameters to [`he_ring::bgv::BGVCiphertextParams::hom_mul()`] are the ciphertext ring over the current and special RNS base, respectively. Since we did not use any special modulus, they can be the same.

## Modulus-switching

Let's assume we want to compute a fourth power, i.e. square `enc_x_sqr` again.
The naive way would be to compute
```rust
#![feature(allocator_api)]
# use he_ring::bgv::*;
# use he_ring::DefaultNegacyclicNTT;
# use he_ring::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
# use std::alloc::Global;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# use feanor_math::homomorphism::Homomorphism;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::assert_el_eq;
# use feanor_math::seq::VectorView;
# type ChosenBGVParamType = Pow2BGV;
# let params = ChosenBGVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 13,
#     log2_q_min: 210,
#     log2_q_max: 220,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let C_initial: CiphertextRing<ChosenBGVParamType> = params.create_initial_ciphertext_ring();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBGVParamType> = params.create_plaintext_ring(plaintext_modulus);
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(plaintext_modulus, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = ChosenBGVParamType::gen_sk(&C_initial, &mut rng, None);
# let rk_digits = RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len());
# let rk_params = KeySwitchKeyParams {
#     digits: &rk_digits,
#     special_modulus_factor_count: 0
# };
# let rk = ChosenBGVParamType::gen_rk(&P, &C_initial, &mut rng, &sk, rk_params);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = ChosenBGVParamType::enc_sym(&P, &C_initial, &mut rng, &x, &sk);
let enc_x_sqr = ChosenBGVParamType::hom_mul(&P, &C_initial, &C_initial, ChosenBGVParamType::clone_ct(&P, &C_initial, &enc_x), enc_x, &rk);
assert_eq!(96, ChosenBGVParamType::noise_budget(&P, &C_initial, &enc_x_sqr, &sk));

let enc_x_pow4 = ChosenBGVParamType::hom_mul(&P, &C_initial, &C_initial, ChosenBGVParamType::clone_ct(&P, &C_initial, &enc_x_sqr), enc_x_sqr, &rk);
assert_eq!(0, ChosenBGVParamType::noise_budget(&P, &C_initial, &enc_x_pow4, &sk)); // this is 0, i.e. noise overflow
```
By querying the noise budget (note that determining the noise budget requires the secret key), we see that 41 bits are left after the first multiplication, and it is 0 after the second multiplication.
This means that the noise became too large, and the decryption would just return some random ring element, unrelated to the actual result.

However, we can decrease the noise growth that happens during the second multiplication by performing a modulus-switch to a new ciphertext modulus `q'`.
Note that finding the right size of `q'` is, in general, not so easy, since it requires an estimate of the current size of the noise in `enc_x_sqr`. 
In particular, this depends on the size of the ring we work in, and also on the number of digits chosen for relinearization.

Once we decided on the number of factors to drop, we can use the convenience function [`crate::gadget_product::digits::recommended_rns_factors_to_drop()`] to choose the exact factors to drop in such a way as to preserve the quality of the relinearization key.
Alternatively, these can also determined manually: [`crate::bgv::BGVCiphertextParams::mod_switch_down()`] takes a list of indices, which refer to the indices of the factors of `q` that will be dropped.
```rust
#![feature(allocator_api)]
# use he_ring::bgv::*;
# use he_ring::DefaultNegacyclicNTT;
# use he_ring::ciphertext_ring::BGFVCiphertextRing;
# use he_ring::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
# use std::alloc::Global;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# use feanor_math::homomorphism::Homomorphism;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::seq::VectorView;
# use feanor_math::assert_el_eq;
# type ChosenBGVParamType = Pow2BGV;
# let params = ChosenBGVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 13,
#     log2_q_min: 210,
#     log2_q_max: 220,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let C_initial: CiphertextRing<ChosenBGVParamType> = params.create_initial_ciphertext_ring();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBGVParamType> = params.create_plaintext_ring(plaintext_modulus);
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(plaintext_modulus, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = ChosenBGVParamType::gen_sk(&C_initial, &mut rng, None);
# let rk_digits = RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len());
# let rk_params = KeySwitchKeyParams {
#     digits: &rk_digits,
#     special_modulus_factor_count: 0
# };
# let rk = ChosenBGVParamType::gen_rk(&P, &C_initial, &mut rng, &sk, rk_params);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = ChosenBGVParamType::enc_sym(&P, &C_initial, &mut rng, &x, &sk);
let enc_x_sqr = ChosenBGVParamType::hom_mul(&P, &C_initial, &C_initial, ChosenBGVParamType::clone_ct(&P, &C_initial, &enc_x), enc_x, &rk);

let num_digits_to_drop = 2;
let to_drop = recommended_rns_factors_to_drop(rk.k0.gadget_vector_digits(), num_digits_to_drop);
let C_new = ChosenBGVParamType::mod_switch_down_C(&C_initial, &to_drop);

let enc_x_modswitch = ChosenBGVParamType::mod_switch_down(&P, &C_new, &C_initial, &to_drop, enc_x_sqr);
let sk_modswitch = ChosenBGVParamType::mod_switch_down_sk(&C_new, &C_initial, &to_drop, &sk);
let rk_modswitch = ChosenBGVParamType::mod_switch_down_rk(&C_new, &C_initial, &to_drop, &rk);

let enc_x_pow4 = ChosenBGVParamType::hom_mul(&P, &C_new, &C_new, ChosenBGVParamType::clone_ct(&P, &C_initial, &enc_x_modswitch), enc_x_modswitch, &rk_modswitch);
assert_eq!(40, ChosenBGVParamType::noise_budget(&P, &C_new, &enc_x_pow4, &sk_modswitch));
let dec_x_pow4 = ChosenBGVParamType::dec(&P, &C_new, enc_x_pow4, &sk_modswitch);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 4), &dec_x_pow4);
```

## Automatic modulus switching

Since deciding when (and how) to modulus-switch, and the manual management of ciphertext moduli, is quite a difficult task, it is extremely helpful for many applications if this is done automatically (like e.g. in HElib).
This is also planned for HE-Ring, and a WIP implementation is available as [`crate::bgv::modswitch::BGVModswitchStrategy`] and [`crate::bgv::modswitch::DefaultModswitchStrategy`].
The main difficulty here is that a good strategy for modulus-switching requires good estimates on the noise of ciphertexts, and the only current noise estimator [`crate::bgv::noise_estimator::NaiveBGVNoiseEstimator`] does not provide very high quality estimates.
Nevertheless, I have already used this system with some success.
For example, we could implement the above evaluation instead as follows:
```rust
#![feature(allocator_api)]
# use he_ring::bgv::*;
# use he_ring::bgv::modswitch::*;
# use he_ring::bgv::noise_estimator::NaiveBGVNoiseEstimator;
# use he_ring::DefaultNegacyclicNTT;
# use he_ring::circuit::*;
# use he_ring::ciphertext_ring::BGFVCiphertextRing;
# use he_ring::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
# use std::alloc::Global;
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# use feanor_math::homomorphism::Homomorphism;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::seq::VectorView;
# use feanor_math::assert_el_eq;
# type ChosenBGVParamType = Pow2BGV;
# let params = ChosenBGVParamType {
#     ciphertext_allocator: Global,
#     log2_N: 13,
#     log2_q_min: 210,
#     log2_q_max: 220,
#     negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
# };
# let C_initial: CiphertextRing<ChosenBGVParamType> = params.create_initial_ciphertext_ring();
# let plaintext_modulus = 17;
# let P: PlaintextRing<ChosenBGVParamType> = params.create_plaintext_ring(plaintext_modulus);
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(plaintext_modulus, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = ChosenBGVParamType::gen_sk(&C_initial, &mut rng, None);
# let rk_digits = RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len());
# let rk_params = KeySwitchKeyParams {
#     digits: &rk_digits,
#     special_modulus_factor_count: 0
# };
# let rk = ChosenBGVParamType::gen_rk(&P, &C_initial, &mut rng, &sk, rk_params);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
let enc_x = ChosenBGVParamType::enc_sym(&P, &C_initial, &mut rng, &x, &sk);

let square_circuit = PlaintextCircuit::mul(StaticRing::<i64>::RING).compose(PlaintextCircuit::select(1, &[0, 0], StaticRing::<i64>::RING), StaticRing::<i64>::RING);
let pow4_circuit = square_circuit.clone(StaticRing::<i64>::RING).compose(square_circuit, StaticRing::<i64>::RING);

let modswitch_strategy = DefaultModswitchStrategy::<_, _, /* debug output = */ false>::new(NaiveBGVNoiseEstimator);

let enc_x_pow4 = modswitch_strategy.evaluate_circuit(
    &pow4_circuit,
    StaticRing::<i64>::RING,
    &P,
    &C_initial,
    &[ModulusAwareCiphertext {
        info: modswitch_strategy.info_for_fresh_encryption(&P, &C_initial, None),
        dropped_rns_factor_indices: RNSFactorIndexList::empty(),
        data: enc_x
    }],
    Some(&rk),
    &[],
    &mut 0,
    None
).into_iter().next().unwrap();
let C_new = ChosenBGVParamType::mod_switch_down_C(&C_initial, &enc_x_pow4.dropped_rns_factor_indices);
let sk_new = ChosenBGVParamType::mod_switch_down_sk(&C_new, &C_initial, &enc_x_pow4.dropped_rns_factor_indices, &sk);
assert_eq!(40, ChosenBGVParamType::noise_budget(&P, &C_new, &enc_x_pow4.data, &sk_new));
let dec_x_pow4 = ChosenBGVParamType::dec(&P, &C_new, enc_x_pow4.data, &sk_new);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 4), &dec_x_pow4);
```