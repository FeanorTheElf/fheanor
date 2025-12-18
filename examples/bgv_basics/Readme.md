# Homomorphic operations using the BGV scheme

BGV was proposed in "Leveled fully homomorphic encryption without bootstrapping" by Z. Brakerski, C. Gentry, and V. Vaikuntanathan (<https://dl.acm.org/doi/10.1145/2090236.2090262>), and is the foundation of the family of "second generation" HE schemes.
In this example, we will show how to use the provided implementation of BGV, without going deep into the mathematical details of the scheme.
In comparison to BFV (for a short introduction, see [`crate::examples::bfv_basics`]), BGV allows for a somewhat more efficient implementation, but the necessity for the user to manually manage the modulus chain introduces significant additional complexity.
We note that some libraries (like HElib) automatically manage the modulus chain, but the plain BGV scheme implemented in this crate doesn't.
This crate does, however, have a separate implementation of BGV noise and modulus management, which currently is WIP.

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
In this crate, this task is currently left to the user, which means that using BGV introduces more complexity than BFV.

## Setting up BGV

In many libraries, there is a central context object that stores all parameters and data associated to the currently used HE scheme.
In this crate, we intentionally avoid this approach, and instead have the use manage these parts themselves.
More concretely, an instantiation of BGV consists of the following:
 - One Ciphertext ring for each modulus `q` in the ciphertext modulus chain `q > q' > q'' > ...`
 - One (or multiple) plaintext rings
 - Keys, possibly including a secret key, a relinearization key and Galois keys

While there is no central object storing all of this, we provide a simple way of creating these objects from a set of parameters.
There are multiple structs that represent a set of parameters for BGV each, since each of them will lead to a different type for the involved rings.
For example, to setup BGV in a power-of-two cyclotomic number ring `Z[X]/(X^N + 1)`, we could proceed as follows:
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use std::marker::PhantomData;
let log2_N = 13;
let params = Pow2BGV::new(2 << log2_N);
```
Here, we set the RLWE dimension to `2^log2_N = 2^13 = 8192`.

Using this, we can now create the plaintext ring and initial ciphertext ring via
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use rand::{SeedableRng, rngs::StdRng};
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# let log2_N = 13;
# let params = Pow2BGV::new(2 << log2_N);
let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);
let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
```
We choose the size of the RLWE modulus `q` to be between `210` and `220` bits - this choice (together with `N = 8192`) gives 128 bits of security, according to "Security Guidelines for Implementing Homomorphic Encryption" <https://ia.cr/2024/463>.
We will later derive the other moduli in the modulus chain `q', q'', ...` from `q` by "dropping" factors of `q`.
This works, since `q` is chosen as a product of many approximately 57 bit long primes.
These primes are also known as the RNS base of `q`.

Note also that the ciphertext and plaintext moduli are not part of the "BGV instantiation" - the rationale behind this is that it is quite reasonable to consider BGV encryptions w.r.t. different plain-or ciphertext moduli in a single use case.
Moreover, we check that `t` is coprime to `q`, otherwise there is no security (this is also checked at encryption time by the library).
However, since `q` is sampled using large primes of up to 57 bits, this is unlikely to be a problem.

Next, let's generate the keys we will require later.
Since the type of the ciphertext ring depends on the type of the chosen parameters, all further functions are associated functions of `Pow2BGV`.
While it would be preferable for the BGV implementation not to be tied to any specific parameter object, not doing this would cause problems, see the doc of [`BFVInstantiation`].
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
# use std::marker::PhantomData;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::RingExtensionStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::RingStore;
# use feanor_math::algorithms::eea::signed_gcd;
# use feanor_math::seq::VectorView;
# let log2_N = 13;
# let params = Pow2BGV::new(2 << log2_N);
# let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);
# let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
let mut rng = StdRng::from_seed([1; 32]);
let sk = Pow2BGV::gen_sk(&C_initial, &mut rng, SecretKeyDistribution::UniformTernary);
let rk = Pow2BGV::gen_rk(&P, &C_initial, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len()), 3.2);
```
To generate the keys (as well as for encryption), we require a source of randomness.
This crate is internally completely deterministic, hence it takes this source as parameter - in form of a [`rand::CryptoRng`].

Furthermore, for the so-called "relinearization key" `rk`, which is required for multiplications, we have to choose a decomposition of all RNS factors into "digits". 
A large number of small digits will cause low noise growth, but larger key-switching keys and slower key-switching.
The function [`RNSGadgetVectorDigitIndices::select_digits()`] will equally distribute all RNS factors across the given number of digits which is usually a reasonable choice.
Here, we choose 3 digits, which might be too low for complex scenarios, but is sufficient for this example

## Encryption and Decryption

Next, let's encrypt a message.
The plaintext space of BGV is the ring `R_t = Z[X]/(Phi_m(X), t)`, which we already have created previously.
To encrypt, we now need to encode whatever data we have as an element of this ring (e.g. via [`FreeAlgebra::from_canonical_basis()`] ), and can then encrypt it as follows:
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
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
# let log2_N = 13;
# let params = Pow2BGV::new(2 << log2_N);
# let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);
# let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = Pow2BGV::gen_sk(&C_initial, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BGV::gen_rk(&P, &C_initial, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len()), 3.2);
let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
    P.base_ring().int_hom().map(i)
));
let enc_x = Pow2BGV::enc_sym(&P, &C_initial, &mut rng, &x, &sk, 3.2);
let dec_x = Pow2BGV::dec(&P, &C_initial, Pow2BGV::clone_ct(&P, &C_initial, &enc_x), &sk);
assert_el_eq!(&P, &x, &dec_x);
```
For more info on how to create and operate on ring elements, see `feanor-math`.

**Note:** As opposed to other HE libraries, initial ciphertexts are created w.r.t. the modulus of the ring passed to [`BGVInstantiation::enc_sym()`].
In particular, no "special modulus" (as in other FHE libraries) is used at this point.
Instead, this crate implements a slightly less efficient variant of hybrid bootstrapping, where the special modulus is only chosen when performing a key-switch, hence gives much more flexibility.

## Homomorphic operations

BGV supports three types of homomorphic operations on ciphertexts:
 - Addition
 - Multiplication, requires a relinearization key
 - Galois automorphisms, requires a corresponding Galois key

Since we already have a relinearization key, we can perform a homomorphic multiplication.
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
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
# let log2_N = 13;
# let params = Pow2BGV::new(2 << log2_N);
# let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);
# let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = Pow2BGV::gen_sk(&C_initial, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BGV::gen_rk(&P, &C_initial, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len()), 3.2);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = Pow2BGV::enc_sym(&P, &C_initial, &mut rng, &x, &sk, 3.2);
let enc_x_sqr = Pow2BGV::hom_mul(&P, &C_initial, &C_initial, Pow2BGV::clone_ct(&P, &C_initial, &enc_x), enc_x, &rk);
let dec_x_sqr = Pow2BGV::dec(&P, &C_initial, enc_x_sqr, &sk);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 2), &dec_x_sqr);
```
Here we used the function [`BGVInstantiation::hom_mul()`] to multiply two encryped plaintexts.
Internally, the homomorphic multiplication will perform an operation called "relinearization" (hence the relinearization key).
Relinearization also makes sense if the relinearization key is defined modulo a larger modulus than the ciphertext, in which case two ciphertext rings, with a smaller and a larger modulus, can be passed to `hom_mul()`.
The next parameter should then be the list of indices of RNS factors only occuring in the larger modulus, which is in this context called the "special modulus".
Here, we don't have any special modulus, thus we pass `C_initial` twice, and an empty list.

## Modulus-switching

Let's assume we want to compute a fourth power, i.e. square `enc_x_sqr` again.
The naïve way would be to compute
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
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
# let log2_N = 13;
# let params = Pow2BGV::new(2 << log2_N);
# let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);
# let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = Pow2BGV::gen_sk(&C_initial, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BGV::gen_rk(&P, &C_initial, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len()), 3.2);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = Pow2BGV::enc_sym(&P, &C_initial, &mut rng, &x, &sk, 3.2);
let enc_x_sqr = Pow2BGV::hom_mul(&P, &C_initial, &C_initial, Pow2BGV::clone_ct(&P, &C_initial, &enc_x), enc_x, &rk);
assert_eq!(96, Pow2BGV::noise_budget(&P, &C_initial, &enc_x_sqr, &sk));

let enc_x_pow4 = Pow2BGV::hom_mul(&P, &C_initial, &C_initial, Pow2BGV::clone_ct(&P, &C_initial, &enc_x_sqr), enc_x_sqr, &rk);
assert_eq!(0, Pow2BGV::noise_budget(&P, &C_initial, &enc_x_pow4, &sk)); // this is 0, i.e. noise overflow
```
By querying the noise budget (note that determining the noise budget requires the secret key), we see that 96 bits are left after the first multiplication, and it is 0 after the second multiplication.
This means that the noise became too large, and the decryption would just return some random ring element, unrelated to the actual result.

However, we can decrease the noise growth that happens during the second multiplication by performing a modulus-switch to a new ciphertext modulus `q'`.
Note that finding the right size of `q'` is, in general, not so easy, since it requires an estimate of the current size of the noise in `enc_x_sqr`. 
In particular, this depends on the size of the ring we work in, and also on the number of digits chosen for relinearization.

Once we decided on the number of factors to drop, we can use the function [`crate::bgv::modswitch::drop_rns_factors_balanced()`] to choose the exact factors to drop in such a way as to preserve the quality of the relinearization key.
Alternatively, these can also determined manually: [`BGVInstantiation::mod_switch_ct()`] takes a list of indices, which refer to the indices of the factors of `q` that will be dropped.
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::ciphertext_ring::BGFVCiphertextRing;
# use anonymizedhelibrary::gadget_product::digits::*;
# use anonymizedhelibrary::bgv::modswitch::drop_rns_factors_balanced;
# use rand::{SeedableRng, rngs::StdRng};
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
# let log2_N = 13;
# let params = Pow2BGV::new(2 << log2_N);
# let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);
# let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = Pow2BGV::gen_sk(&C_initial, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BGV::gen_rk(&P, &C_initial, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len()), 3.2);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = Pow2BGV::enc_sym(&P, &C_initial, &mut rng, &x, &sk, 3.2);
let enc_x_sqr = Pow2BGV::hom_mul(&P, &C_initial, &C_initial, Pow2BGV::clone_ct(&P, &C_initial, &enc_x), enc_x, &rk);

let num_digits_to_drop = 2;
let to_drop = drop_rns_factors_balanced(rk.gadget_vector_digits(), num_digits_to_drop);
let C_new = Pow2BGV::mod_switch_down_C(&C_initial, &to_drop);

let enc_x_modswitch = Pow2BGV::mod_switch_ct(&P, &C_new, &C_initial, enc_x_sqr);
let sk_modswitch = Pow2BGV::mod_switch_sk(&C_new, &C_initial, &sk);
let rk_modswitch = Pow2BGV::mod_switch_down_rk(&C_new, &C_initial, &rk);

let enc_x_pow4 = Pow2BGV::hom_mul(&P, &C_new, &C_new, Pow2BGV::clone_ct(&P, &C_new, &enc_x_modswitch), enc_x_modswitch, &rk_modswitch);
assert_eq!(40, Pow2BGV::noise_budget(&P, &C_new, &enc_x_pow4, &sk_modswitch));
let dec_x_pow4 = Pow2BGV::dec(&P, &C_new, enc_x_pow4, &sk_modswitch);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 4), &dec_x_pow4);
```
Indeed, there is no noise overflow anymore!

We can even reduce the noise growth slightly more by using hybrid key switching as follows.
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::ciphertext_ring::BGFVCiphertextRing;
# use anonymizedhelibrary::gadget_product::digits::*;
# use anonymizedhelibrary::bgv::modswitch::drop_rns_factors_balanced;
# use rand::{SeedableRng, rngs::StdRng};
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
# let log2_N = 13;
# let params = Pow2BGV::new(2 << log2_N);
# let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);
# let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = Pow2BGV::gen_sk(&C_initial, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BGV::gen_rk(&P, &C_initial, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len()), 3.2);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
# let enc_x = Pow2BGV::enc_sym(&P, &C_initial, &mut rng, &x, &sk, 3.2);
let enc_x_sqr = Pow2BGV::hom_mul(&P, &C_initial, &C_initial, Pow2BGV::clone_ct(&P, &C_initial, &enc_x), enc_x, &rk);

let num_digits_to_drop = 2;
let to_drop = drop_rns_factors_balanced(rk.gadget_vector_digits(), num_digits_to_drop);
let C_new = Pow2BGV::mod_switch_down_C(&C_initial, &to_drop);

let enc_x_modswitch = Pow2BGV::mod_switch_ct(&P, &C_new, &C_initial, enc_x_sqr);
let sk_modswitch = Pow2BGV::mod_switch_sk(&C_new, &C_initial, &sk);
// don't modswitch the rk!

// pass both the ring `C_new` where the ciphertext lives, and the ring `C_initial` where the `rk` lives
let enc_x_pow4 = Pow2BGV::hom_mul(&P, &C_new, &C_initial, Pow2BGV::clone_ct(&P, &C_new, &enc_x_modswitch), enc_x_modswitch, &rk);
assert_eq!(78, Pow2BGV::noise_budget(&P, &C_new, &enc_x_pow4, &sk_modswitch));
let dec_x_pow4 = Pow2BGV::dec(&P, &C_new, enc_x_pow4, &sk_modswitch);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 4), &dec_x_pow4);
```
Note that hybrid key switching work on larger rings, and may take more time.
The exact trade-off between noise growth, relinearization key size and runtime is unfortunately somewhat complicated.

## Automatic modulus switching

Since deciding when (and how) to modulus-switch, and the manual management of ciphertext moduli, is quite a difficult task, it is extremely helpful for many applications if this is done automatically (like e.g. in HElib).
This is also planned for this crate, and a WIP implementation is available as [`BGVModswitchStrategy`] and [`DefaultModswitchStrategy`].
The main difficulty here is that a good strategy for modulus-switching requires good estimates on the noise of ciphertexts, and the only current noise estimator [`NaiveBGVNoiseEstimator`] does not provide very high quality estimates.
Nevertheless, I have already used this system with some success.
For example, we could implement the above evaluation instead as follows:
```rust
# use anonymizedhelibrary::bgv::*;
# use anonymizedhelibrary::bgv::modswitch::*;
# use anonymizedhelibrary::bgv::noise_estimator::NaiveBGVNoiseEstimator;
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::circuit::*;
# use anonymizedhelibrary::ciphertext_ring::BGFVCiphertextRing;
# use anonymizedhelibrary::ciphertext_ring::indices::RNSFactorIndexList;
# use anonymizedhelibrary::gadget_product::digits::*;
# use rand::{SeedableRng, rngs::StdRng};
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
# let log2_N = 13;
# let params = Pow2BGV::new(2 << log2_N);
# let C_initial: CiphertextRing<Pow2BGV> = params.create_ciphertext_ring(210..220);
# let P: PlaintextRing<Pow2BGV> = params.create_plaintext_ring(int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING));
# assert!(BigIntRing::RING.is_one(&signed_gcd(BigIntRing::RING.clone_el(C_initial.base_ring().modulus()), int_cast(17, BigIntRing::RING, StaticRing::<i64>::RING), BigIntRing::RING)));
# let mut rng = StdRng::from_seed([1; 32]);
# let sk = Pow2BGV::gen_sk(&C_initial, &mut rng, SecretKeyDistribution::UniformTernary);
# let rk = Pow2BGV::gen_rk(&P, &C_initial, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C_initial.base_ring().len()), 3.2);
# let x = P.from_canonical_basis((0..(1 << 13)).map(|i| 
#     P.base_ring().int_hom().map(i)
# ));
let enc_x = Pow2BGV::enc_sym(&P, &C_initial, &mut rng, &x, &sk, 3.2);

let square_circuit = PlaintextCircuit::mul(StaticRing::<i64>::RING).compose(PlaintextCircuit::select(1, &[0, 0], StaticRing::<i64>::RING), StaticRing::<i64>::RING);
let pow4_circuit = square_circuit.clone(StaticRing::<i64>::RING).compose(square_circuit, StaticRing::<i64>::RING);

let modswitch_strategy = DefaultModswitchStrategy::<_, _, /* debug output = */ false>::new(NaiveBGVNoiseEstimator);

let enc_x_pow4 = modswitch_strategy.evaluate_circuit(
    &pow4_circuit,
    StaticRing::<i64>::RING,
    &P,
    &C_initial,
    &[ModulusAwareCiphertext {
        info: modswitch_strategy.info_for_fresh_encryption(&P, &C_initial, SecretKeyDistribution::UniformTernary),
        dropped_rns_factor_indices: RNSFactorIndexList::empty(),
        data: enc_x,
        sk: SecretKeyDistribution::UniformTernary
    }],
    Some(&rk),
    &[],
    &mut 0,
    None
).into_iter().next().unwrap();
let C_new = Pow2BGV::mod_switch_down_C(&C_initial, &enc_x_pow4.dropped_rns_factor_indices);
let sk_new = Pow2BGV::mod_switch_sk(&C_new, &C_initial, &sk);
assert_eq!(78, Pow2BGV::noise_budget(&P, &C_new, &enc_x_pow4.data, &sk_new));
let dec_x_pow4 = Pow2BGV::dec(&P, &C_new, enc_x_pow4.data, &sk_new);
assert_el_eq!(&P, P.pow(P.clone_el(&x), 4), &dec_x_pow4);
```

[`BGVModswitchStrategy`]: crate::bgv::modswitch::BGVModswitchStrategy
[`DefaultModswitchStrategy`]: crate::bgv::modswitch::DefaultModswitchStrategy
[`BFVInstantiation`]: crate::bfv::BFVInstantiation
[`RNSGadgetVectorDigitIndices`]: crate::gadget_product::digits::RNSGadgetVectorDigitIndices
[`RNSGadgetVectorDigitIndices::select_digits()`]: crate::gadget_product::digits::RNSGadgetVectorDigitIndices::select_digits()
[`FreeAlgebra`]: feanor_math::rings::extension::FreeAlgebra
[`FreeAlgebra::from_canonical_basis()`]: feanor_math::rings::extension::FreeAlgebra::from_canonical_basis()
[`BGVInstantiation`]: crate::bgv::BGVInstantiation
[`BGVInstantiation::mod_switch_ct()`]: crate::bgv::BGVInstantiation::mod_switch_ct()
[`BGVInstantiation::hom_mul()`]: crate::bgv::BGVInstantiation::hom_mul()
[`BGVInstantiation::enc_sym()`]: crate::bgv::BGVInstantiation::enc_sym()
[`NaiveBGVNoiseEstimator`]: crate::bgv::noise_estimator::NaiveBGVNoiseEstimator