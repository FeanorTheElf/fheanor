# Implementing BFV using Fheanor, version 1

Fheanor is designed to facilitate the implementation of new, or variants of known HE schemes. To demonstrate which features come in useful in this case, this example walks you through a simple implementation of the BFV scheme.
In this first example, we will not optimize for performance, we defer this to the follow-up [`crate::examples::bfv_impl_v2`].
If you are just interested in how to use BFV, have a look at [`crate::examples::bfv_basics`].

## Description of BFV

Together with BGV, BFV is one of the most popular second generation FHE schemes.
It was proposed in "Somewhat practical fully homomorphic encryption" by Fan and Vercauteren (<https://ia.cr/2012/144>). We give a very short introduction here, but for any details, please refer to this paper. 

The BFV scheme has the following parameters:
 - the cyclotomic ring `R = Z[X]/(Phi_m(X))`
 - the ciphertext modulus `q`
 - the plaintext modulus `t`

With these parameters, the scheme can be described as follows:
 - `KeyGen()`: sample and return a small `s` in the ring `R_q = Z[X]/(Phi_m(X), q)`
 - `SymEnc(x, sk)`: sample a uniform `a in R_q` and a small noise `e in R_q`, and return `(a * sk + e + Δ * x, -a)`, where `Δ = round(q/t)`
 - `Dec((c0, c1), sk)`: return `round(t (c0 + c1 * sk) / q)`
 - `HomAdd((c0, c1), (c0', c1'))`: return `(c0 + c0', c1 + c1')`
 - `HomMul((c0, c1), (c0', c1'), rk)`: return the 3-component intermediate ciphertext `(round(t c0 c0' / q), round(t (c0 c1' + c1 c0') / q), round(t c1 c1' / q))`, where the multiplication of `ci` and `cj'` does not wrap around `q`, i.e. is performed using their shortest lift;
    To convert this 3-component ciphertext into a standard 2-component ciphertext, use `Relin((c0, c1, c2), rk)`
 - `Relin((c0, c1, c2), rk)`: Represent `c2` w.r.t. a gadget vector `g`, as `c2 = sum_i g[i] c[i]` with smaller ring elements `c[i]`; then return `(c0 + sum_i c[i] rk[i, 0], c1 + sum_i c[i] rk[i, 1])`
 - `RelinKeyGen(sk)`: Take a gadget vector `g` as before, and return `rk[i, 0] = (a[i] * sk + e[i] + g[i] * sk^2)` and `rk[i, 1] = -a[i]` for uniformly random `a[i] in R_q` and small noises `e[i] in R_q`

## Choosing the rings

Before we come to implementing the first operations, let's discuss how we represent the involved rings.
In particular, we will have to perform arithmetic operations in `R_t` and in `R_q`.

Fortunately, there are already various ring implementations available, in both `feanor-math` and `fheanor`.
For `R_t`, we have the following options:
 - Use [`feanor_math::rings::extension::extension_impl::FreeAlgebraImpl`], this is a general implementation of ring extensions of the form `BaseRing[X]/(f(X))`. By choosing `BaseRing` to be `Z/(t)` and `f(X) = Phi_m(X)`, we get the desired ring.
 - Use [`crate::number_ring::quotient::NumberRingQuotient`], which is an implementation of `R/(t)` for any integer `t` and ring `R` that is represented abstractly using [`crate::number_ring::HENumberRing`].
 - Implement our own ring!

Perhaps unsurprisingly, `NumberRingQuotient` is actually perfectly suited for this purpose (after all, this is what it was designed to do).

For `R_q`, we again have some options:
 - The same options as before - indeed, none of those makes assumptions on `t` that would cause a problem when we replace it by `q`
 - However, we have additional options: Since we can choose `q` freely, we can use an RNS representation, implementations of which are provided by [`crate::ciphertext_ring::double_rns_ring::DoubleRNSRing`] and [`crate::ciphertext_ring::single_rns_ring::SingleRNSRing`].

For practical purposes, it turns out that we should absolutely use an RNS-based implementation, since those are much faster than general ones.
However, for our first "unoptimized" implementation of BFV, we will in fact use again `NumberRingQuotient`.
For an example on how to use an RNS basis representation, see the example [`crate::examples::bfv_impl_v2`].

Based on this, we can create type aliases for our ring types.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
type NumberRing = Pow2CyclotomicNumberRing;
type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
```
Note that in all code examples, we skip the `use` statements for compactness.

Note that the only difference between `PlaintextRing` and `CiphertextRing` is the choice of the base ring, i.e. `zn_64::Zn` and `zn_big::Zn<BigIntRing>` respectively.
Both are implementations (from `feanor-math`) of `Z/(m)` for some integer modulus `m`, but `zn_64::Zn` only supports `m`s that are of length less than 57 bits.
57 bits are sufficient for all common choices of the BFV plaintext modulus, but certainly not enough for the ciphertext space.

Once we have these types, creating the actual objects is quite simple.
There is only a small quirk - caused by how `feanor-math` always wraps rings in a [`feanor_math::ring::RingStore`] - which means that the `new()` function belongs to `<CiphertextRing as RingStore>::Type` and not to `CiphertextRing`.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
    return <CiphertextRing as RingStore>::Type::new(
        Pow2CyclotomicNumberRing::new(ring_degree * 2), 
        zn_big::Zn::new(BigIntRing::RING, q)
    );
}

fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
    return <PlaintextRing as RingStore>::Type::new(
        Pow2CyclotomicNumberRing::new(ring_degree * 2), 
        zn_64::Zn::new(t)
    ); 
}
```

## Key Generation, Encryption and Decryption

Let's continue and implement key generation, encryption and decryption.
This is actually quite simple, since the ring objects directly provide arithmetic operations.

Among the non-arithmetic operations, the most important functions are [`feanor_math::rings::extension::FreeAlgebra::from_canonical_basis()`] and [`feanor_math::rings::extension::FreeAlgebra::wrt_canonical_basis()`], which convert between a ring element `sum_i a[i] X^i` and the list of its coefficients `a` (w.r.t. the basis given by `1, X, X^2, ..., X^(n - 1)`).

Using this, we can generate an element of `R_q` with ternary coefficients very easily.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
# fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
#     return <CiphertextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_big::Zn::new(BigIntRing::RING, q)
#     );
# }
# fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
# }
fn key_gen(ciphertext_ring: &CiphertextRing) -> El<CiphertextRing> {
    let mut rng = thread_rng();
    let sk = ciphertext_ring.from_canonical_basis(
        (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
            (rng.next_u32() as i32 % 3) - 1
        ))
    );
    return sk;
}
```
Note here that the function `int_hom()` gives us the homomorphism `Z -> Z/(q)` which reduces integers modulo `q`.

Next, we turn our attention to encryption.
It's not very difficult as well, but note that we require a way to convert the plaintext from `R_t` to `R_q`.
Using `from/wrt_canonical_basis()`, we get the coefficients of the plaintext, but they still need to be mapped from `Z/(t)` to `Z/(q)`.
For this, we use `can_hom()` to get the "canonical homomorphism" `Z -> Z/(q)` and `smallest_lift()`, which gives the smallest integer representative of some element of `Z/(t)`.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
# fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
#     return <CiphertextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_big::Zn::new(BigIntRing::RING, q)
#     );
# }
# fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
# }
# fn key_gen(ciphertext_ring: &CiphertextRing) -> El<CiphertextRing> {
#     let mut rng = thread_rng();
#     let sk = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.next_u32() as i32 % 3) - 1
#         ))
#     );
#     return sk;
# }
fn rlwe_sample(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
    let mut rng = thread_rng();
    let a = ciphertext_ring.random_element(|| rng.next_u64());
    let e = ciphertext_ring.from_canonical_basis(
        (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
            (rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32
        ))
    );
    return (ciphertext_ring.add(e, ciphertext_ring.mul_ref(&a, sk)), ciphertext_ring.negate(a));
}

fn enc_sym(
    plaintext_ring: &PlaintextRing, 
    ciphertext_ring: &CiphertextRing, 
    x: &El<PlaintextRing>, 
    sk: &El<CiphertextRing>
) -> (El<CiphertextRing>, El<CiphertextRing>) {
    let (b, a) = rlwe_sample(ciphertext_ring, sk);

    let q = ciphertext_ring.base_ring().modulus();
    let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
    let Δ = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap().map(BigIntRing::RING.rounded_div(BigIntRing::RING.clone_el(q), &t));

    let x_mod_q = ciphertext_ring.from_canonical_basis(
        plaintext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().int_hom().map(
            plaintext_ring.base_ring().smallest_lift(c) as i32
        ))
    );
    return (ciphertext_ring.add(ciphertext_ring.inclusion().mul_map(x_mod_q, Δ), b), a);
}
```
Finally, let's do decryption.
It does not require any new techniques.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
# fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
#     return <CiphertextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_big::Zn::new(BigIntRing::RING, q)
#     );
# }
# fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
# }
# fn key_gen(ciphertext_ring: &CiphertextRing) -> El<CiphertextRing> {
#     let mut rng = thread_rng();
#     let sk = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.next_u32() as i32 % 3) - 1
#         ))
#     );
#     return sk;
# }
# fn rlwe_sample(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let mut rng = thread_rng();
#     let a = ciphertext_ring.random_element(|| rng.next_u64());
#     let e = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32
#         ))
#     );
#     return (ciphertext_ring.add(e, ciphertext_ring.mul_ref(&a, sk)), ciphertext_ring.negate(a));
# }
# fn enc_sym(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, x: &El<PlaintextRing>, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let (b, a) = rlwe_sample(ciphertext_ring, sk);
#     let q = ciphertext_ring.base_ring().modulus();
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let Δ = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap().map(BigIntRing::RING.rounded_div(BigIntRing::RING.clone_el(q), &t));
#     let x_mod_q = ciphertext_ring.from_canonical_basis(
#         plaintext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().int_hom().map(
#             plaintext_ring.base_ring().smallest_lift(c) as i32
#         ))
#     );
#     return (ciphertext_ring.add(ciphertext_ring.inclusion().mul_map(x_mod_q, Δ), b), a);
# }
fn dec(
    plaintext_ring: &PlaintextRing, 
    ciphertext_ring: &CiphertextRing, 
    ct: &(El<CiphertextRing>, El<CiphertextRing>), 
    sk: &El<CiphertextRing>
) -> El<PlaintextRing> {
    let decryption_with_noise = ciphertext_ring.add_ref_fst(&ct.0, ciphertext_ring.mul_ref(&ct.1, sk));

    let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
    let modulo_t = plaintext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    // next, we have to compute the scaling-by-`t/q`, which includes a rounding at the end
    return plaintext_ring.from_canonical_basis(
        ciphertext_ring.wrt_canonical_basis(&decryption_with_noise).iter().map(|c| modulo_t.map(BigIntRing::RING.rounded_div(
            BigIntRing::RING.mul_ref_fst(&t, ciphertext_ring.base_ring().smallest_lift(c)),
            ciphertext_ring.base_ring().modulus()
        )))
    );
}
```
We can then test this code, but note that these parameters are not secure in practice.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# use feanor_math::assert_el_eq;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
# fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
#     return <CiphertextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_big::Zn::new(BigIntRing::RING, q)
#     );
# }
# fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
# }
# fn key_gen(ciphertext_ring: &CiphertextRing) -> El<CiphertextRing> {
#     let mut rng = thread_rng();
#     let sk = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.next_u32() as i32 % 3) - 1
#         ))
#     );
#     return sk;
# }
# fn rlwe_sample(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let mut rng = thread_rng();
#     let a = ciphertext_ring.random_element(|| rng.next_u64());
#     let e = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32
#         ))
#     );
#     return (ciphertext_ring.add(e, ciphertext_ring.mul_ref(&a, sk)), ciphertext_ring.negate(a));
# }
# fn enc_sym(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, x: &El<PlaintextRing>, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let (b, a) = rlwe_sample(ciphertext_ring, sk);
#     let q = ciphertext_ring.base_ring().modulus();
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let Δ = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap().map(BigIntRing::RING.rounded_div(BigIntRing::RING.clone_el(q), &t));
#     let x_mod_q = ciphertext_ring.from_canonical_basis(
#         plaintext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().int_hom().map(
#             plaintext_ring.base_ring().smallest_lift(c) as i32
#         ))
#     );
#     return (ciphertext_ring.add(ciphertext_ring.inclusion().mul_map(x_mod_q, Δ), b), a);
# }
# fn dec(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, ct: &(El<CiphertextRing>, El<CiphertextRing>), sk: &El<CiphertextRing>) -> El<PlaintextRing> {
#     let decryption_with_noise = ciphertext_ring.add_ref_fst(&ct.0, ciphertext_ring.mul_ref(&ct.1, sk));
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let modulo_t = plaintext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     return plaintext_ring.from_canonical_basis(
#         ciphertext_ring.wrt_canonical_basis(&decryption_with_noise).iter().map(|c| modulo_t.map(BigIntRing::RING.rounded_div(
#             BigIntRing::RING.mul_ref_fst(&t, ciphertext_ring.base_ring().smallest_lift(c)),
#             ciphertext_ring.base_ring().modulus()
#         )))
#     );
# }
let C = create_ciphertext_ring(1 << 8, BigIntRing::RING.power_of_two(100));
let P = create_plaintext_ring(1 << 8, 5);
let sk = key_gen(&C);
let message = P.int_hom().map(2);
let ciphertext = enc_sym(&P, &C, &message, &sk);
let result = dec(&P, &C, &ciphertext, &sk);
assert_el_eq!(&P, message, result);
```

## Homomorphic Addition and Multiplication

First of all, implementing addition of ciphertexts is absolutely trivial.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# use feanor_math::assert_el_eq;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
fn hom_add(
    ciphertext_ring: &CiphertextRing, 
    lhs: &(El<CiphertextRing>, El<CiphertextRing>), 
    rhs: &(El<CiphertextRing>, El<CiphertextRing>)
) -> (El<CiphertextRing>, El<CiphertextRing>) {
    return (ciphertext_ring.add_ref(&lhs.0, &rhs.0), ciphertext_ring.add_ref(&lhs.1, &rhs.1));
}
```
Multiplication is more interesting.
The first question is, how do we actually compute the products `c0 * c0'` without wrapping around `q`?
After all, multiplication in the ciphertext ring will wrap around `q`.

The most natural option is of course to perform arithmetic in the ring `R = Z[X]/(Phi_m)`.
This is not supported by `NumberRingQuotient` (which only represents `R/(q)` for some integer `q`), but is supported by `FreeAlgebraImpl`.
In particular, we could create a `FreeAlgebraImpl` using `BigIntRing::RING` as base ring and the `m`-th cyclotomic polynomial as modulus.

If we want to try this, note that we have to pass the cyclotomic polynomial `Phi_m` to `FreeAlgebraImpl::new()`.
In the power-of-two case that we are currently working in, this is just `X^(m/2) + 1`.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::cyclotomic::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# use feanor_math::assert_el_eq;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
fn hom_mul_three_component(
    plaintext_ring: &PlaintextRing, 
    ciphertext_ring: &CiphertextRing, 
    lhs: &(El<CiphertextRing>, El<CiphertextRing>), 
    rhs: &(El<CiphertextRing>, El<CiphertextRing>)
) -> (El<CiphertextRing>, El<CiphertextRing>, El<CiphertextRing>) {
    let multiplication_ring = FreeAlgebraImpl::new(
        BigIntRing::RING,
        ciphertext_ring.rank(),
        // we give the modulus as the coefficients of `X^n mod Phi_m = -1`
        [BigIntRing::RING.neg_one()]
    );

    let lift_ciphertext_ring_el = |x: &El<CiphertextRing>| multiplication_ring.from_canonical_basis(
        ciphertext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().smallest_lift(c))
    );
    let lhs_lifted = (lift_ciphertext_ring_el(&lhs.0), lift_ciphertext_ring_el(&lhs.1));
    let rhs_lifted = (lift_ciphertext_ring_el(&rhs.0), lift_ciphertext_ring_el(&rhs.1));

    let product = (
        multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.0),
        multiplication_ring.add(multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.1), multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.0)),
        multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.1)
    );

    let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
    let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    let scale_down_multiplication_ring_el = |x: &El<FreeAlgebraImpl<_, [_; 1]>>| ciphertext_ring.from_canonical_basis(
        multiplication_ring.wrt_canonical_basis(x).iter().map(|c| modulo_q.map(BigIntRing::RING.rounded_div(
            BigIntRing::RING.mul_ref_snd(c, &t),
            ciphertext_ring.base_ring().modulus()
        )))
    );

    return (
        scale_down_multiplication_ring_el(&product.0),
        scale_down_multiplication_ring_el(&product.1),
        scale_down_multiplication_ring_el(&product.2)
    );
}
```
Before we implement relinearization, we want to test the multiplication that we have so far.
We do this by using the formula `round( t (c0 + c1 * sk + c2 * sk^2) / q )` to decrypt the three-component ciphertext.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::cyclotomic::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# use feanor_math::assert_el_eq;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
# fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
#     return <CiphertextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_big::Zn::new(BigIntRing::RING, q)
#     );
# }
# fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
# }
# fn key_gen(ciphertext_ring: &CiphertextRing) -> El<CiphertextRing> {
#     let mut rng = thread_rng();
#     let sk = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.next_u32() as i32 % 3) - 1
#         ))
#     );
#     return sk;
# }
# fn rlwe_sample(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let mut rng = thread_rng();
#     let a = ciphertext_ring.random_element(|| rng.next_u64());
#     let e = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32
#         ))
#     );
#     return (ciphertext_ring.add(e, ciphertext_ring.mul_ref(&a, sk)), ciphertext_ring.negate(a));
# }
# fn enc_sym(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, x: &El<PlaintextRing>, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let (b, a) = rlwe_sample(ciphertext_ring, sk);
#     let q = ciphertext_ring.base_ring().modulus();
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let Δ = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap().map(BigIntRing::RING.rounded_div(BigIntRing::RING.clone_el(q), &t));
#     let x_mod_q = ciphertext_ring.from_canonical_basis(
#         plaintext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().int_hom().map(
#             plaintext_ring.base_ring().smallest_lift(c) as i32
#         ))
#     );
#     return (ciphertext_ring.add(ciphertext_ring.inclusion().mul_map(x_mod_q, Δ), b), a);
# }
# fn hom_mul_three_component(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, lhs: &(El<CiphertextRing>, El<CiphertextRing>), rhs: &(El<CiphertextRing>, El<CiphertextRing>)) -> (El<CiphertextRing>, El<CiphertextRing>, El<CiphertextRing>) {
#     let multiplication_ring = FreeAlgebraImpl::new(
#         BigIntRing::RING,
#         ciphertext_ring.rank(),
#         // we give the modulus as the coefficients of `X^n mod Phi_m = -1`
#         [BigIntRing::RING.neg_one()]
#     );
#     let lift_ciphertext_ring_el = |x: &El<CiphertextRing>| multiplication_ring.from_canonical_basis(
#         ciphertext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().smallest_lift(c))
#     );
#     let lhs_lifted = (lift_ciphertext_ring_el(&lhs.0), lift_ciphertext_ring_el(&lhs.1));
#     let rhs_lifted = (lift_ciphertext_ring_el(&rhs.0), lift_ciphertext_ring_el(&rhs.1));
#     let product = (
#         multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.0),
#         multiplication_ring.add(multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.1), multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.0)),
#         multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.1)
#     );
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     let scale_down_multiplication_ring_el = |x: &El<FreeAlgebraImpl<_, [_; 1]>>| ciphertext_ring.from_canonical_basis(
#         multiplication_ring.wrt_canonical_basis(x).iter().map(|c| modulo_q.map(BigIntRing::RING.rounded_div(
#             BigIntRing::RING.mul_ref_snd(c, &t),
#             ciphertext_ring.base_ring().modulus()
#         )))
#     );
#     return (
#         scale_down_multiplication_ring_el(&product.0),
#         scale_down_multiplication_ring_el(&product.1),
#         scale_down_multiplication_ring_el(&product.2)
#     );
# }
# fn dec(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, ct: &(El<CiphertextRing>, El<CiphertextRing>), sk: &El<CiphertextRing>) -> El<PlaintextRing> {
#     let decryption_with_noise = ciphertext_ring.add_ref_fst(&ct.0, ciphertext_ring.mul_ref(&ct.1, sk));
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let modulo_t = plaintext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     return plaintext_ring.from_canonical_basis(
#         ciphertext_ring.wrt_canonical_basis(&decryption_with_noise).iter().map(|c| modulo_t.map(BigIntRing::RING.rounded_div(
#             BigIntRing::RING.mul_ref_fst(&t, ciphertext_ring.base_ring().smallest_lift(c)),
#             ciphertext_ring.base_ring().modulus()
#         )))
#     );
# }
let C = create_ciphertext_ring(1 << 8, BigIntRing::RING.power_of_two(100));
let P = create_plaintext_ring(1 << 8, 5);
let sk = key_gen(&C);
let message = P.int_hom().map(2);
let ciphertext = enc_sym(&P, &C, &message, &sk);
let ciphertext_sqr = hom_mul_three_component(&P, &C, &ciphertext, &ciphertext);
let ciphertext_sqr_relin = (C.add(ciphertext_sqr.0, C.mul(ciphertext_sqr.2, C.pow(C.clone_el(&sk), 2))), ciphertext_sqr.1);
let result = dec(&P, &C, &ciphertext_sqr_relin, &sk);
assert_el_eq!(&P, P.pow(message, 2), result);
```

## Relinearization

Finally, let's do relinearization.
Before we come to the implementation, we need to choose a suitable gadget vector.
In particular, `g` should allow us to decompose the `c2` that `hom_mul_three_component()` outputs into multiple small parts `c[i]`, via `c2 = sum_i g[i] c[i]`.
The easiest method is to use a basis-`B` decomposition, in other words we set `g[i] = B^i`.
This leads us to the following code.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::cyclotomic::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
# use feanor_math::pid::EuclideanRingStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# use feanor_math::assert_el_eq;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
fn gadget_vector(B: &El<BigIntRing>, digits: usize) -> Vec<El<BigIntRing>> {
    (0..digits).map(|i| BigIntRing::RING.pow(BigIntRing::RING.clone_el(B), i)).collect()
}

fn gadget_decompose(mut x: El<BigIntRing>, B: &El<BigIntRing>, digits: usize) -> Vec<El<BigIntRing>> {
    let mut result = Vec::with_capacity(digits);
    for _ in 0..digits {
        let (quotient, remainder) = BigIntRing::RING.euclidean_div_rem(x, B);
        x = quotient;
        result.push(remainder);
    }
    return result;
}
```
Putting it all together, we get the following.
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::cyclotomic::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
# use feanor_math::pid::EuclideanRingStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# use feanor_math::assert_el_eq;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
# fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
#     return <CiphertextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_big::Zn::new(BigIntRing::RING, q)
#     );
# }
# fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
# }
# fn key_gen(ciphertext_ring: &CiphertextRing) -> El<CiphertextRing> {
#     let mut rng = thread_rng();
#     let sk = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.next_u32() as i32 % 3) - 1
#         ))
#     );
#     return sk;
# }
# fn rlwe_sample(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let mut rng = thread_rng();
#     let a = ciphertext_ring.random_element(|| rng.next_u64());
#     let e = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32
#         ))
#     );
#     return (ciphertext_ring.add(e, ciphertext_ring.mul_ref(&a, sk)), ciphertext_ring.negate(a));
# }
# fn enc_sym(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, x: &El<PlaintextRing>, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let (b, a) = rlwe_sample(ciphertext_ring, sk);
#     let q = ciphertext_ring.base_ring().modulus();
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let Δ = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap().map(BigIntRing::RING.rounded_div(BigIntRing::RING.clone_el(q), &t));
#     let x_mod_q = ciphertext_ring.from_canonical_basis(
#         plaintext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().int_hom().map(
#             plaintext_ring.base_ring().smallest_lift(c) as i32
#         ))
#     );
#     return (ciphertext_ring.add(ciphertext_ring.inclusion().mul_map(x_mod_q, Δ), b), a);
# }
# fn hom_mul_three_component(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, lhs: &(El<CiphertextRing>, El<CiphertextRing>), rhs: &(El<CiphertextRing>, El<CiphertextRing>)) -> (El<CiphertextRing>, El<CiphertextRing>, El<CiphertextRing>) {
#     let multiplication_ring = FreeAlgebraImpl::new(
#         BigIntRing::RING,
#         ciphertext_ring.rank(),
#         // we give the modulus as the coefficients of `X^n mod Phi_m = -1`
#         [BigIntRing::RING.neg_one()]
#     );
#     let lift_ciphertext_ring_el = |x: &El<CiphertextRing>| multiplication_ring.from_canonical_basis(
#         ciphertext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().smallest_lift(c))
#     );
#     let lhs_lifted = (lift_ciphertext_ring_el(&lhs.0), lift_ciphertext_ring_el(&lhs.1));
#     let rhs_lifted = (lift_ciphertext_ring_el(&rhs.0), lift_ciphertext_ring_el(&rhs.1));
#     let product = (
#         multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.0),
#         multiplication_ring.add(multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.1), multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.0)),
#         multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.1)
#     );
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     let scale_down_multiplication_ring_el = |x: &El<FreeAlgebraImpl<_, [_; 1]>>| ciphertext_ring.from_canonical_basis(
#         multiplication_ring.wrt_canonical_basis(x).iter().map(|c| modulo_q.map(BigIntRing::RING.rounded_div(
#             BigIntRing::RING.mul_ref_snd(c, &t),
#             ciphertext_ring.base_ring().modulus()
#         )))
#     );
#     return (
#         scale_down_multiplication_ring_el(&product.0),
#         scale_down_multiplication_ring_el(&product.1),
#         scale_down_multiplication_ring_el(&product.2)
#     );
# }
# fn dec(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, ct: &(El<CiphertextRing>, El<CiphertextRing>), sk: &El<CiphertextRing>) -> El<PlaintextRing> {
#     let decryption_with_noise = ciphertext_ring.add_ref_fst(&ct.0, ciphertext_ring.mul_ref(&ct.1, sk));
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let modulo_t = plaintext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     return plaintext_ring.from_canonical_basis(
#         ciphertext_ring.wrt_canonical_basis(&decryption_with_noise).iter().map(|c| modulo_t.map(BigIntRing::RING.rounded_div(
#             BigIntRing::RING.mul_ref_fst(&t, ciphertext_ring.base_ring().smallest_lift(c)),
#             ciphertext_ring.base_ring().modulus()
#         )))
#     );
# }
# fn gadget_vector(B: &El<BigIntRing>, digits: usize) -> Vec<El<BigIntRing>> {
#     (0..digits).map(|i| BigIntRing::RING.pow(BigIntRing::RING.clone_el(B), i)).collect()
# }
# fn gadget_decompose(mut x: El<BigIntRing>, B: &El<BigIntRing>, digits: usize) -> Vec<El<BigIntRing>> {
#     let mut result = Vec::with_capacity(digits);
#     for _ in 0..digits {
#         let (quotient, remainder) = BigIntRing::RING.euclidean_div_rem(x, B);
#         x = quotient;
#         result.push(remainder);
#     }
#     return result;
# }
fn gen_relin_key(
    ciphertext_ring: &CiphertextRing, 
    sk: &El<CiphertextRing>, 
    B: &El<BigIntRing>, 
    digits: usize
) -> Vec<(El<CiphertextRing>, El<CiphertextRing>)> {
    let sk_sqr = ciphertext_ring.pow(ciphertext_ring.clone_el(sk), 2);
    let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    return gadget_vector(B, digits).iter().map(|factor| {
        let (b, a) = rlwe_sample(ciphertext_ring, sk);
        return (ciphertext_ring.add(b, ciphertext_ring.inclusion().mul_ref_map(&sk_sqr, &modulo_q.map_ref(factor))), a);
    }).collect();
}

fn relinearize(
    ciphertext_ring: &CiphertextRing, 
    three_component_ciphertext: &(El<CiphertextRing>, El<CiphertextRing>, El<CiphertextRing>), 
    relin_key: &[(El<CiphertextRing>, El<CiphertextRing>)], 
    B: &El<BigIntRing>, 
    digits: usize
) -> (El<CiphertextRing>, El<CiphertextRing>) {
    let mut c2_decomposition = (0..digits).map(|_| (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().zero()).collect::<Vec<_>>()).collect::<Vec<_>>();
    let c2_wrt_basis = ciphertext_ring.wrt_canonical_basis(&three_component_ciphertext.2);
    let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
    for i in 0..c2_wrt_basis.len() {
        let mut coeff_decomposition = gadget_decompose(ciphertext_ring.base_ring().smallest_lift(c2_wrt_basis.at(i)), B, digits).into_iter();
        for j in 0..digits {
            c2_decomposition[j][i] = modulo_q.map(coeff_decomposition.next().unwrap());
        }
    }
    let c2_decomposition = c2_decomposition.into_iter().map(|coefficients| ciphertext_ring.from_canonical_basis(coefficients)).collect::<Vec<_>>();

    return (
        ciphertext_ring.add_ref_fst(&three_component_ciphertext.0, ciphertext_ring.sum(c2_decomposition.iter().zip(relin_key.iter()).map(|(c, (rk0, _))| ciphertext_ring.mul_ref(c, rk0)))),
        ciphertext_ring.add_ref_fst(&three_component_ciphertext.1, ciphertext_ring.sum(c2_decomposition.iter().zip(relin_key.iter()).map(|(c, (_, rk1))| ciphertext_ring.mul_ref(c, rk1))))
    );
}
```
Finally, let's test that decrypting the result of a homomorphic multiplication with relinearization gives the correct result!
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::cyclotomic::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::number_ring::quotient::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
# use feanor_math::pid::EuclideanRingStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use feanor_math::primitive_int::*;
# use feanor_math::assert_el_eq;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = NumberRingQuotient<NumberRing, zn_big::Zn<BigIntRing>>;
# fn create_ciphertext_ring(ring_degree: usize, q: El<BigIntRing>) -> CiphertextRing {
#     return <CiphertextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_big::Zn::new(BigIntRing::RING, q)
#     );
# }
# fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
# }
# fn key_gen(ciphertext_ring: &CiphertextRing) -> El<CiphertextRing> {
#     let mut rng = thread_rng();
#     let sk = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.next_u32() as i32 % 3) - 1
#         ))
#     );
#     return sk;
# }
# fn rlwe_sample(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let mut rng = thread_rng();
#     let a = ciphertext_ring.random_element(|| rng.next_u64());
#     let e = ciphertext_ring.from_canonical_basis(
#         (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().int_hom().map(
#             (rng.sample::<f64, _>(StandardNormal) * 3.2).round() as i32
#         ))
#     );
#     return (ciphertext_ring.add(e, ciphertext_ring.mul_ref(&a, sk)), ciphertext_ring.negate(a));
# }
# fn enc_sym(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, x: &El<PlaintextRing>, sk: &El<CiphertextRing>) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let (b, a) = rlwe_sample(ciphertext_ring, sk);
#     let q = ciphertext_ring.base_ring().modulus();
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let Δ = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap().map(BigIntRing::RING.rounded_div(BigIntRing::RING.clone_el(q), &t));
#     let x_mod_q = ciphertext_ring.from_canonical_basis(
#         plaintext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().int_hom().map(
#             plaintext_ring.base_ring().smallest_lift(c) as i32
#         ))
#     );
#     return (ciphertext_ring.add(ciphertext_ring.inclusion().mul_map(x_mod_q, Δ), b), a);
# }
# fn hom_mul_three_component(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, lhs: &(El<CiphertextRing>, El<CiphertextRing>), rhs: &(El<CiphertextRing>, El<CiphertextRing>)) -> (El<CiphertextRing>, El<CiphertextRing>, El<CiphertextRing>) {
#     let multiplication_ring = FreeAlgebraImpl::new(
#         BigIntRing::RING,
#         ciphertext_ring.rank(),
#         // we give the modulus as the coefficients of `X^n mod Phi_m = -1`
#         [BigIntRing::RING.neg_one()]
#     );
#     let lift_ciphertext_ring_el = |x: &El<CiphertextRing>| multiplication_ring.from_canonical_basis(
#         ciphertext_ring.wrt_canonical_basis(x).iter().map(|c| ciphertext_ring.base_ring().smallest_lift(c))
#     );
#     let lhs_lifted = (lift_ciphertext_ring_el(&lhs.0), lift_ciphertext_ring_el(&lhs.1));
#     let rhs_lifted = (lift_ciphertext_ring_el(&rhs.0), lift_ciphertext_ring_el(&rhs.1));
#     let product = (
#         multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.0),
#         multiplication_ring.add(multiplication_ring.mul_ref(&lhs_lifted.0, &rhs_lifted.1), multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.0)),
#         multiplication_ring.mul_ref(&lhs_lifted.1, &rhs_lifted.1)
#     );
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     let scale_down_multiplication_ring_el = |x: &El<FreeAlgebraImpl<_, [_; 1]>>| ciphertext_ring.from_canonical_basis(
#         multiplication_ring.wrt_canonical_basis(x).iter().map(|c| modulo_q.map(BigIntRing::RING.rounded_div(
#             BigIntRing::RING.mul_ref_snd(c, &t),
#             ciphertext_ring.base_ring().modulus()
#         )))
#     );
#     return (
#         scale_down_multiplication_ring_el(&product.0),
#         scale_down_multiplication_ring_el(&product.1),
#         scale_down_multiplication_ring_el(&product.2)
#     );
# }
# fn dec(plaintext_ring: &PlaintextRing, ciphertext_ring: &CiphertextRing, ct: &(El<CiphertextRing>, El<CiphertextRing>), sk: &El<CiphertextRing>) -> El<PlaintextRing> {
#     let decryption_with_noise = ciphertext_ring.add_ref_fst(&ct.0, ciphertext_ring.mul_ref(&ct.1, sk));
#     let t = int_cast(*plaintext_ring.base_ring().modulus(), BigIntRing::RING, StaticRing::<i64>::RING);
#     let modulo_t = plaintext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     return plaintext_ring.from_canonical_basis(
#         ciphertext_ring.wrt_canonical_basis(&decryption_with_noise).iter().map(|c| modulo_t.map(BigIntRing::RING.rounded_div(
#             BigIntRing::RING.mul_ref_fst(&t, ciphertext_ring.base_ring().smallest_lift(c)),
#             ciphertext_ring.base_ring().modulus()
#         )))
#     );
# }
# fn gadget_vector(B: &El<BigIntRing>, digits: usize) -> Vec<El<BigIntRing>> {
#     (0..digits).map(|i| BigIntRing::RING.pow(BigIntRing::RING.clone_el(B), i)).collect()
# }
# fn gadget_decompose(mut x: El<BigIntRing>, B: &El<BigIntRing>, digits: usize) -> Vec<El<BigIntRing>> {
#     let mut result = Vec::with_capacity(digits);
#     for _ in 0..digits {
#         let (quotient, remainder) = BigIntRing::RING.euclidean_div_rem(x, B);
#         x = quotient;
#         result.push(remainder);
#     }
#     return result;
# }
# fn gen_relin_key(ciphertext_ring: &CiphertextRing, sk: &El<CiphertextRing>, B: &El<BigIntRing>, digits: usize) -> Vec<(El<CiphertextRing>, El<CiphertextRing>)> {
#     let sk_sqr = ciphertext_ring.pow(ciphertext_ring.clone_el(sk), 2);
#     let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     return gadget_vector(B, digits).iter().map(|factor| {
#         let (b, a) = rlwe_sample(ciphertext_ring, sk);
#         return (ciphertext_ring.add(b, ciphertext_ring.inclusion().mul_ref_map(&sk_sqr, &modulo_q.map_ref(factor))), a);
#     }).collect();
# }
# fn relinearize(ciphertext_ring: &CiphertextRing, three_component_ciphertext: &(El<CiphertextRing>, El<CiphertextRing>, El<CiphertextRing>), relin_key: &[(El<CiphertextRing>, El<CiphertextRing>)], B: &El<BigIntRing>, digits: usize) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     let mut c2_decomposition = (0..digits).map(|_| (0..ciphertext_ring.rank()).map(|_| ciphertext_ring.base_ring().zero()).collect::<Vec<_>>()).collect::<Vec<_>>();
#     let c2_wrt_basis = ciphertext_ring.wrt_canonical_basis(&three_component_ciphertext.2);
#     let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     for i in 0..c2_wrt_basis.len() {
#         let mut coeff_decomposition = gadget_decompose(ciphertext_ring.base_ring().smallest_lift(c2_wrt_basis.at(i)), B, digits).into_iter();
#         for j in 0..digits {
#             c2_decomposition[j][i] = modulo_q.map(coeff_decomposition.next().unwrap());
#         }
#     }
#     let c2_decomposition = c2_decomposition.into_iter().map(|coefficients| ciphertext_ring.from_canonical_basis(coefficients)).collect::<Vec<_>>();
#     return (
#         ciphertext_ring.add_ref_fst(&three_component_ciphertext.0, ciphertext_ring.sum(c2_decomposition.iter().zip(relin_key.iter()).map(|(c, (rk0, _))| ciphertext_ring.mul_ref(c, rk0)))),
#         ciphertext_ring.add_ref_fst(&three_component_ciphertext.1, ciphertext_ring.sum(c2_decomposition.iter().zip(relin_key.iter()).map(|(c, (_, rk1))| ciphertext_ring.mul_ref(c, rk1))))
#     );
# }
let C = create_ciphertext_ring(1 << 8, BigIntRing::RING.power_of_two(100));
let P = create_plaintext_ring(1 << 8, 5);
let B = BigIntRing::RING.power_of_two(20);
let digits = 5;
let sk = key_gen(&C);
let relin_key = gen_relin_key(&C, &sk, &B, digits);

let message = P.int_hom().map(2);
let ciphertext = enc_sym(&P, &C, &message, &sk);
let ciphertext_sqr = hom_mul_three_component(&P, &C, &ciphertext, &ciphertext);
let ciphertext_sqr_relin = relinearize(&C, &ciphertext_sqr, &relin_key, &B, digits);
let result = dec(&P, &C, &ciphertext_sqr_relin, &sk);
assert_el_eq!(&P, P.pow(message, 2), result);
```

## Putting it all together

Taking all these functions together gives the code in `main.rs`. 

# Performance

On my desktop PC, a slight modification of the above test with `N = 16384` and `q = 2^100` performs homomorphic multiplication and relinearization in about 7.7 seconds (of course, you need to compile it with `--release`).
This might be suitable for prototyping, but is far behind what one can achieve with a more careful implementation.
In particular, we lose a lot of time due to the following points:
 - Without further configuration, `FreeAlgebraImpl` (which we use during `hom_mul_three_component()`) uses Karatsuba's algorithm for multiplication.
   However, if we perform the multiplication during `hom_mul_three_component()` modulo a special, large enough modulus, it is possible to use NTT-based techniques, which are much faster.
 - Similarly, if we choose a special `q` (for security and correctness of BFV, only the approximate size matters), we can use this technique also for all other multiplications in `R_q`. 
 - If `q` is a product of primes, we can store elements modulo `q` by their reductions modulo `p` for each `p | q`.
   This is called Residue Number System (RNS), and allows us to avoid big integers, if we assume that every prime factor `p | q` fits within (say) a `u64`.
 - Finally, if we choose a gadget vector for relinearization that is compatible with the RNS system, we can also perform the gadget-decomposition and relinearization without big integers.

We discuss a more efficient implementation in [`crate::examples::bfv_impl_v2`].
