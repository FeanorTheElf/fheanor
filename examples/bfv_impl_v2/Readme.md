# Implementing BFV using Fheanor, version 2

In this example, we will again implement the BFV scheme, but this time aiming for good performance.
Perhaps unsurprisingly, the result will look quite similar to [`crate::bfv`] - the main difference is that [`crate::bfv`] is defined more generically, and allows more configuration and different parameters.

If you are unsure about the details of BFV, refer to the version 1 of our BFV implementation [`crate::examples::bfv_impl_v1`] first.
At the end of [`crate::examples::bfv_impl_v1`], we list some points that have to be considered when aiming for state-of-the-art performance - these will be the main points for this example.
Mostly, this boils down to two points: Use a Residue Number System, and a Number-Theoretic Transform-based multiplication.

## The computational and mathematical foundations

### The Residue Number System (RNS)

In BFV, only approximate size of the ciphertext modulus `q` matters - usually its bitlength.
Hence, we have a lot of freedom when actually choosing `q`.
It has become standard to choose `q = p1 ... pr` as the product of distinct primes `p1, ..., pr`, which each fit into a machine integer, e.g. `i64`.
In this case, the Chinese Remainder theorem gives an isomorphism
```text
  Z/(q)  ->  Z/(p1) x ... x Z/(pr),  x  ->  (x mod p1, ..., x mod pr)
```
In other words, instead of storing an element of `Z/(q)` as an integer `0 <= x < q`, we can store `x mod p1, ..., x mod pr`.
Each of those `x mod pi` now fit into a `i64`, which means we don't need slow arbitrary-precision integers.

In particular, since this map is an isomorphism, we can perform addition and multiplication component-wise modulo each `pi`.
In other words, we have
```text
  (x + y) mod pi = (x mod pi) + (x mod pi) mod pi
  (x * y) mod pi = (x mod pi) * (x mod pi) mod pi
```
for each `pi`.
Now each `pi` fits into a `i64`, so we actually only perform additions, multiplications and modular reductions on `i64`s, and completely avoid expensive multiplications of very large numbers.

When it comes to implementation, `feanor-math` already provides the ring [`feanor_math::rings::zn::zn_rns::Zn`] for `Z/qZ` when `q` can be represented in RNS basis. We will heavily use this from now on.

### The Number-Theoretic Transform

On a mathematical level, the Number-Theoretic Transform (NTT) is quite similar to what we did before - it just refers to the Chinese Remainder theorem, with prime numbers replaced by prime ideals in a cyclotomic number ring modulo a prime that splits completely.
In more down-to-the-earth terms, the NTT is the evaluation of a polynomial at all `n`-th roots of unity.
In other words, we say it is the map
```text
  NTT: Fp^n  ->  Fp^n,  (a[0], ..., a[n - 1])  ->  (sum_i a[i] ξ_n^i)
```
where `ξ` is a `n`-th root of unity in the finite field `Fp` - note that for `ξ` to exist, we require `p = 1 mod n`.

The NTT is important, because of two well-known facts:
 - The NTT can be computed very fast using a "Fast Fourier Transform" (FFT), in time `O(n log n)`; The same holds for the inverse map, which we call `InvNTT()`.
 - Addition and multiplication are component-wise for elements in NTT form. With NTT form, we refer to the values `NTT(x[0], ..., x[n - 1])` of an element `x = sum_i x[i] X^n` in the ring `R_p = Z[X]/(Phi_n(X), p)`.

In other words, if we store each element `x` in `R/(p)` using the values `(x'[0], ..., x'[n - 1]) = NTT(x[0], ..., x[n - 1])`, we can compute the multiplication of elements `x, y` by
```text
  z'[0] = x'[0] * y'[0],  ...,  z'[n - 1] = x'[n - 1] * y'[n - 1]
```
The individual multiplications here are very fast, since they are performed on values of `Fp`.

Note here a little mismatch: We can actually represent an element `x` in `R/(p)` by a sum `x[0] + x[1] X + ... + x[phi(n) - 1] X^(phi(n) - 1)` of only `phi(n)` summands. However, padding this to `n` when necessary does not pose a significant problem.

### The Double-RNS representation

So how do we combine these two techniques?

Very simply, for an element `x in R_q` we first compute `x mod pi` in `R/(pi)` for each `pi`, and then store `NTT(x mod pi)` for each `pi`.
These values are called the Double-RNS representation of `x`, because of the mathematical similarities between NTT and RNS, which means we view the NTT as "a second RNS".
This representation allows for very fast arithmetic, and is implemented by [`crate::ciphertext_ring::double_rns_ring::DoubleRNSRing`].

## Implementing Encryption and Decryption

Ok, so let's use [`crate::ciphertext_ring::double_rns_ring::DoubleRNSRing`] for the ciphertext ring.
We cannot use it for the plaintext ring, since to use the double-RNS representation, we need to have `p = 1 mod n` for each prime divisor `p | q` of `q`.
We also remark that due to technical details, we sometimes additionally require `p = 1 mod 2^k n` for some `k > log2(n) + 1`.

Anyway, we can now define our ring types
```rust
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::ciphertext_ring::double_rns_ring::*;
# use fheanor::number_ring::quotient::*;
type NumberRing = Pow2CyclotomicNumberRing;
type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
type CiphertextRing = DoubleRNSRing<NumberRing>;
```
Creating this ring is not completely trivial, since we need to find a suitable `q`.
```rust
# use feanor_math::algorithms::miller_rabin::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::StaticRing;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::ciphertext_ring::double_rns_ring::*;
# use fheanor::number_ring::quotient::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = DoubleRNSRing<NumberRing>;
fn create_ciphertext_ring(ring_degree: usize, mut number_of_rns_factors: usize) -> CiphertextRing {
    let n = ring_degree * 2;
    let mut rns_factors = Vec::new();
    // `current` should always be `= 1 mod n`
    let mut current = (1 << 57) - ((1 << 57) % n) + 1;
    while number_of_rns_factors > 0 {
        if is_prime(StaticRing::<i64>::RING, &(current as i64), 10) {
            rns_factors.push(current);
            number_of_rns_factors -= 1;
        }
        current -= n;
    }
    return <CiphertextRing as RingStore>::Type::new(
        Pow2CyclotomicNumberRing::new(n),
        zn_rns::Zn::new(rns_factors.iter().map(|p| zn_64::Zn::new(*p as u64)).collect(), BigIntRing::RING)
    );
}

fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
    // as before
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
}
```
Note that Fheanor provides the convenience function [`crate::number_ring::sample_primes()`] and [`crate::number_ring::extend_sampled_primes()`] to simplify this:
```rust
# use feanor_math::algorithms::miller_rabin::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::integer::*;
# use feanor_math::primitive_int::StaticRing;
# use feanor_math::ordered::OrderedRingStore;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::ciphertext_ring::double_rns_ring::*;
# use fheanor::number_ring::quotient::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = DoubleRNSRing<NumberRing>;
fn create_ciphertext_ring(ring_degree: usize, bitlength_of_q: usize) -> CiphertextRing {
    let number_ring = Pow2CyclotomicNumberRing::new(ring_degree * 2);
    let mut rns_factors = sample_primes(
        bitlength_of_q - 10, 
        bitlength_of_q, 
        57, 
        |bound| largest_prime_leq_congruent_to_one(int_cast(bound, StaticRing::<i64>::RING, BigIntRing::RING), number_ring. mod_p_required_root_of_unity() as i64).map(|p| int_cast(p, BigIntRing::RING, StaticRing::<i64>::RING))
    ).unwrap();
    return <CiphertextRing as RingStore>::Type::new(
        number_ring,
        zn_rns::Zn::new(rns_factors.into_iter().map(|p| zn_64::Zn::new(int_cast(p, StaticRing::<i64>::RING, BigIntRing::RING) as u64)). collect(), BigIntRing::RING)
    );
}

fn create_plaintext_ring(ring_degree: usize, t: u64) -> PlaintextRing {
    // as before
#     return <PlaintextRing as RingStore>::Type::new(
#         Pow2CyclotomicNumberRing::new(ring_degree * 2), 
#         zn_64::Zn::new(t)
#     ); 
}
```
Once we have this, key-generation, encryption and decryption can actually be implemented exactly as before.
It might be possible to optimize decryption somewhat (leveraging the RNS representation), but we skip that here.
Instead, we will use similar (but more impactful) techniques when implementing homomorphic multiplication.

```rust
# use feanor_math::algorithms::miller_rabin::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::homomorphism::*;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::integer::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::ordered::OrderedRingStore;
# use feanor_math::primitive_int::StaticRing;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::ciphertext_ring::double_rns_ring::*;
# use fheanor::number_ring::quotient::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = DoubleRNSRing<NumberRing>;
# fn create_ciphertext_ring(ring_degree: usize, bitlength_of_q: usize) -> CiphertextRing {
#     let number_ring = Pow2CyclotomicNumberRing::new(ring_degree * 2);
#     let mut rns_factors = sample_primes(
#         bitlength_of_q - 10, 
#         bitlength_of_q, 
#         56, 
#         |bound| largest_prime_leq_congruent_to_one(int_cast(bound, StaticRing::<i64>::RING, BigIntRing::RING), number_ring. mod_p_required_root_of_unity() as i64).map(|p| int_cast(p, BigIntRing::RING, StaticRing::<i64>::RING))
#     ).unwrap();
#     rns_factors.sort_unstable_by(|l, r| BigIntRing::RING.cmp(l, r));
#     return <CiphertextRing as RingStore>::Type::new(
#         number_ring,
#         zn_rns::Zn::new(rns_factors.into_iter().map(|p| zn_64::Zn::new(int_cast(p, StaticRing::<i64>::RING, BigIntRing::RING) as u64)). collect(), BigIntRing::RING)
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

fn hom_add(
    ciphertext_ring: &CiphertextRing, 
    lhs: &(El<CiphertextRing>, El<CiphertextRing>), 
    rhs: &(El<CiphertextRing>, El<CiphertextRing>)
) -> (El<CiphertextRing>, El<CiphertextRing>) {
    return (ciphertext_ring.add_ref(&lhs.0, &rhs.0), ciphertext_ring.add_ref(&lhs.1, &rhs.1));
}
```

## Homomorphic multiplication

As in [`crate::examples::bfv_impl_v1`], homomorphic multiplication is the most interesting operation.
The first question is, which ring do we use to evaluate `c0 * c0'` etc. without wrapping around `q`?
Previously, we worked without any modulus in `Z[X]/(Phi_n(X))`, which certainly works, but means we cannot use the double-RNS representation.
Instead, it makes sense to choose a larger modulus - say `qq'` - and perform the multiplication in `R_(qq')`.
If `qq'` is larger than the coefficients of `c0 * c0'` in `R`, this means we still get the correct result.
Since creating a double-RNS ring is somewhat expensive, we do this once and reuse the ring.
```rust
# use feanor_math::algorithms::miller_rabin::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::homomorphism::*;
# use feanor_math::seq::VectorView;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::integer::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::ordered::OrderedRingStore;
# use feanor_math::primitive_int::StaticRing;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use fheanor::number_ring::*;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::ciphertext_ring::double_rns_ring::*;
# use fheanor::number_ring::quotient::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = DoubleRNSRing<NumberRing>;
fn create_multiplication_ring(ciphertext_ring: &CiphertextRing) -> CiphertextRing {
    let number_ring = ciphertext_ring.get_ring().number_ring().clone();
    let rns_factors = extend_sampled_primes(
        &ciphertext_ring.base_ring().as_iter().map(|RNS_factor| int_cast(*RNS_factor.modulus(), BigIntRing::RING, StaticRing::<i64>::RING)).collect::<Vec<_>>(),
        BigIntRing::RING.abs_log2_ceil(ciphertext_ring.base_ring().modulus()).unwrap() * 2 + StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.rank() as i64)).unwrap() + 10, 
        BigIntRing::RING.abs_log2_ceil(ciphertext_ring.base_ring().modulus()).unwrap() * 2 + StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.rank() as i64)).unwrap() + 67, 
        57, 
        |bound| largest_prime_leq_congruent_to_one(int_cast(bound, StaticRing::<i64>::RING, BigIntRing::RING), number_ring.mod_p_required_root_of_unity() as i64).map(|p| int_cast(p, BigIntRing::RING, StaticRing::<i64>::RING))
    ).unwrap().into_iter().map(|p| 
        int_cast(p, StaticRing::<i64>::RING, BigIntRing::RING)
    ).collect::<Vec<_>>();
    return <CiphertextRing as RingStore>::Type::new(
        number_ring,
        zn_rns::Zn::new(rns_factors.into_iter().map(|p| zn_64::Zn::new(p as u64)).collect(), BigIntRing::RING)
    );
}
```
Next, we turn to the question on how to map the elements of `R_q` to `R_(qq')`.
While we could do it in the same way as before, i.e. take the shortest lift of each coefficient and map it into `Z/(qq')`, this would again mean using arbitrary-precision integers.

Instead we use a technique that was propsed by <https://ia.cr/2016/510>.
More concretely, they show how to implement the necessary operations as "RNS conversions", which directly operate on the RNS values, and don't involve big integers.
The details are not overly complicated, but would go beyond the scope of this introduction, so we just describe how to use the RNS conversion implementations that are implemented in Fheanor.
In particular, we are interested in [`crate::rnsconv::lift::AlmostExactBaseConversion`] and [`crate::rnsconv::bfv_rescale::AlmostExactRescalingConvert`], since they implement the two operations that we require for BFV multiplication.
The first one takes care of the conversion `Z/(q) -> Z/(qq')`, and the second one does the downscaling at the end, which scales elements of `Z/(qq')` by `t/q` and maps them back to `Z/(q)`.
All implemented RNS conversions take the input in the form of the following matrix:
```text
   /  x[1] mod p1   x[2] mod p1   ...   x[m] mod p1   \
  |   x[1] mod p2   x[2] mod p2   ...   x[m] mod p2    |
  |         ⋮              ⋮                   ⋮        |
   \  x[1] mod pr   x[2] mod pr   ...   x[m] mod pr   /
```
where `x[1], ..., x[m]` are an arbitrary number of elements of `Z/(q)`.
The output is returned in the same format.

If we now want to apply such an RNS conversion to an element of `R_q`, we need to first convert this element back from double-RNS basis, to "single-RNS" representation.
This requires a relatively costly NTT, but no way of avoiding this is known.
Note however that it actually is not required to get the actual coefficients `x[i]` in the representatation `x = x[0] + x[1] X + ... + x[phi(n) - 1] X^(phi(n) - 1)`, but the coefficients w.r.t. any basis that consists of "short" elements suffice.
The reason for this is that the noise growth during multiplication depends on the size of `c0, c1, c0', c1'` w.r.t. the *canonical norm* of the number ring `R`.
More details on the mathematical background can be found in the original BFV paper.

We can access the coefficients w.r.t. some "short-element" basis of an element of `R_q` using the functions [`crate::ciphertext_ring::double_rns_ring::DoubleRNSRingBase::undo_fft()`] and [`crate::ciphertext_ring::double_rns_ring::DoubleRNSRingBase::as_matrix_wrt_small_basis()`].
Fortunately for us, the returned data is exactly in the right format.
This leaves us to implement BFV multiplication as follows.
```rust
#![feature(allocator_api)]
# use std::alloc::Global;
# use feanor_math::algorithms::miller_rabin::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::homomorphism::*;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::integer::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::seq::VectorView;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::ordered::OrderedRingStore;
# use feanor_math::primitive_int::StaticRing;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use fheanor::number_ring::*;
# use fheanor::rnsconv::bfv_rescale::AlmostExactRescalingConvert;
# use fheanor::rnsconv::RNSOperation;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::ciphertext_ring::double_rns_ring::*;
# use fheanor::number_ring::quotient::*;
# use fheanor::rnsconv::lift::AlmostExactBaseConversion;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = DoubleRNSRing<NumberRing>;
# fn create_multiplication_ring(ciphertext_ring: &CiphertextRing) -> CiphertextRing {
#     let number_ring = ciphertext_ring.get_ring().number_ring().clone();
#     let rns_factors = extend_sampled_primes(
#         &ciphertext_ring.base_ring().as_iter().map(|RNS_factor| int_cast(*RNS_factor.modulus(), BigIntRing::RING, StaticRing::<i64>::RING)).collect::<Vec<_>>(),
#         BigIntRing::RING.abs_log2_ceil(ciphertext_ring.base_ring().modulus()).unwrap() * 2 + StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.rank() as i64)).unwrap() + 10, 
#         BigIntRing::RING.abs_log2_ceil(ciphertext_ring.base_ring().modulus()).unwrap() * 2 + StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.rank() as i64)).unwrap() + 67, 
#         57, 
#         |bound| largest_prime_leq_congruent_to_one(int_cast(bound, StaticRing::<i64>::RING, BigIntRing::RING), number_ring.mod_p_required_root_of_unity() as i64).map(|p| int_cast(p, BigIntRing::RING, StaticRing::<i64>::RING))
#     ).unwrap().into_iter().map(|p| 
#         int_cast(p, StaticRing::<i64>::RING, BigIntRing::RING)
#     ).collect::<Vec<_>>();
#     return <CiphertextRing as RingStore>::Type::new(
#         number_ring,
#         zn_rns::Zn::new(rns_factors.into_iter().map(|p| zn_64::Zn::new(p as u64)).collect(), BigIntRing::RING)
#     );
# }
fn hom_mul_three_component(
    plaintext_ring: &PlaintextRing, 
    ciphertext_ring: &CiphertextRing, 
    multiplication_ring: &CiphertextRing,
    lhs: &(SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>), 
    rhs: &(SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>)
) -> (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>) {
    let (c0, c1) = (&lhs.0, &lhs.1);
    let (c0_prime, c1_prime) = (&rhs.0, &rhs.1);
    
    let lift_to_multiplication_ring_rnsconv = AlmostExactBaseConversion::new_with(
        ciphertext_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(), 
        multiplication_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(),
        Global
    );
    debug_assert!(lift_to_multiplication_ring_rnsconv.input_rings().iter().zip(ciphertext_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
    debug_assert!(lift_to_multiplication_ring_rnsconv.output_rings().iter().zip(multiplication_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
    let lift_to_multiplication_ring = |x: &SmallBasisEl<_, _>| {
        let mut result = multiplication_ring.get_ring().zero_non_fft();
        lift_to_multiplication_ring_rnsconv.apply(ciphertext_ring.get_ring().as_matrix_wrt_small_basis(&x), multiplication_ring.get_ring().as_matrix_wrt_small_basis_mut(&mut result));
        return multiplication_ring.get_ring().do_fft(result);
    };

    let unscaled_result = (
        multiplication_ring.mul(lift_to_multiplication_ring(&c0), lift_to_multiplication_ring(&c0_prime)),
        multiplication_ring.add(
            multiplication_ring.mul(lift_to_multiplication_ring(&c0), lift_to_multiplication_ring(&c1_prime)),
            multiplication_ring.mul(lift_to_multiplication_ring(&c1), lift_to_multiplication_ring(&c0_prime))
        ),
        multiplication_ring.mul(lift_to_multiplication_ring(&c1), lift_to_multiplication_ring(&c1_prime))
    );

    let scale_down_rnsconv = AlmostExactRescalingConvert::new_with(
        multiplication_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(), 
        vec![ zn_64::Zn::new(*plaintext_ring.base_ring().modulus() as u64) ], 
        ciphertext_ring.base_ring().as_iter().map(|Zp| multiplication_ring.base_ring().as_iter().position(|Zp2| Zp2.modulus() == Zp.modulus()).unwrap()).collect::<Vec<_>>(),
        Global
    );
    debug_assert!(scale_down_rnsconv.input_rings().iter().zip(multiplication_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
    debug_assert!(scale_down_rnsconv.output_rings().iter().zip(ciphertext_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
    let scale_down = |x: El<CiphertextRing>| {
        let mut result = ciphertext_ring.get_ring().zero_non_fft();
        scale_down_rnsconv.apply(multiplication_ring.get_ring().as_matrix_wrt_small_basis(&multiplication_ring.get_ring().undo_fft(x)), ciphertext_ring.get_ring().as_matrix_wrt_small_basis_mut(&mut result));
        return result;
    };

    return (
        scale_down(unscaled_result.0),
        scale_down(unscaled_result.1),
        scale_down(unscaled_result.2)
    );
}
```
Note that we now take the inputs and return the outputs as `SmallBasisEl<Pow2CyclotomicNumberRing>`, instead of `El<CiphertextRing>`.
The difference is that `El<CiphertextRing>` will store elements in double-RNS representation, while [`crate::ciphertext_ring::double_rns_ring::SmallBasisEl`] uses the single-RNS small-basis representation.
Hence, by taking inputs as `SmallBasisEl`, we can avoid the costly NTT - assuming that the caller already has elements available in small-basis representation.

To conclude this example, we have to implement relinearization.
Note that previously, we did so by using a gadget product, which relies on the basis-`B` decomposition of elements.
We still use a gadget product, but this time, we use an RNS-compatible gadget vector.
This again allows us to avoid arbitrary-precision integers.
In fact, this means we can use the available implementation of gadget product in [`crate::gadget_product`], and thus this part will actually be much shorter than relinearization in [`crate::examples::bfv_impl_v1`].
Without going into the details, we just create two [`crate::gadget_product::GadgetProductRhsOperand`] instead of the `Vec<(El<CiphertextRing>, El<CiphertextRing>)>` as the relinearization key, and a single [`crate::gadget_product::GadgetProductLhsOperand`] for `c2` during relinearization.
We arrive at:
```rust
#![feature(allocator_api)]
# use std::alloc::Global;
# use feanor_math::algorithms::miller_rabin::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::homomorphism::*;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::integer::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::seq::VectorView;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::primitive_int::StaticRing;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use fheanor::number_ring::*;
# use fheanor::gadget_product::*;
# use fheanor::rnsconv::RNSOperation;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::ciphertext_ring::double_rns_ring::*;
# use fheanor::number_ring::quotient::*;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = DoubleRNSRing<NumberRing>;
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
type RelinKey = (GadgetProductRhsOperand<<CiphertextRing as RingStore>::Type>, GadgetProductRhsOperand<<CiphertextRing as RingStore>::Type>);

fn gen_relin_key(
    ciphertext_ring: &CiphertextRing, 
    sk: &El<CiphertextRing>, 
    digits: usize
) -> RelinKey {
    let sk_sqr = ciphertext_ring.pow(ciphertext_ring.clone_el(sk), 2);
    let mut result0 = GadgetProductRhsOperand::new(ciphertext_ring.get_ring(), digits);
    let mut result1 = GadgetProductRhsOperand::new(ciphertext_ring.get_ring(), digits);
    
    let gadget_vector_len = result0.gadget_vector(ciphertext_ring.get_ring()).len();
    for i in 0..gadget_vector_len {
        let (b, a) = rlwe_sample(ciphertext_ring, sk);
        let factor = result0.gadget_vector(ciphertext_ring.get_ring()).at(i);
        let (key0, key1) = (ciphertext_ring.add(b, ciphertext_ring.inclusion().mul_ref_map(&sk_sqr, &factor)), a);
        result0.set_rns_factor(ciphertext_ring.get_ring(), i, key0);
        result1.set_rns_factor(ciphertext_ring.get_ring(), i, key1);
    }
    return (result0, result1);
}

fn relinearize(
    ciphertext_ring: &CiphertextRing, 
    three_component_ciphertext: (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>), 
    relin_key: &RelinKey
) -> (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>) {
    let c2_decomposition = GadgetProductLhsOperand::from_double_rns_ring_with(ciphertext_ring.get_ring(), &three_component_ciphertext.2, relin_key.0.gadget_vector_digits());
    let mut result0 = three_component_ciphertext.0;
    ciphertext_ring.get_ring().add_assign_non_fft(&mut result0, &ciphertext_ring.get_ring().undo_fft(c2_decomposition.gadget_product(&relin_key.0, ciphertext_ring.get_ring())));
    let mut result1 = three_component_ciphertext.1;
    ciphertext_ring.get_ring().add_assign_non_fft(&mut result1, &ciphertext_ring.get_ring().undo_fft(c2_decomposition.gadget_product(&relin_key.1, ciphertext_ring.get_ring())));
    return (result0, result1);
}
```
Finally, let's test this implementation again!
```rust
#![feature(allocator_api)]
# use std::alloc::Global;
# use feanor_math::algorithms::miller_rabin::*;
# use feanor_math::ring::*;
# use feanor_math::rings::zn::*;
# use feanor_math::assert_el_eq;
# use feanor_math::homomorphism::*;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::integer::*;
# use feanor_math::seq::VectorFn;
# use feanor_math::seq::VectorView;
# use feanor_math::rings::finite::FiniteRingStore;
# use feanor_math::primitive_int::StaticRing;
# use feanor_math::ordered::OrderedRingStore;
# use rand::{Rng, RngCore, thread_rng};
# use rand_distr::StandardNormal;
# use fheanor::number_ring::*;
# use fheanor::rnsconv::bfv_rescale::AlmostExactRescalingConvert;
# use fheanor::gadget_product::*;
# use fheanor::rnsconv::RNSOperation;
# use fheanor::number_ring::pow2_cyclotomic::*;
# use fheanor::ciphertext_ring::double_rns_ring::*;
# use fheanor::number_ring::quotient::*;
# use fheanor::rnsconv::lift::AlmostExactBaseConversion;
# type NumberRing = Pow2CyclotomicNumberRing;
# type PlaintextRing = NumberRingQuotient<NumberRing, zn_64::Zn>;
# type CiphertextRing = DoubleRNSRing<NumberRing>;
# type RelinKey = (GadgetProductRhsOperand<<CiphertextRing as RingStore>::Type>, GadgetProductRhsOperand<<CiphertextRing as RingStore>::Type>);
# fn create_ciphertext_ring(ring_degree: usize, bitlength_of_q: usize) -> CiphertextRing {
#     let number_ring = Pow2CyclotomicNumberRing::new(ring_degree * 2);
#     let mut rns_factors = sample_primes(
#         bitlength_of_q - 10, 
#         bitlength_of_q, 
#         57, 
#         |bound| largest_prime_leq_congruent_to_one(int_cast(bound, StaticRing::<i64>::RING, BigIntRing::RING), number_ring. mod_p_required_root_of_unity() as i64).map(|p| int_cast(p, BigIntRing::RING, StaticRing::<i64>::RING))
#     ).unwrap();
#     return <CiphertextRing as RingStore>::Type::new(
#         number_ring,
#         zn_rns::Zn::new(rns_factors.into_iter().map(|p| zn_64::Zn::new(int_cast(p, StaticRing::<i64>::RING, BigIntRing::RING) as u64)). collect(), BigIntRing::RING)
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
# fn enc_sym(
#     plaintext_ring: &PlaintextRing, 
#     ciphertext_ring: &CiphertextRing, 
#     x: &El<PlaintextRing>, 
#     sk: &El<CiphertextRing>
# ) -> (El<CiphertextRing>, El<CiphertextRing>) {
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
# fn dec(
#     plaintext_ring: &PlaintextRing, 
#     ciphertext_ring: &CiphertextRing, 
#     ct: &(El<CiphertextRing>, El<CiphertextRing>), 
#     sk: &El<CiphertextRing>
# ) -> El<PlaintextRing> {
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
# fn hom_add(
#     ciphertext_ring: &CiphertextRing, 
#     lhs: &(El<CiphertextRing>, El<CiphertextRing>), 
#     rhs: &(El<CiphertextRing>, El<CiphertextRing>)
# ) -> (El<CiphertextRing>, El<CiphertextRing>) {
#     return (ciphertext_ring.add_ref(&lhs.0, &rhs.0), ciphertext_ring.add_ref(&lhs.1, &rhs.1));
# }
# fn create_multiplication_ring(ciphertext_ring: &CiphertextRing) -> CiphertextRing {
#     let number_ring = ciphertext_ring.get_ring().number_ring().clone();
#     let rns_factors = extend_sampled_primes(
#         &ciphertext_ring.base_ring().as_iter().map(|RNS_factor| int_cast(*RNS_factor.modulus(), BigIntRing::RING, StaticRing::<i64>::RING)).collect::<Vec<_>>(),
#         BigIntRing::RING.abs_log2_ceil(ciphertext_ring.base_ring().modulus()).unwrap() * 2 + StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.rank() as i64)).unwrap() + 10, 
#         BigIntRing::RING.abs_log2_ceil(ciphertext_ring.base_ring().modulus()).unwrap() * 2 + StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.rank() as i64)).unwrap() + 67, 
#         57, 
#         |bound| largest_prime_leq_congruent_to_one(int_cast(bound, StaticRing::<i64>::RING, BigIntRing::RING), number_ring.mod_p_required_root_of_unity() as i64).map(|p| int_cast(p, BigIntRing::RING, StaticRing::<i64>::RING))
#     ).unwrap().into_iter().map(|p| 
#         int_cast(p, StaticRing::<i64>::RING, BigIntRing::RING)
#     ).collect::<Vec<_>>();
#     return <CiphertextRing as RingStore>::Type::new(
#         number_ring,
#         zn_rns::Zn::new(rns_factors.into_iter().map(|p| zn_64::Zn::new(p as u64)).collect(), BigIntRing::RING)
#     );
# }
# fn hom_mul_three_component(
#     plaintext_ring: &PlaintextRing, 
#     ciphertext_ring: &CiphertextRing, 
#     multiplication_ring: &CiphertextRing,
#     lhs: &(SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>), 
#     rhs: &(SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>)
# ) -> (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>) {
#     let (c0, c1) = (&lhs.0, &lhs.1);
#     let (c0_prime, c1_prime) = (&rhs.0, &rhs.1);
#     let lift_to_multiplication_ring_rnsconv = AlmostExactBaseConversion::new_with(
#         ciphertext_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(), 
#         multiplication_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(),
#         Global
#     );
#     debug_assert!(lift_to_multiplication_ring_rnsconv.input_rings().iter().zip(ciphertext_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
#     debug_assert!(lift_to_multiplication_ring_rnsconv.output_rings().iter().zip(multiplication_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
#     let lift_to_multiplication_ring = |x: &SmallBasisEl<_, _>| {
#         let mut result = multiplication_ring.get_ring().zero_non_fft();
#         lift_to_multiplication_ring_rnsconv.apply(ciphertext_ring.get_ring().as_matrix_wrt_small_basis(&x), multiplication_ring.get_ring().as_matrix_wrt_small_basis_mut(&mut result));
#         return multiplication_ring.get_ring().do_fft(result);
#     };
#     let unscaled_result = (
#         multiplication_ring.mul(lift_to_multiplication_ring(&c0), lift_to_multiplication_ring(&c0_prime)),
#         multiplication_ring.add(
#             multiplication_ring.mul(lift_to_multiplication_ring(&c0), lift_to_multiplication_ring(&c1_prime)),
#             multiplication_ring.mul(lift_to_multiplication_ring(&c1), lift_to_multiplication_ring(&c0_prime))
#         ),
#         multiplication_ring.mul(lift_to_multiplication_ring(&c1), lift_to_multiplication_ring(&c1_prime))
#     );
#     let scale_down_rnsconv = AlmostExactRescalingConvert::new_with(
#         multiplication_ring.base_ring().as_iter().map(|Zp| zn_64::Zn::new(*Zp.modulus() as u64)).collect::<Vec<_>>(), 
#         vec![ zn_64::Zn::new(*plaintext_ring.base_ring().modulus() as u64) ], 
#         ciphertext_ring.base_ring().as_iter().map(|Zp| multiplication_ring.base_ring().as_iter().position(|Zp2| Zp2.modulus() == Zp.modulus()).unwrap()).collect::<Vec<_>>(),
#         Global
#     );
#     debug_assert!(scale_down_rnsconv.input_rings().iter().zip(multiplication_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
#     debug_assert!(scale_down_rnsconv.output_rings().iter().zip(ciphertext_ring.base_ring().as_iter()).all(|(lhs, rhs)| lhs.get_ring() == rhs.get_ring()));
#     let scale_down = |x: El<CiphertextRing>| {
#         let mut result = ciphertext_ring.get_ring().zero_non_fft();
#         scale_down_rnsconv.apply(multiplication_ring.get_ring().as_matrix_wrt_small_basis(&multiplication_ring.get_ring().undo_fft(x)), ciphertext_ring.get_ring().as_matrix_wrt_small_basis_mut(&mut result));
#         return result;
#     };
#     return (
#         scale_down(unscaled_result.0),
#         scale_down(unscaled_result.1),
#         scale_down(unscaled_result.2)
#     );
# }
# fn gen_relin_key(
#     ciphertext_ring: &CiphertextRing, 
#     sk: &El<CiphertextRing>, 
#     digits: usize
# ) -> RelinKey {
#     let sk_sqr = ciphertext_ring.pow(ciphertext_ring.clone_el(sk), 2);
#     let mut result0 = GadgetProductRhsOperand::new(ciphertext_ring.get_ring(), digits);
#     let mut result1 = GadgetProductRhsOperand::new(ciphertext_ring.get_ring(), digits);
#     let modulo_q = ciphertext_ring.base_ring().can_hom(&BigIntRing::RING).unwrap();
#     
#     let gadget_vector_len = result0.gadget_vector(ciphertext_ring.get_ring()).len();
#     for i in 0..gadget_vector_len {
#         let (b, a) = rlwe_sample(ciphertext_ring, sk);
#         let factor = result0.gadget_vector(ciphertext_ring.get_ring()).at(i);
#         let (key0, key1) = (ciphertext_ring.add(b, ciphertext_ring.inclusion().mul_ref_map(&sk_sqr, &factor)), a);
#         result0.set_rns_factor(ciphertext_ring.get_ring(), i, key0);
#         result1.set_rns_factor(ciphertext_ring.get_ring(), i, key1);
#     }
#     return (result0, result1);
# }
# fn relinearize(
#     ciphertext_ring: &CiphertextRing, 
#     three_component_ciphertext: (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>), 
#     relin_key: &RelinKey
# ) -> (SmallBasisEl<Pow2CyclotomicNumberRing>, SmallBasisEl<Pow2CyclotomicNumberRing>) {
#     let c2_decomposition = GadgetProductLhsOperand::from_double_rns_ring_with(ciphertext_ring.get_ring(), &three_component_ciphertext.2, relin_key.0.gadget_vector_digits());
#     let mut result0 = three_component_ciphertext.0;
#     ciphertext_ring.get_ring().add_assign_non_fft(&mut result0, &ciphertext_ring.get_ring().undo_fft(c2_decomposition.gadget_product(&relin_key.0, ciphertext_ring.get_ring())));
#     let mut result1 = three_component_ciphertext.1;
#     ciphertext_ring.get_ring().add_assign_non_fft(&mut result1, &ciphertext_ring.get_ring().undo_fft(c2_decomposition.gadget_product(&relin_key.1, ciphertext_ring.get_ring())));
#     return (result0, result1);
# }
let C = create_ciphertext_ring(1 << 8, 100);
let C_mul = create_multiplication_ring(&C);
let P = create_plaintext_ring(1 << 8, 5);
let digits = 2;
let sk = key_gen(&C);
let relin_key = gen_relin_key(&C, &sk, digits);

let message = P.int_hom().map(2);
let ciphertext = enc_sym(&P, &C, &message, &sk);

// we now have to explicity change from double-RNS to small-basis representation to use hom-mul
let ciphertext = (C.get_ring().undo_fft(ciphertext.0), C.get_ring().undo_fft(ciphertext.1));
let ciphertext_sqr = hom_mul_three_component(&P, &C, &C_mul, &ciphertext, &ciphertext);
let ciphertext_sqr_relin = relinearize(&C, ciphertext_sqr, &relin_key);

// finally, we have to explicitly change representation back
let ciphertext_sqr_relin = (C.get_ring().do_fft(ciphertext_sqr_relin.0), C.get_ring().do_fft(ciphertext_sqr_relin.1));
let result = dec(&P, &C, &ciphertext_sqr_relin, &sk);
assert_el_eq!(&P, P.pow(message, 2), result);
```

## Performance

Plugging in larger values in the above example, I find that on my desktop PC, homomorphic multiplication for `N = 16384` and `q ~ 2^100` takes only 50 ms!
This is clearly an impressive speedup compared to the 7.7 seconds we got in the first example [`crate::examples::bfv_impl_v1`].
In fact, a little more benchmarking shows that our implementation almost matches state-of-the-art HE libraries!
For example, for `N = 32768` and `q ~ 800`, I get 0.88 seconds, which is close to the 0.5 seconds that SEAL version 4.1.2 takes on my system.

Nevertheless, there does remain some optimization potential:
 - Currently, the native NTT of Fheanor is the same as in `feanor-math`, and it is not quite as fast as others.
   You can use the HEXL library (using the `feanor-math-hexl` library), which will give you an even faster NTT!
 - Apart from multiplication, decryption can also profit from a careful use of RNS conversions.
 - When doing the first RNS conversion `q -> qq'` during multiplication, note that the `mod q` part of the result is the same as the input.
   Hence, one can replace [`crate::rnsconv::lift::AlmostExactBaseConversion`] with [`crate::rnsconv::shared_lift::AlmostExactSharedBaseConversion`] which avoids recomputing these values and thus is slightly faster.

Implementing these points is left as an exercise.