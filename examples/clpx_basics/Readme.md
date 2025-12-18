# Homomorphic operations using the CLPX scheme in Fheanor

CLPX was proposed in "High-Precision Arithmetic in Homomorphic Encryption" by Chen, Laine, Player and Xia (<https://ia.cr/2017/809>), and can be described as a variant of BFV that supports computations with large integers.
As such, its use is very similar to BFV, and we recommend the reader to first have a look at [`crate::examples::bfv_basics`].
In this example, we will then focus on the points that are different from standard BFV.

## Setting up CLPX

The design of CLPX is exactly as for BFV (or BGV), so we start by choosing a ciphertext ring instantiation (i.e. a type implementing [`crate::clpx::CLPXInstantiation`], which determines the type of the ciphertext ring that will be used) and use it to set up the ciphertext ring.
```rust
# use anonymizedhelibrary::clpx::{CLPXInstantiation, CiphertextRing, Pow2CLPX};
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use std::marker::PhantomData;
let log2_N = 12;
let params = Pow2CLPX::new(2 << log2_N);
let log2_t_can_norm_bound = 10;
let (C, C_for_multiplication): (CiphertextRing<Pow2CLPX>, CiphertextRing<Pow2CLPX>) = params.create_ciphertext_rings(105..110, log2_t_can_norm_bound);
```
It turns out that a lot of functionality of CLPX is exactly as in BFV, and the type [`crate::clpx::Pow2CLPX`] is actually just type aliases to its BFV equivalent.
Really the only difference here is that [`crate::clpx::CLPXInstantiation::create_ciphertext_rings()`] takes another parameter - a bound on `log_2(| t |_can)`, which is required to compute how large the modulus of `C_for_multiplication` has to be.
Here we just set it to `10`, which means we can later choose any `t` with `| t |_can <= 1024`, which is satisfied by all `t` we might be interested in.
Generally speaking, this can be a rough bound, since its impact on performance is not very large.

Next, we create the plaintext ring.
```rust,should_panic
# use anonymizedhelibrary::clpx::{CLPXInstantiation, CiphertextRing, Pow2CLPX};
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use std::marker::PhantomData;
# let log2_N = 12;
# let params = Pow2CLPX::new(2 << log2_N);
# let log2_t_can_norm_bound = 10;
# let (C, C_for_multiplication): (CiphertextRing<Pow2CLPX>, CiphertextRing<Pow2CLPX>) = params.create_ciphertext_rings(105..110, log2_t_can_norm_bound);
let P = params.create_plaintext_ring::<true>(todo!(), todo!(), todo!(), todo!());
```
This is actually more involved than in the BFV setting, as you can see by the four parameters.
The reason is that the plaintext ring of CLPX is `Z[X]/(Phi_m(X), t(X), p^e)` for a polynomial `t(X)` and a prime `p`, which should be isomorphic to `(Z/p^eZ)[X]/(f(X))` for some polynomial `f(X)`.
It is important that we can compute this isomorphism - on the one hand, we usually want to think of plaintexts as elements of `(Z/p^eZ)[X]/(f(X))`, but when encrypting them, we need to find short lifts to `Z[X]/(Phi_m(X))`.
The data associated to this isomorphism is mostly computed by [`crate::clpx::CLPXInstantiation::create_plaintext_ring()`], when given `Z[X]`, `t(X)` and `p`.
However, it currently does not compute one thing, and that is the subgroup of the Galois group that fixes the ideal `(t(𝝵), p^e)`.
This is the group that then acts on the CLPX plaintext ring as kind of Galois group, and its order will be equal to the degree of `f(X)`.
We have to manually pass this subgroup as fourth parameter, but the implementation will check that it is indeed correct.

As an example, consider the following possible choices of `m`, `p` and `t(X)`:

| `m`       | `t(X)`      | `p`                                                               | Galois group |
| --------- | ----------- | ----------------------------------------------------------------- | ------------ |
| `2^12`    | `X^128 + 2` | `65537`                                                           |       `<33>` |
| `2^12`    | `X^32 + 2`  | `67280421310721`                                                  |      `<129>` |
| `2^12`    | `X^8 + 2`   | `93461639715357977769163558199606896584051237541638188580280321`  |      `<513>` |
| `17 * 5`  | `X - 2`     | `9520972806333758431`                                             |        `{1}` |
| `17 * 31` | `X^31 - 2`  | `131071`                                                          |       `<52>` |
| `17 * 31` | `X^17 - 2`  | `2147483647`                                                      |       `<63>` |
| `17 * 31` | `X - 2`     | *a number so large that we cant easily find its prime factors...* |        `{1}` |

Indeed, as this table shows, a suitable choice of `t` means that we can effectively perform arithmetic modulo some very large modulus.

The ring returned by `create_plaintext_ring()` looks like `(Z/p^eZ)[X]/(f(X))`, but it supports lifting to and reducing from `Z[X]/(Phi_m(X))` via the functions [`crate::clpx::encoding::CLPXPlaintextRingBase::small_lift()`] and [`crate::clpx::encoding::CLPXPlaintextRingBase::reduce_mod_t()`].
Hence, we can use CLPX as follows:
```rust
# use anonymizedhelibrary::clpx::{CLPXInstantiation, CiphertextRing, Pow2CLPX, SecretKeyDistribution};
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::number_ring::AbstractNumberRing;
# use anonymizedhelibrary::number_ring::galois::CyclotomicGaloisGroupOps;
# use feanor_math::group::AbelianGroupStore;
# use feanor_math::rings::poly::dense_poly::DensePolyRing;
# use feanor_math::rings::poly::*;
# use feanor_math::integer::*;
# use feanor_math::homomorphism::*;
# use feanor_math::primitive_int::*;
# use feanor_math::ring::*;
# use feanor_math::assert_el_eq;
# use std::marker::PhantomData;
# let log2_N = 12;
# let params = Pow2CLPX::new(2 << log2_N);
# let log2_t_can_norm_bound = 10;
# let (C, C_for_multiplication): (CiphertextRing<Pow2CLPX>, CiphertextRing<Pow2CLPX>) = params.create_ciphertext_rings(105..110, log2_t_can_norm_bound);
let ZZX = DensePolyRing::new(BigIntRing::RING, "X");
let p = BigIntRing::RING.get_ring().parse("93461639715357977769163558199606896584051237541638188580280321", 10).unwrap();
let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(16) + 2]);
let full_galois_group = params.number_ring().galois_group();
let acting_galois_group = full_galois_group.get_group().clone().subgroup([full_galois_group.from_representative(513)]);
// the computation is slightly expensive, thus you can pass true as generic argument to log progress to stdout
let P = params.create_plaintext_ring::</* LOG = */ true>(ZZX, t, p, acting_galois_group);

let mut rng = rand::rng();
let sk = Pow2CLPX::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
let m = P.inclusion().map(P.base_ring().coerce(&BigIntRing::RING, BigIntRing::RING.power_of_two(100)));
let ct = Pow2CLPX::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
let res = Pow2CLPX::dec(&P, &C, ct, &sk);
assert_el_eq!(P, &m, &res);
```
Applying homomorphic operations is just as easy as for BFV as well. 
```rust
# use anonymizedhelibrary::clpx::{CLPXInstantiation, CiphertextRing, Pow2CLPX, SecretKeyDistribution};
# use anonymizedhelibrary::DefaultNegacyclicNTT;
# use anonymizedhelibrary::gadget_product::digits::RNSGadgetVectorDigitIndices;
# use anonymizedhelibrary::number_ring::AbstractNumberRing;
# use anonymizedhelibrary::number_ring::galois::CyclotomicGaloisGroupOps;
# use feanor_math::group::AbelianGroupStore;
# use feanor_math::rings::poly::dense_poly::DensePolyRing;
# use feanor_math::rings::poly::*;
# use feanor_math::integer::*;
# use feanor_math::homomorphism::*;
# use feanor_math::primitive_int::*;
# use feanor_math::rings::extension::FreeAlgebraStore;
# use feanor_math::rings::zn::ZnRingStore;
# use feanor_math::ring::*;
# use feanor_math::assert_el_eq;
# use feanor_math::seq::*;
# use std::marker::PhantomData;
# let log2_N = 12;
# let params = Pow2CLPX::new(2 << log2_N);
# let log2_t_can_norm_bound = 10;
# let (C, C_for_multiplication): (CiphertextRing<Pow2CLPX>, CiphertextRing<Pow2CLPX>) = params.create_ciphertext_rings(105..110, log2_t_can_norm_bound);
# let ZZX = DensePolyRing::new(BigIntRing::RING, "X");
# let p = BigIntRing::RING.get_ring().parse("93461639715357977769163558199606896584051237541638188580280321", 10).unwrap();
# let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(16) + 2]);
# let full_galois_group = params.number_ring().galois_group();
# let acting_galois_group = full_galois_group.get_group().clone().subgroup([full_galois_group.from_representative(513)]);
# // the computation is slightly expensive, thus you can pass true as generic argument to log progress to stdout
# let P = params.create_plaintext_ring::<true>(ZZX, t, p, acting_galois_group);
let mut rng = rand::rng();
let sk = Pow2CLPX::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
let rk = Pow2CLPX::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(2, C.base_ring().len()), 3.2);
let m = P.inclusion().map(P.base_ring().coerce(&BigIntRing::RING, BigIntRing::RING.power_of_two(100)));
let ct = Pow2CLPX::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
let ct_sqr = Pow2CLPX::hom_square(&P, &C, &C_for_multiplication, ct, &rk);
let res = Pow2CLPX::dec(&P, &C, ct_sqr, &sk);
let res_constant_coeff = P.wrt_canonical_basis(&res).at(0);
assert_el_eq!(BigIntRing::RING, BigIntRing::RING.power_of_two(200), P.base_ring().smallest_positive_lift(res_constant_coeff));
```
