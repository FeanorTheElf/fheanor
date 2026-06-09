# Report — Step 2: Noise estimation refactor + new `src/bgv/eval.rs`

This report covers Step 2: creating `src/bgv/eval.rs` (which now holds `AsBGVPlaintext`)
and the accompanying noise-estimation refactor described in the "## Noise Estimation"
section of `TASK.md`. As confirmed up front, the full noise-estimator refactor was done as
part of this step (since `eval.rs`'s `*_noise` functions depend on it), and the
`BGVNoiseEstimator` methods take/return the new bundled descriptor.

`src/bgv/modswitch.rs` and `src/bgv/bootstrap.rs` remain commented out (Steps 4/5).

## Status

- `cargo build --lib` compiles; `cargo build --lib --tests` compiles.
- `cargo test --lib bgv::` passes: 12 passed, 3 ignored (the `#[ignore]` benchmarks), 0 failed.
  This includes two new tests in `eval.rs`.
- The only build warnings are the two pre-existing ones in `src/bfv/mod.rs` (unused
  `PlaintextCircuit` / `group` imports, a consequence of the Step-1 commenting-out of
  `bfv::bootstrap`); none come from the new code.
- The `examples/bgv_basics/main.rs` example does **not** compile, because it imports
  `fheanor::bgv::modswitch::drop_rns_factors_balanced` from the still-commented `modswitch`
  module. This is unchanged from the Step-1 state (it broke when `modswitch` was commented
  out) and will resolve once `modswitch` is re-included in Step 4.

## Modules re-included (`src/bgv/mod.rs`)

`pub mod noise_estimator;` was re-enabled and `pub mod eval;` was added; `modswitch` and
`bootstrap` stay commented out.

## Noise estimation (`src/bgv/noise_estimator.rs`, full rewrite)

### New struct `CiphertextDescriptor`

```rust
pub struct CiphertextDescriptor<Params: BGVInstantiation, N: BGVNoiseEstimator<Params> + ?Sized> {
    pub noise: N::CiphertextDescriptor,                 // the estimator-specific noise descriptor
    pub implicit_scale: <Params::PlaintextZnRing as RingBase>::Element,
    pub sk: SecretKeyDistribution,
}
```

This is the noise-side analogue of `Ciphertext`: it bundles the estimator-specific noise
descriptor with the deterministic per-ciphertext data (implicit scale + secret-key
distribution). A single `CiphertextDescriptor` describes either a `Ciphertext` or a
`CiphertextNoRelin` (the noise estimate does not depend on the relinearization state).

### `BGVNoiseEstimator` now mirrors `BGVInstantiation`

Every method takes/returns `CiphertextDescriptor<Params, Self>` (replacing `Ciphertext` /
`CiphertextNoRelin`), `KeySwitchKeyDescriptor` (replacing key-switch keys), and
`SecretKeyDistribution` (replacing secret keys). As with `BGVInstantiation`, most operations
are **default methods** that delegate to a small set of **primitive** methods, so an estimator
only implements the latter:

- Primitives: `estimate_log2_relative_noise_level`, `clone_ct`, `enc_sym_zero`,
  `transparent_zero`, `hom_add_plain_encoded`, `hom_mul_plain_encoded`, `hom_mul_plain_int`,
  `hom_add`, `key_switch`, `hom_mul_norelin`, `mod_switch_ct`, `change_plaintext_modulus`.
- Defaults (mirroring `BGVInstantiation`'s delegating defaults): `enc_sym`, `hom_add_plain`,
  `hom_add_plain_scalar`, `hom_mul_plain`, `hom_mul_plain_scalar`, `merge_implicit_scale`,
  `hom_sub`, `hom_mul`, `relinearize`, `hom_square`, `hom_square_norelin`, `hom_galois`,
  `hom_galois_many`, `mod_switch_norelin`, and the three `hom_inner_product_plain*` families.

The deterministic implicit-scale arithmetic is factored into free helpers (`mul_scale`,
`mod_switch_scale`, `change_plaintext_modulus_scale`, `add_scale`) shared by both estimators.

`NaiveBGVNoiseEstimator`'s inner descriptor was reduced to just
`log2_relative_critical_quantity: f64` (the `sk` moved into the bundle). The noise formulas
are unchanged from the previous version. `AlwaysZeroNoiseEstimator` still tracks the implicit
scale and secret-key distribution (these are needed for correctness, not just noise).

### Deviations from a strict 1:1 mirror (for review)

- **Randomness / `sigma`.** `enc_sym_zero` etc. drop the `rng`, and noise std-deviations are
  not separate parameters; the relevant `sigma` is carried by `KeySwitchKeyDescriptor` as
  before.
- **`hom_mul_plain_int`.** Kept as a noise-only primitive (it existed before): the size of an
  integer multiplicand bounds the noise growth more tightly than routing through the plaintext
  ring. `hom_mul_plain_scalar`'s default uses it.
- **Inference instead of explicit index lists.** To match `BGVInstantiation`'s signatures,
  `key_switch` infers the special modulus from `C`/`C_special`, and `mod_switch_ct` infers the
  dropped factors from `Cnew`/`Cold`, rather than receiving an explicit `RNSFactorIndexList`.
- **`clone_ct` / `transparent_zero` / `change_plaintext_modulus`** take `&self` and the
  relevant rings (so the implicit scale can be cloned/derived); `change_plaintext_modulus` is
  `&self` rather than static.
- **`mod_switch_to_plaintext`** (which returns plaintext-ring elements, not a ciphertext) is
  **not** mirrored on the noise side — it is only used by bootstrapping and needs no noise
  estimate there. Flag if you'd like a noise equivalent anyway.
- **`*_norelin` noise variants.** Since the descriptor is relinearization-agnostic, the
  `_norelin` operations are provided as defaults that delegate to their relinearized
  counterparts.

## Evaluation (`src/bgv/eval.rs`, new file)

### `CiphertextOrNoRelin`

```rust
pub enum CiphertextOrNoRelin<Params> { Relin(Ciphertext<Params>), NoRelin(CiphertextNoRelin<Params>) }
```

The operand type for all `AsBGVPlaintext` data operations, with helpers `implicit_scale`,
`is_norelin`, `into_norelin` (promotes a `Ciphertext` by setting `c2 = 0`), `unwrap_relin`,
`clone_ct`, and `From` conversions.

### `AsBGVPlaintext`

```rust
pub trait AsBGVPlaintext<Params: BGVInstantiation>: RingBase {
    fn hom_add_to(..., ct: CiphertextOrNoRelin<Params>) -> CiphertextOrNoRelin<Params>;
    fn hom_mul_to(..., ct: CiphertextOrNoRelin<Params>) -> CiphertextOrNoRelin<Params>;
    fn hom_inner_product<I>(...) -> CiphertextOrNoRelin<Params> where I: IntoIterator<Item = (Self::Element, CiphertextOrNoRelin<Params>)>;
    fn hom_add_to_noise<N>(..., ct: &CiphertextDescriptor<Params,N>) -> CiphertextDescriptor<Params,N>;
    fn hom_mul_to_noise<N>(...) -> CiphertextDescriptor<Params,N>;
    fn hom_inner_product_noise<N,L,R,I>(...) -> CiphertextDescriptor<Params,N>;
}
```

- `hom_inner_product_ref` was removed (as instructed).
- The old `dropped_factors: &RNSFactorIndexList` parameter is gone; the ciphertext ring `C`
  passed in already is the (possibly modulus-switched-down) operand ring, mirroring
  `bfv/eval.rs`. `EncodedBGVPlaintextRingBase` derives the dropped factors itself from `C` vs.
  its stored ciphertext ring.
- **Relinearization-state propagation:** `hom_add_to`/`hom_mul_to` preserve the state;
  `hom_inner_product` returns an un-relinearized result as soon as any summand is
  un-relinearized (promoting the relinearized summands via `into_norelin`).
- `hom_inner_product` / `hom_inner_product_noise` have fold-based default implementations and
  are overridden by all three impls with the accelerated `Params::hom_inner_product_plain*`
  (resp. `estimator.hom_inner_product_plain*`) variants.

### The three impls

Exactly the three required impls exist:

1. **`Params::PlaintextRing`** — see the note below; delegates to `hom_add_plain` /
   `hom_mul_plain` / `hom_inner_product_plain` (and the `_norelin` variants).
2. **`BigIntRingBase`** — integer constants; delegates to `hom_*_plain_scalar` (reducing the
   integer mod `t`, which is correct and lower-noise) and `hom_mul_plain_int` for noise.
3. **`EncodedBGVPlaintextRingBase`** — a new ring (mirroring `EncodedBFVPlaintextRingBase`)
   whose elements carry the plaintext, its `encode_plain` image in a fixed ciphertext ring,
   and a `PreparedMultiplicant`. `hom_mul_to` uses the prepared multiplicant on the fast path
   (when the operand ring equals the stored ring) and otherwise drops RNS factors and falls
   back to `hom_mul_plain_encoded`.

### Decisions for review

- **`impl ... for Params::PlaintextRing` cannot be written literally.** An associated-type
  projection in the self-type position is opaque to coherence, so the literal
  `impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for Params::PlaintextRing` is rejected
  as conflicting with the `BigIntRingBase` and `EncodedBGVPlaintextRingBase` impls (E0119). I
  used the same workaround the previous code used: implement for the concrete plaintext-ring
  type `NumberRingQuotientByIntBase<NumberRing<Params>, Zn>` with a
  `BGVInstantiation<PlaintextRing = ...>` where-clause. This *is* `Params::PlaintextRing` for
  every current instantiation (all of `Pow2BGV`, `CompositeBGV`, `CompositeSingleRNSBGV` use
  this plaintext ring type). Please flag if you'd prefer a different structure.
- **`hom_inner_product` operand ownership.** The data inner product consumes owned
  `(Self::Element, CiphertextOrNoRelin)` items; the noise inner product takes
  `(Borrow<Self::Element>, Borrow<CiphertextDescriptor>)`. Happy to align these if you prefer.
- **`EncodedBGVPlaintextRingBase` inner products don't use the prepared multiplicant.** Only
  single `hom_mul_to` exploits it; inner products go through `Params::hom_inner_product_plain_encoded`
  (which uses the ciphertext ring's accelerated `ComputeInnerProduct`). A prepared-multiplicant
  inner product could be added later if profiling warrants it.

## Tests added (`src/bgv/eval.rs`)

- `test_as_bgv_plaintext_ops`: exercises `hom_add_to` / `hom_mul_to` / `hom_inner_product` for
  all three constant rings, both the relinearized and un-relinearized paths, the relin/norelin
  mixing rule for inner products, and the `EncodedBGVPlaintextRingBase` prepared-multiplicant
  fast path; decryptions are checked against expected values.
- `test_as_bgv_plaintext_noise`: checks that plaintext-ciphertext multiplication increases the
  estimated noise while addition does not, and that the inner-product noise estimate is finite.

# Review

Please fix the following points:
 - I'm surprised that `impl<Params> AsBGVPlaintext<Params> for Params::PlaintextRing`; After all, `EncodedBGVPlaintextRingBase` is not `NumberRingQuotient`, which is necessary to be any `Param::PlaintextRing`. But ok, if it doesn't work, try first `impl<Params, R> AsBGVPlaintext<Params> for R where Params: BGVInstantiation<PlaintextRing = R>, R: NumberRingQuotient`; if that also doesn't work, do what is done in `src/bfv/eval.rs`, i.e. `impl<Params, R> AsBGVPlaintext<Params> for R where Params::PlaintextRing: CanHomFrom<R>, R: NumberRingQuotient`. I don't want to have a separate implementation for every ring that is used as plaintext ring by some `BGVInstantiation`.
 - It's a bit annoying that `EncodedBGVPlaintextRing::hom_inner_product` cannot currently use the prepared operand. However, fixing that for now would go beyond the scope of this refactor, so just add a note there explaining why this is difficult and that this choice was made, potentially to be fixed in the future.
 - Let's leave the ownership question on the `inner_product` functions as-is for now. While `Borrow` pattern might be an improvement, I just realized that here and for `BGVInstantiation`, the even better choice would actually be to use `src/boo.rs`. But let's leave it for now, to be fixed later.
# Review response

- **`AsBGVPlaintext` for the plaintext ring.** Replaced the concrete
  `NumberRingQuotientByIntBase` impl with the first form you suggested:
  ```rust
  impl<Params, R> AsBGVPlaintext<Params> for R
      where Params: BGVInstantiation<PlaintextRing = R>, R: NumberRingQuotient
  ```
  This compiles: the `R: NumberRingQuotient` bound lets coherence rule out overlap with the
  `BigIntRingBase` and `EncodedBGVPlaintextRingBase` impls (neither is `NumberRingQuotient`), so
  the second (`CanHomFrom`) fallback was not needed. There is no longer a per-ring impl.
  (One incidental rename: in this impl the `hom_inner_product_noise` method's `R` type
  parameter was renamed to `Rhs` to avoid clashing with the new impl-level `R`.)
- **`EncodedBGVPlaintextRingBase::hom_inner_product` not using the prepared operand.** Added a
  `NOTE` comment at that method explaining why (no prepared-operand inner-product routine on the
  ciphertext ring, plus the modulus-switched-down case where the stored prepared multiplicant no
  longer applies), that it still uses the ring's accelerated `ComputeInnerProduct`, and that this
  is a deliberate scope choice to potentially revisit later.
- **Ownership of the `inner_product` operands.** Left as-is, per your note (to be revisited later,
  possibly using `src/boo.rs`).

# Human approved