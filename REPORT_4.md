# Report — Step 4: Re-include and refactor `src/bgv/modswitch.rs`

This report covers Step 4: re-enabling `src/bgv/modswitch.rs` and adapting it to the new
primitive-BGV API (Step 1), the new noise-estimation / `eval.rs` design (Step 2), and the
`CircuitEvaluator` fan-out parameter (Step 3); plus extending `DefaultModswitchStrategy` with
lazy relinearization.

`src/bgv/bootstrap.rs` remains commented out (Step 5).

## Status

- `cargo build --lib` and `cargo build --lib --tests` compile with **no new warnings**
  (the two pre-existing `src/bfv/mod.rs` warnings are gone now, see below).
- `cargo test --lib` passes: **167 passed, 11 ignored, 0 failed** (the 4 BGV modswitch tests
  are among them).
- `cargo build --examples` compiles (`examples/bgv_basics` uses
  `modswitch::drop_rns_factors_balanced`, which is re-enabled).

## Module wiring

- Re-enabled `pub mod modswitch;` in `src/bgv/mod.rs`.
- The old `AsBGVPlaintext` trait definition and its many impls (for `StaticRingBase<i64>`,
  `ZnBase`, `BigIntRingBase`, `NumberRingQuotientByIntBase`, `ManagedDoubleRNSRingBase`,
  `DoubleRNSRingBase`, `SingleRNSRingBase`) were **removed** from `modswitch.rs` — `AsBGVPlaintext`
  now lives in `src/bgv/eval.rs` (Step 2) with exactly the three required impls. `modswitch.rs`
  now `use super::eval::*`.
- Re-enabled `pub mod bootstrap;` in `src/bfv/mod.rs`, reverting the temporary Step-1 workaround
  (it had been disabled only because it imports `bgv::modswitch::compute_optimal_special_modulus`,
  which is available again). `bfv::bootstrap` compiles and its tests pass
  (`test_digit_extract_homomorphic`, `test_pow2_bfv_thin_bootstrapping_17`, …).

## `ModulusAwareCiphertext`

Now stores exactly the three requested fields:

```rust
pub struct ModulusAwareCiphertext<Params, Strategy> {
    pub data: CiphertextOrNoRelin<Params>,            // was: Ciphertext<Params>
    pub dropped_rns_factor_indices: Box<RNSFactorIndexList>,
    pub info: Strategy::CiphertextInfo,               // CiphertextDescriptor bundle (see below)
}
```

The previous separate `sk` field is **gone**: the secret-key distribution (and the implicit scale)
are now tracked inside the `CiphertextDescriptor` bundle, which is `DefaultModswitchStrategy`'s
`CiphertextInfo`:

```rust
type CiphertextInfo = CiphertextDescriptor<Params, N>;   // { noise, implicit_scale, sk }
```

Wherever the old code read `x.sk` / `x.data.implicit_scale`, it now reads `x.info.sk` /
`x.info.implicit_scale`.

## `BGVModswitchStrategy` trait

The trait is kept as-is (same associated type and same methods `evaluate_circuit`,
`info_for_fresh_encryption`, `clone_info`, `print_info`, `clone_ct`). The only adjustment is the
body of the default `clone_ct`, which now clones `data` via `CiphertextOrNoRelin::clone_ct` and no
longer copies a `sk` field.

### One necessary `where`-bound (please flag if undesired)

`clone_info(&self, info: &Self::CiphertextInfo) -> Self::CiphertextInfo` has no `P`/`C` parameters,
but the new bundled `CiphertextInfo = CiphertextDescriptor<Params, N>` contains a noise descriptor
(`N::CiphertextDescriptor`) and an implicit scale (`<Params::PlaintextZnRing as RingBase>::Element`),
neither of which can be cloned without either a ring or a `Clone` bound. To keep the **trait
signature byte-for-byte unchanged**, I added

```rust
where N::CiphertextDescriptor: Clone,
      <Params::PlaintextZnRing as RingBase>::Element: Clone
```

to the three `impl` blocks that mention `DefaultModswitchStrategy` (`impl DefaultModswitchStrategy`,
the `CircuitEvaluator` impl, and `impl BGVModswitchStrategy for DefaultModswitchStrategy`). Both
bounds hold for every concrete instantiation (the noise descriptors of `NaiveBGVNoiseEstimator` /
`AlwaysZeroNoiseEstimator` are `Copy`, and the plaintext-`Zn` element type `ZnEl` is `Copy`), so
this is transparent in practice. The alternative — adding `P`/`C` parameters to `clone_info` — would
change the trait, which the task asked to avoid.

(Note: internal cloning, e.g. in `inner_prod`, does *not* rely on `clone_info`; it clones via
`estimator.clone_ct(P, C, …)` and `CiphertextOrNoRelin::clone_ct(P, C)`, which have the rings
available. Only the public `clone_ct`/`clone_info` path needs the bounds.)

## Lazy relinearization in `DefaultModswitchStrategy`

The four bullet points from the task are implemented as follows.

### 1./2. Fan-out-driven lazy vs. eager relinearization (`mul`, `square`)

`mul`/`square` receive the gate `fan_out` (Step 3). After deciding the modulus-switch
(`compute_optimal_mul_modswitch`, unchanged in spirit, only adapted to the new noise API) and
mod-switching the operands, the product is first computed **un-relinearized** via
`Params::hom_mul_norelin` / `hom_square_norelin`:

- `fan_out == 1`: lazy — return a `ModulusAwareCiphertext` holding a `CiphertextNoRelin`
  (noise via `estimator.hom_mul_norelin` / `hom_square_norelin`); relinearization is deferred.
- `fan_out != 1`: eager — relinearize now (`Params::relinearize` + `estimator.relinearize`),
  using the special modulus computed by `compute_optimal_mul_modswitch`.

**Why the deferred relinearization does not waste a modulus level.** A lazy product is mod-switched
to `C_target` (the special-modulus RNS factors are dropped, exactly as in the eager case). When it
is later relinearized (`relinearize_if_needed`, see below) it calls
`compute_optimal_special_modulus(…, drop_additional = 0, …)`, i.e. it reserves its special modulus
**among the already-dropped factors** and drops **no additional** factors. Hence a lazy product that
is later relinearized once ends up at the same modulus as the eager path would have — but when
several lazy products are summed first (the motivating case from `TASK.md`), only **one**
relinearization (key-switch) is performed on the sum instead of one per product.

### 3. Inner products propagate the un-relinearized state (`inner_prod`)

`inner_prod` splits the summands into an integer part (handled via `BigIntRingBase`) and a "main"
part (handled via the circuit's constant ring `R`), mod-switches all referenced ciphertexts to the
common base, and computes each part with the new `AsBGVPlaintext::hom_inner_product`. That routine
already returns an un-relinearized result as soon as any summand is un-relinearized; combining the
two parts (`add_ct`, mirroring `eval.rs`) likewise yields a `CiphertextNoRelin` if either part is
un-relinearized. So an inner product is un-relinearized iff at least one summand is.

The old hand-rolled implicit-scale optimization (choosing an output scale equal to the noisiest
ciphertext's scale and pre-scaling coefficients) was dropped: per the Step-1 review decision,
`hom_inner_product_plain`/`_plain_scalar` always merge the implicit scale into the (plaintext)
multiplicand for free, giving result scale `1`. The two parts are combined with
`ImplicitScalePolicy::Merge` (harmless when both are already scale `1`).

### 4. Relinearize-before-consume (`mul`, `square`, `gal`)

A new helper `relinearize_if_needed` relinearizes an un-relinearized operand in place (w.r.t. its
current modulus, `drop_additional = 0`). It is called at the start of `mul` (both operands),
`square`, and `gal_many` (the input). `gal_many` therefore now also receives the relinearization key
(`rk`, threaded through from the evaluator); it `expect`s it only on the un-relinearized path
(un-relinearized ciphertexts can only arise from a multiplication, which requires `rk`).

### Output relinearization

Because a final gate with fan-out 1 (feeding a single output) is left lazy, circuit *outputs* could
be un-relinearized. `evaluate_circuit` now relinearizes any un-relinearized output before returning,
so callers always receive ordinary, decryptable ciphertexts (matching the previous behavior). This
also realizes the intended benefit: an output that is a sum of products is relinearized exactly once.

## `CircuitEvaluator` impl (`BGVEvaluator`)

- `mul`/`square` take the new `fan_out: usize` and forward it to the strategy.
- `gal` forwards `self.rk` so the input can be relinearized first if needed.
- `supports_mul` simplified to `self.rk.is_some()` (the old `self.rk.is_some() && self.rk.is_some()`
  was a duplicated check).
- `add_constant` uses the new `AsBGVPlaintext::hom_add_to` / `hom_add_to_noise` (no `dropped_factors`
  argument — the passed ciphertext ring is already the operand ring) and preserves the
  relinearization state.

## Test changes

The behavior under test is unchanged; only the constant ring had to be adapted, because
`StaticRingBase<i64>` (`ZZi64`) and `ZnBase` are **no longer** `AsBGVPlaintext` (Step 2 keeps exactly
three impls):

- The pure mul/square circuits in `test_modswitch_strategy_mul` /
  `test_never_modswitch_strategy_mul` were built over `ZZi64`; they are now built over `ZZbig`
  (`BigIntRingBase` is `AsBGVPlaintext`). These circuits have no constants, so this is purely a
  type change.
- `test_modswitch_strategy_evaluate_circuit`'s digit-retain circuit has constants in `P.base_ring()`
  (a `Zn`); it is now `change_ring`-mapped into the plaintext ring `P` (which is `AsBGVPlaintext`),
  and the reference evaluation uses `P.identity()` accordingly.
- All result extractions use `res.data.unwrap_relin()` (outputs are relinearized, see above) and the
  fresh-encryption inputs wrap the ciphertext in `CiphertextOrNoRelin::Relin(...)` and drop the
  removed `sk` field. The decryption/noise-budget assertions are unchanged and still pass (including
  `assert_eq!(0, res_noise)` for the never-modswitch pow8 case).

## Decisions for review

- **Modulus-switch decision in the lazy case.** I deliberately reuse `compute_optimal_mul_modswitch`
  (which optimizes the *relinearized* product noise) for both the lazy and the eager path, rather
  than introducing a separate norelin-specific optimizer. As argued above, this is not wasteful
  because the deferred relinearization reserves its special modulus among the already-dropped
  factors. Refining the lazy-case modswitch decision (e.g. optimizing the un-relinearized product
  noise directly) is a possible future improvement.
- **Encoded-ring constants in `inner_prod`.** When the circuit's constant ring is
  `EncodedBGVPlaintextRingBase`, `AsBGVPlaintext::hom_inner_product` uses
  `ImplicitScalePolicy::AssertEqual` (the Step-2 design, since merging an *encoded* plaintext is not
  free). If such an inner product mixes ciphertexts that ended up at different implicit scales (e.g.
  via different mod-switch histories), this will panic. The realistic constant rings (plaintext ring,
  integers, scalars) all merge the scale for free and are unaffected. I left this matching the
  `eval.rs` design rather than force-merging scales into ciphertexts (which would cost noise). Flag
  if you'd prefer `inner_prod` to pre-equalize scales for the encoded case.
- **`where N::CiphertextDescriptor: Clone` + element `Clone`** on the `DefaultModswitchStrategy`
  impls (see the trait section above).
- **Re-enabling `bfv::bootstrap`** now (rather than in Step 5), since its only `bgv` dependency
  (`compute_optimal_special_modulus`) is available again and this cleanly removes the Step-1
  workaround. Flag if you'd rather keep it disabled until Step 5.
