# Report — Step 5: Re-include and adapt `src/bgv/bootstrap.rs`

This report covers Step 5: re-enabling `src/bgv/bootstrap.rs` and adjusting it to the refactored
codebase from Steps 1–4 (the streamlined primitive BGV API, the new `eval.rs` design with
`AsBGVPlaintext` / `EncodedBGVPlaintextRingBase` / `CiphertextOrNoRelin`, the `CiphertextDescriptor`
bundle, the `BGVModswitchStrategy` / `ModulusAwareCiphertext` changes, and the `CircuitEvaluator`
fan-out parameter).

Per the task, changes were kept as minimal as possible while making bootstrapping work.

## Status

- `cargo build --lib`, `cargo build --lib --tests` and `cargo build --examples` compile with
  **no new warnings**.
- `cargo test --lib` passes: **175 passed, 0 failed, 18 ignored**. This includes the three
  (non-ignored) BGV bootstrapping tests:
  - `bgv::bootstrap::test_digit_extract_homomorphic`
  - `bgv::bootstrap::test_pow2_bgv_thin_bootstrapping_17`
  - `bgv::bootstrap::test_composite_bgv_thin_bootstrapping_2_sparse_key_encapsulation`

## Module wiring

- Re-enabled `pub mod bootstrap;` in `src/bgv/mod.rs`.
- Added `use feanor_math::delegate::WrapHom;` and
  `use crate::bgv::eval::{AsBGVPlaintext, CiphertextOrNoRelin, EncodedBGVPlaintextRing, EncodedBGVPlaintextRingBase};`
  to `bootstrap.rs`. (`AsBGVPlaintext` now lives in `eval.rs`, not `modswitch.rs`.)

## Constants are now `EncodedBGVPlaintextRingBase`, not the ciphertext ring

The biggest structural change. Previously the slots-to-coeffs / coeffs-to-slots circuits stored
their (encoded) constants directly in the ciphertext ring
(`PlaintextCircuit<<CiphertextRing<Inst> as RingStore>::Type>`), relying on the old
`AsBGVPlaintext for <ciphertext ring>` impls. Step 2 removed those impls (exactly three impls now
exist: `PlaintextRing`, `BigIntRingBase`, `EncodedBGVPlaintextRingBase`). So, mirroring
`src/bfv/bootstrap.rs`:

- The circuit fields are now `PlaintextCircuit<EncodedBGVPlaintextRingBase<Inst>>`.
- `ThinBootstrapper` stores two encoded plaintext rings (both over the master ciphertext ring):
  `slots_to_coeffs_plaintext_ring` (plaintext modulus `p^r`) and `intermediate_plaintext_ring`
  (plaintext modulus `p^e`). The previous separate `original_plaintext_ring` /
  `intermediate_plaintext_ring` `PlaintextRing` fields are gone; the
  `base_plaintext_ring()` / `intermediate_plaintext_ring()` accessors now read the inner plaintext
  ring out of the encoded rings (exactly as BFV does).
- In `create()`, the constants are mapped into the encoded ring with
  `change_ring_uniform(|x| x.change_ring(|x| WrapHom::to_delegate_ring(encoded_ring.get_ring()).map(x)))`
  (BFV pattern), instead of the old `Inst::encode_plain(...)`. Both encoded rings are built over the
  **master** ciphertext ring; at evaluation time `EncodedBGVPlaintextRingBase::encoded_for` adjusts
  the encoded value (and its prepared multiplicant) to the actual, possibly modulus-switched-down,
  operand ring — so encoding over the master ring is correct even though the slots-to-coeffs
  transform runs at a reduced modulus.
- `create()` therefore needs `where Inst::CiphertextRing: Clone` (the master ring is reused for the
  two encoded rings and the stored `master_ciphertext_ring`). Both `build_pow2`/`build_odd` already
  required this bound, so no caller is affected.

The two `evaluate_circuit` calls (`perform_slots_to_coefficients`, `perform_coefficients_to_slots`)
now pass the corresponding encoded ring as the constant-`ring` argument (previously they passed the
ciphertext ring `C_master`).

## `ModulusAwareCiphertext` field changes

`ModulusAwareCiphertext` (Step 4) no longer has a separate `sk` field, its `data` is now a
`CiphertextOrNoRelin`, and its `info` is the `CiphertextDescriptor` bundle (which already tracks the
secret-key distribution and implicit scale). Accordingly, every `ModulusAwareCiphertext { .. }`
literal in `bootstrap.rs` was updated to:
- wrap the raw ciphertext as `CiphertextOrNoRelin::Relin(ct)`,
- drop the `sk: ...` field,
- and obtain `info` from `Strategy::fresh_encryption(...)` (renamed from the old
  `info_for_fresh_encryption`).

Wherever the old code consumed `result.data` / `ct.data` as a `Ciphertext`, it now uses
`.unwrap_relin()` (for owned values) or matches `CiphertextOrNoRelin::Relin(ct)` (for the debug-only
`dec_println*` reference paths). All these sites are provably relinearized: circuit outputs are
relinearized by `evaluate_circuit`, and the noisy-expansion / change-plaintext-modulus values are
ordinary ciphertexts.

### `perform_slots_to_coefficients`

The descriptor for the (never-modswitch) slots-to-coeffs evaluation is created with
`strategy.fresh_encryption(P_base, C_input, UniformTernary)` (matching the old hard-coded
`UniformTernary`). Because this path uses `never_modswitch` (so no modulus-switches occur inside the
transform) and the descriptor is discarded afterwards (only `result.data` is returned), the
descriptor's absolute implicit-scale value is irrelevant here: all derived ciphertexts/descriptors
stay internally consistent, so the `AssertEqual` policy used by the encoded-ring inner products does
not trip.

### `evaluate_bgv` change-plaintext-modulus closure

`Inst::change_plaintext_modulus` operates on a `Ciphertext`, so the closure unwraps
(`input.data.unwrap_relin()`), applies it, and re-wraps as `Relin`. As in the previous code, the
`info` descriptor is carried through unchanged. This is safe: the only effect of not re-deriving the
descriptor is on its implicit-scale value, and all subsequent digit-extraction operations use
integer/plaintext coefficients whose inner products **merge** the implicit scale (result scale `1`)
rather than asserting equality — so any transient divergence between the descriptor scale and the
ciphertext scale is harmless and is re-synchronized at the next inner product.

## Test adjustments (`bootstrap.rs` tests)

- `test_digit_extract_homomorphic` built its `DigitExtract` over the base `Zn` rings
  (`P1.base_ring(), P2.base_ring()`). `ZnBase` is no longer `AsBGVPlaintext` (Step 2). To match the
  real bootstrap path (`DigitExtract::new_default` builds over `Zn` then calls
  `embed_plaintext_ring`), the test now does
  `DigitExtract::new_digit_retain_based(&[P1.base_ring(), P2.base_ring()]).embed_plaintext_ring(&[&P1, &P2])`,
  giving a `DigitExtract<Inst::PlaintextRing>` (which **is** `AsBGVPlaintext`); the `rings` argument
  to `evaluate_bgv` is correspondingly `&[&P1, &P2]`.
- All result extractions use `.data.unwrap_relin()`, the `ModulusAwareCiphertext` literals use
  `CiphertextOrNoRelin::Relin(..)` + `fresh_encryption(..)` and drop the `sk` field, and the
  noise-budget prints bind the unwrapped ciphertext to a local before printing/decrypting.

## One necessary fix in `src/bgv/modswitch.rs` (Step 4 code)

Bootstrapping exposed a latent bug in `DefaultModswitchStrategy::gal_many`: it called
`rk.expect(...)` **eagerly** when relinearizing the input before a Galois automorphism, even when
the input is already relinearized. Linear transforms (slots-to-coeffs / coeffs-to-slots) are
evaluated with `rk = None` and contain Galois gates on relinearized ciphertexts, so this panicked.
The fix only `expect`s the relinearization key on the un-relinearized path:

```rust
let x = if x.data.is_norelin() {
    self.relinearize_if_needed(P, C_master, x, rk.expect(/* msg */), debug_sk)
} else {
    x
};
```

This matches the documented intent in REPORT_4 ("it `expect`s it only on the un-relinearized path")
and does not change the trait or any signatures. All previously-passing modswitch tests still pass.

## `where`-bound additions in `bootstrap.rs`

`perform_slots_to_coefficients` (and, transitively, `bootstrap_thin`) use the concrete
`never_modswitch` strategy, which is `DefaultModswitchStrategy<_, AlwaysZeroNoiseEstimator, false>`.
That type's `BGVModswitchStrategy` impl carries the Step-4 bounds
`N::CiphertextDescriptor: Clone` (here `()`, trivially satisfied) and
`<Params::PlaintextZnRing as RingBase>::Element: Clone`. The latter does not hold abstractly, so it
was added as `where <Inst::PlaintextZnRing as RingBase>::Element: Clone` to those two functions. It
holds for every concrete instantiation (the plaintext-`Zn` element type is `Copy`), so it is
transparent in practice — the same situation already noted in REPORT_4 for `clone_info`.

## Things intentionally left unchanged

- `prepare_input_for_slots_to_coefficients`, `SparseKeyEncapsulationKey`, the noisy-expansion math,
  and the public API of `ThinBootstrapper` (other than the `create`/`bootstrap_thin` `where` bounds
  above) are unchanged.
- The `bfv::bootstrap` module had already been re-enabled in Step 4 (it only depended on
  `compute_optimal_special_modulus`); nothing more was needed for it here.

# Review

 - First of all, I have changed your handling of Clone; Implicit scale and ciphertext descriptor shouldn't have to be `Clone`, since the noise estimator/rings can clone it. No more changes from your side required here
 - There seems to be a bug that `DefaultModswitchStrategy::inner_prod` can indirectly call `hom_inner_product_plain_encoded` with `ImplicitScalePolicy::AssertEqual` but non-equal implicit scales. Write a test that demonstrates this bug. Afterwards, find a fix. If it helps: I have the feeling like the handling of the implicit scale in `AsBGVPlaintext` is not properly specified: I would assume that `AsBGVPlaintext::hom_inner_product` would accept inputs with mixed implicit scale, but it uses `AssertEqual` internally. If this is not the behavior, write a doc comment on what it expects.
 - You have the comment `// both parts have implicit scale 1 (merging the implicit scale into the plaintext is free), // so the addition does not increase noise; use `Merge` to be robust regardless` in `src/bgv/modswitch.rs`; that's not good style - if they have the same implicit scale, use `AssertEqual` to make sure this assumption is correct.
# Review response

All three points addressed.

## 1. Clone handling

Picked up your change (no `Clone` bounds on the implicit scale / `CiphertextDescriptor`; `clone_info`
delegates to `noise_estimator.clone_ct`). The `where ...: Clone` bounds I had added to
`perform_slots_to_coefficients` / `bootstrap_thin` are gone accordingly. Nothing further from my side.

## 2. `inner_prod` → `hom_inner_product_plain_encoded` with mixed implicit scales

**Bug confirmed and reproduced.** New regression test
`bgv::modswitch::test_modswitch_strategy_inner_prod_encoded_mixed_scale`: it builds an
`EncodedBGVPlaintextRingBase` constant ring, encrypts three values, modulus-switches one of them
down (so that after `inner_prod` brings everything to the common base the summands have *different*
implicit scales), and computes an inner product with `Coefficient::Other` (encoded) coefficients.
Before the fix this panics with *"ImplicitScalePolicy::AssertEqual requires all summands to have the
same implicit scale"* (verified by temporarily reverting the fix); after the fix it decrypts to the
correct value.

**Fix.** As you suspected, the intended contract is that `AsBGVPlaintext::hom_inner_product` accepts
mixed implicit scales — the plaintext-ring and integer impls already do (their
`hom_inner_product_plain` / `_plain_scalar` fold each summand's scale into the coefficient for free).
Only the encoded impl used `AssertEqual`. It now uses `ImplicitScalePolicy::Merge` (data side:
`hom_inner_product`'s relin and norelin branches; noise side: `hom_inner_product_noise`), which
folds each summand's scale in via `merge_implicit_scale` (one scalar multiplication per ciphertext)
and yields a result with implicit scale `1`. I also documented this on the trait method
`AsBGVPlaintext::hom_inner_product`: it accepts arbitrary/mixed implicit scales and always returns
scale `1`.

## 3. `Merge`-"to be robust" comment in `inner_prod`

Replaced with `AssertEqual`, as requested. Both the integer part and the encoded/plaintext "main"
part now always produce implicit scale `1` (every `hom_inner_product` merges per summand), so
combining them with `AssertEqual` actively checks that invariant instead of silently papering over a
mismatch. Comment updated to state the invariant rather than the old hand-wave.

## Status

`cargo test --lib`: **176 passed, 0 failed, 18 ignored** (the 175 from before plus the new
regression test). `cargo build --lib --tests --examples` clean, no new warnings.
