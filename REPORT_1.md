# Report — Step 1: Refactoring `src/bgv/mod.rs`

This report covers Step 1 of the circuit-evaluation refactoring: streamlining the
primitive BGV API in `src/bgv/mod.rs` (trait `BGVInstantiation`). As instructed,
`src/bgv/{noise_estimator,modswitch,bootstrap}.rs` remain commented out, so this step
was tested in isolation.

## Status

- The crate compiles (`cargo build --lib`).
- All non-ignored BGV tests pass (`cargo test --lib bgv::`): 9 passed, 3 ignored
  (the `#[ignore]` benchmarks), 0 failed.

## Two pre-existing build blockers I had to address first

The branch did **not** compile as handed over. Two issues, both consequences of the
task-setup commit (`Added claude-code task`):

1. **Accidental typo in `src/bfv/mod.rs`.** The task commit introduced
   `#[instrument(skip_all)]h fu` on the `create_ciphertext_rings` method of
   `CompositeSingleRNSBFV`. This is clearly a stray keystroke; I reverted it to
   `#[instrument(skip_all)]`.

2. **`bfv::bootstrap` depends on the now-disabled `bgv::modswitch`.**
   `src/bfv/bootstrap.rs` imports `crate::bgv::modswitch::compute_optimal_special_modulus`.
   Commenting out `bgv::modswitch` therefore breaks `bfv::bootstrap` (and produced the
   cascading "type annotations needed" errors at `bfv/bootstrap.rs:253,349`).

   Nothing else in the crate depends on `bfv::bootstrap`, so — mirroring exactly what the
   task did for the bgv submodules — I **temporarily commented out `pub mod bootstrap;` in
   `src/bfv/mod.rs`** (with a comment explaining why). I will re-enable it in Step 5 once
   `bgv::modswitch` is re-included. **Please flag in review if you'd prefer a different
   resolution** (e.g. relocating `compute_optimal_special_modulus`).

## Changes to `BGVInstantiation`

### New types

- **`ImplicitScalePolicy`** (`enum { Merge, AssertEqual }`): controls how implicit scales
  are handled by operations that add ciphertexts.
  - `Merge`: each summand is first rescaled to implicit scale `1` (via
    `merge_implicit_scale`), and the result has implicit scale `1`.
  - `AssertEqual`: asserts all summands share the same implicit scale, adds directly, and
    keeps that scale (panics otherwise).
- **`CiphertextNoRelin`**: like `Ciphertext` but with three components `c0, c1, c2`
  (the output of a ciphertext-ciphertext multiplication before relinearization), plus an
  `implicit_scale`.

### Removed

- **`equalize_implicit_scale`** (the rational-reconstruction-based scale alignment) is
  gone, replaced by the simpler `ImplicitScalePolicy`. (Note: the commented-out
  `noise_estimator.rs` still references it; that will be updated when it is re-included.)

### Addition variants

- Added **`hom_add_plain_scalar`** (scalar from `Z/tZ`), so all three plaintext-operand
  flavours now have add **and** mul variants: `hom_add_plain_scalar` / `hom_add_plain` /
  `hom_add_plain_encoded` and `hom_mul_plain_scalar` / `hom_mul_plain` / `hom_mul_plain_encoded`.

### Inner-product variants

- Added **`hom_inner_product_plain_scalar`**, **`hom_inner_product_plain`**,
  **`hom_inner_product_encoded`**, each computing `sum_i m_i * ct_i` and taking an
  `ImplicitScalePolicy`. Empty input yields `transparent_zero`.

### Split of multiplication

- **`hom_mul_norelin`** / **`hom_square_norelin`** produce a `CiphertextNoRelin` (the
  `two_by_two_convolution` step; no relinearization key needed).
- **`relinearize`** turns a `CiphertextNoRelin` back into a `Ciphertext` (the key-switch
  step).
- **`hom_mul`** / **`hom_square`** are kept but now only delegate:
  `relinearize(hom_mul_norelin(..))`.

### `_norelin` operations

Added `CiphertextNoRelin` variants with concise default implementations:
`hom_mul_plain_scalar_norelin`, `hom_mul_plain_norelin`, `hom_mul_plain_encoded_norelin`,
`hom_add_plain_scalar_norelin`, `hom_add_plain_norelin`, `hom_add_plain_encoded_norelin`,
`hom_inner_product_plain_scalar_norelin`, `hom_inner_product_plain_norelin`,
`hom_inner_product_encoded_norelin`, and `mod_switch_norelin`.

### `hom_add` / `hom_sub`

Both now take an `ImplicitScalePolicy` parameter.

## Additional helper methods (beyond the explicit list)

To give the `_norelin` family concise, non-duplicated default implementations, I added a
few companion methods that mirror existing `Ciphertext` helpers:

- `clone_ct_norelin`, `transparent_zero_norelin` — mirror `clone_ct` / `transparent_zero`;
  needed by the `_norelin` inner products.
- `merge_implicit_scale_norelin` — mirrors `merge_implicit_scale`.
- `hom_add_norelin` — mirrors `hom_add` (with `ImplicitScalePolicy`); used by the
  `_norelin` inner products so they fold exactly like the relinearized versions.

If you'd rather keep the trait surface strictly to the listed functions, I can fold these
into module-private free functions instead.

## Design notes / decisions for review

- **Inner-product signatures.** All inner products take
  `I: IntoIterator<Item = (L, R)>` where `L: Borrow<operand>` and
  `R: Borrow<Ciphertext>` / `Borrow<CiphertextNoRelin>`, cloning the ciphertext operands
  internally. This mirrors `AsBFVPlaintext::hom_inner_prod` and fits how the evaluator will
  pass circuit wires (which may be reused elsewhere). Happy to switch to consuming owned
  ciphertexts if you prefer.
- **`relinearize` / `hom_mul_norelin` signatures.** `hom_mul_norelin` takes no special
  modulus and no relin key; `relinearize` takes `C_special` and the relin key. This matches
  the lazy-relinearization design used later in Step 4.
- No `fma` variants were added (as instructed).

# Review

Generally looks good. I praise you for the definition of `inner_product` using `Borrow`, that's very clever. But fix the following points:
 - the `inner_product` variants should use the `inner_product` operation in the ciphertext ring, whenever appropriate. More concretely, `inner_product_plain_encoded` should use `<CiphertextRing as ComputeInnerProduct>::inner_product` (from feanor-math), which can be faster than the current loop. Furthermore, `inner_product_plain` should encode the operands (it is ok to store the encoded ones in a new, temporary vector) and then use `inner_product_plain_encoded`. Finally, `hom_inner_product_plain_scalar` doesn't (cannot) call an inner product function of the ring, but should instead use `Inclusion::fma_map()` from feanor-math.
 Make sure to still respect the implicitscalepolicy.
 - `hom_mul_plain_scalar` should only lift the scalar once (irrelevant for performance, but cleaner)

# Review response

Both points addressed (relinearized and `_norelin` inner products, for consistency):

- **`hom_inner_product_encoded`** now brings all summands to a common implicit scale
  (per the `ImplicitScalePolicy`: `Merge` rescales each via `merge_implicit_scale`,
  `AssertEqual` checks equality), collects the ciphertext components, and computes each
  component with `<CiphertextRing as ComputeInnerProduct>::inner_product_ref_fst` (so the
  accelerated ring inner products are used where available; the blanket impl in feanor-math
  covers the rest).
- **`hom_inner_product_plain`** now encodes the operands into a temporary vector and
  delegates to `hom_inner_product_encoded`.
- **`hom_inner_product_plain_scalar`** cannot use a ring inner product; it folds the
  implicit scale into the (lifted) scalar and accumulates the components with
  `Inclusion::fma_map`, avoiding intermediate allocations. The `ImplicitScalePolicy` is
  respected in all cases.
- The same three changes were applied to the `_norelin` variants (three components).
- **`hom_mul_plain_scalar`** now lifts the scalar only once (and uses `mul_assign_ref_map`).

Added a test `test_pow2_bgv_hom_inner_product` covering the scalar/plaintext/encoded
variants, both `AssertEqual` and `Merge` policies, and the `_norelin` path.
