
Your task is to refactor the circuit evaluation framework in fheanor.
For now, we restrict to BGV: If refactoring is successful, a similar model will then be applied to BFV and CLPX.
Concretely, the goal is to address the following shortcomings:
 - Inconsistencies in the API, in particular regarding fma and inner product, and operand types (integers, plaintexts, encoded plaintexts)
 - Unconditional fusing of HomMul + Relin leads to inferior performance in cases where ciphertext-ciphertext multiplication results are summed up, and relinearization could, in theory, only be performed on the sum

Follow the following steps. After every step, write a markdown report `REPORT_<number>.md` in the directory root. The user will either append a `# Review` to that report, in which case you should fix the feedback before continuing, or `# Review approved`, in which case you continue with the next task in the list. Apart from commented-out modules, the code should compile after every step, and the tests should pass.
The tasks are:

1. First, refactor `src/bgv/mod.rs` as outlined below. Note that the module declarations for the primary dependencies `src/bgv/noise_estimator.rs`, `src/bgv/modswitch.rs` and `src/bgv/bootstrap.rs` are currently commented out, so you can test the refactored version without immediate changing those.

2. Then create `src/bgv/eval.rs` as outlined below.

3. Make the small changes to `CircuitEvaluator`

4. Re-include `src/bgv/modswitch.rs` and refactor it as outlined below.

5. Re-include `src/bgv/bootstrap.rs` and adjust it to the changed codebase.

# Current Design

Since we focus on BGV, the relevant files are
 - `src/bgv/mod.rs` containing the primitive BGV implementation (trait `BGVInstantiation` and implementors)
 - `src/bgv/noise_estimator.rs` containing the BGV noise estimation framework and implementation (trait `BGVNoiseEstimator` and implementors)
 - `src/bgv/modswitch.rs` containing automated modulus-switching for BGV (trait `AsBGVPlaintext` and `BGVModswitchStrategy`, and primary implementor `DefaultModswitchStrategy`)
 - `src/circuit/mod.rs` containing the implementation of evaluatable circuits (struct `PlaintextCircuit`)

`BGVInstantiation` implements primitive BGV operations like plaintext-ciphertext multiplication/addition and ciphertext-ciphertext multiplication/addition. `AsBGVPlaintext` is a bridge that translates plaintext-ciphertext operations for various rings that naturally "contain" BGV plaintexts (usually via a homomorphism ring -> scheme plaintext ring) to the primitive operations provided by `BGVInstantiation`. `BGVModswitchStrategy` and `DefaultModswitchStrategy` build on that to implement circuit evaluation, with automated modulus-switching.

# Changes and New Design

## Primitive BGV

The primary architecture should remain the same. In particular, `BGVInstantiation` realizes primitive BGV operations, and `AsBGVPlaintext` allows treating a wider set of plaintexts as plaintexts, by translating them down to `BGVInstantiation` primitives.

However, the design of `BGVInstantiation` should be more streamlined, and allow for more optimizations by users.
Concretely
 - Keep the functions `hom_mul_plain_scalar` (taking a ciphertext and an element of `Z/tZ`, where `t` is plaintext modulus), `hom_mul_plain` (taking a ciphertext and a plaintext from `R/tR`) and `encode_plain` + `hom_mul_plain_encoded`. These are the right way to model plaintext-ciphertext ring multiplications in an efficient way.
 - Ensure that addition variants for each of them exist, i.e. `hom_add_plain_scalar`, `hom_add_plain` and `hom_add_plain_encoded`
 - Add an inner-product variant for each of them, i.e. `hom_inner_product_plain_scalar`, `hom_inner_product_plain`, `hom_inner_product_encoded`. 
 - Simplify the `implicit_scale` handling. Create an enum `ImplicitScalePolicy` with two options `Merge` and `AssertEqual`. All operations that perform additions of ciphertexts (i.e. `hom_add` and the above `inner_product_plain_*`) take such a policy as argument: If `Merge`, each ciphertext is multiplied with its implicit scale first, resulting in the result implicit scale `1`. If `AssertEqual`, assert that all summands have the same implicit scale, and panic otherwise. For now, get rid of `equalize_implicit_scale` (although an option for this might later be added to `ImplicitScalePolicy)
 - For now, to keep it simple, do not add any fused-multiply-add `fma` variants
 - Introduce an additional type `CiphertextNoRelin`, which is like `Ciphertext` but has three components `c0, c1, c2` (i.e. the output of a ciphertext-ciphertext multiplication without relinearization)
 - Add functions `hom_mul_plain_scalar_norelin`, `hom_mul_plain_norelin`, `hom_mul_plain_encoded_norelin`, `hom_add_plain_scalar_norelin`, `hom_add_plain_norelin`, `hom_add_plain_encoded_norelin`, `hom_inner_product_plain_scalar_norelin`, `hom_inner_product_plain_norelin`, `hom_inner_product_encoded_norelin` and `mod_switch_norelin`.
 It should be possible to give all these functions a sensible, performant and concise default implementation, so hopefully `BGVInstantiation` will not be blown up terribly by this.
 - Split `hom_mul` and `hom_square` into `hom_mul_norelin`/`hom_square_norelin` (which produce the above `CiphertextNoRelin`) and `relinearize`. Keep `hom_mul` and `hom_square`, but only delegate there, and have the actual logic in  `hom_mul_norelin`, `hom_square_norelin` and `relinearize`.

## Noise Estimation

Create a new struct `CiphertextDescriptor`, which stores a `BGVNoiseEstimator::CiphertextDescriptor`, an implicit scale value, and the `SecretKeyDistribution` of the secret key that the ciphertext was encrypted with respect to.

Ensure that the interface for `BGVNoiseEstimator` matches exactly the interface for `BGVInstantiation`, except that ciphertexts parameters/return values are replaced with `CiphertextDescriptor`, key-switch keys are replaced with `KeySwitchKeyDescriptor`, secret key is replaced with `SecretKeyDistribution`. Another difference should, of course, be that `BGVNoiseEstimator` doesn't have the equivalent of functions that don't do anything noise-related, in particular functions like `create_rns_base` or `create_plaintext_ring`.

## Evaluation

Generally, you can refer to `src/bfv/eval.rs` for this task, but note that the below description differs from the design there in some aspects

Create a new file `src/bgv/eval.rs`, which now contains `AsBGVPlaintext`.
Change the trait to have the following functions:
 - `hom_add_to`, `hom_mul_to`, `hom_inner_product` that perform plaintext-ciphertext addition/multiplication/inner product; remove the existing function `hom_inner_product_ref`
 - `hom_add_to_noise`, `hom_mul_to_noise`, `hom_inner_product_noise` that are the `BGVNoiseEstimator` equivalent of the before (they should take the `BGVNoiseEstimator` as parameter)

All of these functions should have parameters that can be either a `Ciphertext` or a `CiphertextNoRelin` (create an enum for this).

Create a new ring `EncodedBGVPlaintextRingBase` that stores both a BGV plaintext ring and a ciphertext ring, and its elements are a BGV plaintext together with the "encoded" plaintext (i.e. the result of `BGVInstantiation::encode_plain`), and a `<<CiphertextRing<Params> as RingStore>::Type as PreparedMultiplicationRing>::PreparedMultiplicant` for this value. In other words, this ring should be the BGV plaitnext ring again, but with elements having additional data to speed up plaintext-ciphertext multiplications as much as possible.

Ensure that exactly the following implementations for `AsBGVPlaintext` exist:
 - `impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for Params::PlaintextRing`
 - `impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for BigIntRingBase`
 - `impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for EncodedBGVPlaintextRingBase<Params>`

## `CircuitEvaluator` trait

This is a small change to the circuit evaluator in `src/circuit/evaluator.rs`. Add an additional parameter to `mul` and `square` that specifies the fan-out of the gate, i.e. the number of further gates or outputs that use the result of the current gate (i.e. their linear combinations have a non-zero coefficient for that output). At all implementations of `CircuitEvaluator`s, just add this parameter as an unused parameter `_: usize`. In `PlaintextCircuit::evaluate_generic()`, just make a quick linear-time forward search to compute this value for every gate.

## Modulus-switching

Change the struct `ModulusAwareCiphertext` to store the ciphertext (which now can either be a `Ciphertext` or a `CiphertextNoRelin`), the `CiphertextDescriptor` struct corresponding to the noise estimator, and the `dropped_rns_factor_indices` that it already contains.

Keep the trait `BGVModswitchStrategy` as it is.

Adjust the implementation of `DefaultModswitchStrategy` to work with the new version of the BGV primitives and evaluation code. Extend the current logic to use lazy relinearization. In other words:
 - if the fan-out of a multiplication or squaring gate is 1, do lazy relinearization: Don't relinearize now, but return a `ModulusAwareCiphertext` that stores a `CiphertextNoRelin`
 - if the fan-out of a multiplication or squaring gate is > 1, relinearize eagerly, i.e. now
 - when computing inner products, leave un-relinearized ciphertexts un-relinearized. In other words, if any of the input summands is un-relinearized, the output should also be un-relinearized
 - for multiplications, squarings and galois automorphisms, if the input is un-relinearized, relinearize it first before continuing with the operation.

## Bootstrapping

Don't change anything here, except what is necessary to make bootstrapping work with the previous changes. In the optimal case, the changes here should be minimal.