# Report — Step 3: Fan-out parameter for `CircuitEvaluator`

This report covers Step 3: adding a fan-out parameter to the `mul` and `square`
methods of the `CircuitEvaluator` trait (`src/circuit/evaluator.rs`), updating all
implementors, and computing the value in `PlaintextCircuit::evaluate_generic()` via
a linear-time forward sweep.

As before, `src/bgv/modswitch.rs` and `src/bgv/bootstrap.rs` remain commented out
(Steps 4/5). The fan-out value computed here is what the `DefaultModswitchStrategy`
will consume in Step 4 to decide between lazy and eager relinearization.

## Status

- `cargo build --lib --tests` compiles. The only warnings are the two pre-existing
  ones in `src/bfv/mod.rs` (unused `PlaintextCircuit` / `group` imports, from the
  Step-1 commenting-out of `bfv::bootstrap`); none come from this step.
- `cargo test --lib circuit` passes (results below).

## Trait change (`src/circuit/evaluator.rs`)

`CircuitEvaluator::mul` and `::square` gained a trailing `fan_out: usize` parameter:

```rust
fn mul(&mut self, lhs: T, rhs: T, fan_out: usize) -> T;
fn square(&mut self, val: T, fan_out: usize) -> T;
```

`fan_out` is documented as "the number of later gates or outputs that use the result
of this gate (i.e. whose linear combinations have a non-zero coefficient for this
gate's output)". Evaluators that don't care may ignore it.

## Implementors updated

All existing implementations were updated; only the BGV modswitch evaluator (Step 4,
still commented out) will actually *use* the value:

- `HomEvaluator` / `HomEvaluatorGal` (`src/circuit/evaluator.rs`): `mul`/`square` take
  `_: usize` (the gal evaluator forwards it to the base, which ignores it).
- `BFVEvaluator` (`src/bfv/eval.rs`): `_: usize`.
- `CLPXEvaluator` (`src/clpx/eval.rs`): `_: usize`.
- `ToIREvaluator` (`src/circuit/ir.rs`): `mul` takes `_: usize`; `square` forwards its
  `fan_out` to `self.mul(val, val, fan_out)`.
- `MulDepthEvaluator` (`src/lin_transform/matmul.rs`, test-only): `_: usize` (both
  bodies are `unreachable!()`).

## Fan-out computation (`src/circuit/mod.rs`)

Added a private method `PlaintextCircuit::compute_gate_output_fan_out(&self) -> Vec<usize>`,
indexed by the position of a value in the sequence of gate outputs (the same indexing
`evaluate_generic` uses for its `current` buffer). `evaluate_generic` calls it once up
front and passes `fan_out[result_index]` into `mul`/`square`, where `result_index` is
`current.len()` immediately before the gate's output is pushed.

The computation is a single linear-time forward sweep:

- A `LinearCombination`'s factor at position `pos` refers to a circuit input when
  `pos < input_count` and to gate-output value `pos - input_count` otherwise (matching
  the `inputs.chain(current)` ordering used in `LinearCombination::evaluate_generic`).
- Each gate (via its input linear combinations) and each output transform is treated as
  one "consumer". For every distinct gate-output value a consumer references with a
  non-zero coefficient, that value's fan-out is incremented.
- A `last_consumer` stamp array ensures a consumer is counted **at most once per value**,
  even if it references the value in several linear combinations (e.g. both operands of
  a `Mul` gate) or multiple times — matching the "number of gates or outputs" wording
  rather than a raw reference count.

### Decision for review

- **Counting per consumer, not per reference.** A `Mul` gate whose `lhs` and `rhs` both
  reference the same value counts as fan-out 1, since it is a single consuming gate. This
  matches the literal wording ("the number of further gates or outputs"). For the lazy-vs-
  eager relinearization decision in Step 4 this is also the conservative-correct choice
  (only fan-out exactly 1 triggers lazy relinearization). Flag if you'd prefer a raw
  reference count instead.
