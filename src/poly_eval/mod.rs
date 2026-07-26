/// Functions to find short addition chains of low multiplicative depth.
pub mod addition_chains;
/// Contains [`digit_extract::DigitExtract`] that bundles all circuits required
/// for the digit extraction step during bootstrapping. Also contains functions to
/// compute Halevi and Shoup digit extraction polynomials, Chen and Han digit retain
/// polynomials, and MHWW digit retain polynomials.
pub mod digit_extract;
/// Contains Galois-based algorithms for polynomial evaluation, along the lines of
/// <https://ia.cr/2023/1304>.
pub mod galois_based;
/// Contains a heuristic adaption of the Paterson-Stockmeyer to finite rings;
/// this is used internally by [`to_circuit::poly_to_circuit()`].
pub mod paterson_stockmeyer;
pub mod special;
/// Contains [`to_circuit::poly_to_circuit()`] to convert multiple polynomials into
/// a [`PlaintextCircuit`] that evaluates them.
///
/// [`PlaintextCircuit`]: crate::circuit::PlaintextCircuit
pub mod to_circuit;
