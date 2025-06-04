
mod serialization;

///
/// Contains [`structure::HypercubeStructure`] representing hypercube structures, i.e. 
/// mappings of a set of representatives of `(Z/mZ)* / <p>` to the entries of a hypercube.  
/// 
pub mod structure;
///
/// Contains [`interpolate::FastPolyInterpolation`] for fast polynomial interpolation on
/// a fixed set of points.
/// 
pub mod interpolate;
///
/// Contains [`isomorphism::HypercubeIsomorphism`] for the isomorphism of `R_t` to a direct
/// product of many slots, indexed by the codomain of a [`structure::HypercubeStructure`].
/// 
pub mod isomorphism;