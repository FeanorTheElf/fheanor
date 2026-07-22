use std::mem::MaybeUninit;

use feanor_math::ring::*;
use feanor_math::rings::zn::{ZnRing, ZnRingStore};
use feanor_math::matrix::*;

mod matmul_kernel;
///
/// Contains the implementation of the rounded rescaling operations used
/// during BFV multiplication and modulus-switching.
/// 
pub mod bfv_rescale;
///
/// Contains the implementation of the rounded rescaling operations used
/// during BGV modulus-switching.
/// 
pub mod bgv_rescale;
///
/// Contains a convenience-wrapper around the basic RNS conversion from
/// [`bconv`], which preserves some of the RNS factors without recomputing
/// them. 
/// 
pub mod shared_lift;
///
/// Contains the main implementation of the RNS base conversion.
/// 
pub mod bconv;

///
/// Trait for any map `Zq -> Zq'` for (usually composite) `q, q'`.
/// 
/// In the normal case that `q, q'` are composite, the input and output
/// are given/expected to be returned in RNS resp. CRT form, i.e. `x in Zq`
/// is represented by `(x mod p)_{p | q}`.
/// 
/// # Standard use case
/// 
/// The main use case for this are cases where `q, q'` are huge (do not fit into
/// basic integers) and the maps can be efficiently computed without computing the 
/// representatives modulo `q` resp. `q'`. This is in particular possible for
/// "approximate versions" of rounding or rescaling, that are important during
/// RLWE-based HE.
/// 
/// When we then have an object representing such a map, we can pass it to
/// [`perform_rns_op()`] or similar functions. This way, we can perform some
/// operations on double-RNS-represented ring element very easily and efficiently
/// (without arbitrary-precision arithmetic).
/// 
/// [`perform_rns_op()`]: crate::ciphertext_ring::perform_rns_op()
/// 
pub trait RNSOperation {

    type Ring: ZnRingStore<Type = Self::RingType>;
    
    type RingType: ?Sized + ZnRing;

    fn input_rings<'a>(&'a self) -> &'a [Self::Ring];

    fn output_rings<'a>(&'a self) -> &'a [Self::Ring];

    ///
    /// Applies the RNS operation to each column of the given matrix, and writes the results to the columns
    /// of `output`. The entries of the `i`-th row are considered to be elements of `self.input_rings().at(i)`
    /// resp. `self.output_rings().at(i)`.
    ///
    fn apply<'a, V1, V2>(&self, input: Submatrix<V1, El<Self::Ring>>, output: SubmatrixMut<'a, V2, MaybeUninit<El<Self::Ring>>>) -> SubmatrixMut<'a, V2, El<Self::Ring>>
        where V1: Sync + AsPointerToSlice<El<Self::Ring>>,
            V2: Sync + AsPointerToSlice<El<Self::Ring>> + AsPointerToSlice<MaybeUninit<El<Self::Ring>>>;
}

pub(crate) type UsedBaseConversion = bconv::RNSBaseConversion;
