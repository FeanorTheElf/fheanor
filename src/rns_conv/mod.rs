use feanor_math::ring::*;
use feanor_math::rings::zn::{ZnRing, ZnRingStore};
use feanor_math::matrix::*;

///
/// Contains the basic "lift-and-reduce" RNS base conversion, which
/// can be used to change the RNS modulus without "changing" the representative
/// of elements.
/// 
pub mod lift;

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
/// [`lift`], which preserves some of the RNS factors without recomputing
/// them. 
/// 
pub mod shared_lift;
///
/// Contains another implementation of the basic RNS base conversion
/// (as in [`lift`]), which explicitly considers the conversion as matrix
/// multiplication.
/// 
pub mod matrix_lift;

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
    fn apply<V1, V2>(&self, input: Submatrix<V1, El<Self::Ring>>, output: SubmatrixMut<V2, El<Self::Ring>>)
        where V1: AsPointerToSlice<El<Self::Ring>>,
            V2: AsPointerToSlice<El<Self::Ring>>;
}

pub(crate) type UsedBaseConversion<A> = matrix_lift::AlmostExactMatrixBaseConversion<A>;

///
/// Returns `(data_sorted, perm)` such that `data_sorted` is an (ascending)
/// unstable sorting of `data`, and `data[i] = data_sorted[perm[i]]`.
/// 
fn sort_unstable_permutation<T, F>(data: Vec<T>, mut sort_by: F) -> (Vec<T>, Vec<usize>)
    where F: FnMut(&T, &T) -> std::cmp::Ordering
{
    let len = data.len();
    let mut enumerated = data.into_iter().enumerate().collect::<Vec<_>>();
    enumerated.sort_unstable_by(|(_, x), (_, y)| sort_by(x, y));
    let mut perm = (0..len).map(|_| 0).collect::<Vec<_>>();
    let mut data_sorted = Vec::with_capacity(len);
    for (j, (i, x)) in enumerated.into_iter().enumerate() {
        data_sorted.push(x);
        perm[i] = j;
    }
    return (data_sorted, perm);
}