use std::alloc::Global;

use feanor_math::assert_el_eq;
use feanor_math::homomorphism::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::*;
use feanor_math::matrix::*;
use tracing::instrument;

use crate::NiceZn;

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

    fn input_rings<'a>(&'a self) -> &'a [zn_64::Zn];

    fn output_rings<'a>(&'a self) -> &'a [zn_64::Zn];

    ///
    /// Applies the RNS operation to each column of the given matrix, and writes the results to the columns
    /// of `output`. The entries of the `i`-th row are considered to be elements of `self.input_rings().at(i)`
    /// resp. `self.output_rings().at(i)`.
    ///
    fn apply_base<V1, V2>(&self, input: Submatrix<V1, El<zn_64::Zn>>, output: SubmatrixMut<V2, El<zn_64::Zn>>)
        where V1: AsPointerToSlice<El<zn_64::Zn>>,
            V2: AsPointerToSlice<El<zn_64::Zn>>;

    ///
    /// Like [`RNSOperation::apply_base()`], but additionally converts inputs and outputs to and from the given
    /// ring implementations.
    /// 
    /// This requires that `in_rings[i]` is the same ring (in the mathematical sense, not implementation-wise)
    /// as `self.input_rings()[i]`, and similarly for the output rings.
    /// 
    /// Implementors may wish to override this function, if they can merge the conversions into the actual operations.
    /// 
    #[instrument(skip_all)]
    fn apply<IIn, IOut, ZnIn, ZnOut, V1, V2>(&self, in_rings: IIn, out_rings: IOut, input: Submatrix<V1, El<ZnIn>>, mut output: SubmatrixMut<V2, El<ZnOut>>)
        where V1: AsPointerToSlice<El<ZnIn>>,
            V2: AsPointerToSlice<El<ZnOut>>,
            ZnIn: RingStore,
            ZnIn::Type: NiceZn,
            ZnOut: RingStore,
            ZnOut::Type: NiceZn,
            IIn: ExactSizeIterator<Item = ZnIn>,
            IOut: ExactSizeIterator<Item = ZnOut>
    {
        assert_eq!(in_rings.len(), self.input_rings().len());
        assert_eq!(out_rings.len(), self.output_rings().len());
        let mut input_converted = OwnedMatrix::zero(input.row_count(), input.col_count(), &self.input_rings()[0]);
        for (i, in_ring) in in_rings.enumerate() {
            let int_iso = self.input_rings()[i].integer_ring().can_hom(in_ring.integer_ring()).unwrap();
            assert_eq!(self.input_rings()[i].modulus(), &int_iso.map_ref(in_ring.modulus()));
            for j in 0..input.col_count() {
                *input_converted.at_mut(i, j) = self.input_rings()[i].get_ring().from_int_promise_reduced(int_iso.map(in_ring.smallest_positive_lift(in_ring.clone_el(input.at(i, j)))));
            }
        }
        let mut output_converted = OwnedMatrix::zero(output.row_count(), output.col_count(), &self.output_rings()[0]);
        self.apply_base(input_converted.data(), output_converted.data_mut());
        for (i, out_ring) in out_rings.enumerate() {
            let int_iso = out_ring.integer_ring().can_hom(self.output_rings()[i].integer_ring()).unwrap();
            assert_el_eq!(out_ring.integer_ring(), out_ring.modulus(), int_iso.map(*self.output_rings()[i].modulus()));
            for j in 0..output.col_count() {
                *output.at_mut(i, j) = out_ring.get_ring().from_int_promise_reduced(int_iso.map(self.output_rings()[i].smallest_positive_lift(*output_converted.at(i, j))));
            }
        }
    }
}

pub(crate) type UsedBaseConversion<A = Global> = matrix_lift::RNSMatrixBaseConversion<A>;

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