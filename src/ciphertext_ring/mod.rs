use std::alloc::Allocator;

use feanor_math::integer::BigIntRing;
use feanor_math::matrix::*;
use feanor_math::ring::*;
use feanor_math::rings::extension::{FreeAlgebra, FreeAlgebraStore};
use feanor_math::rings::zn::zn_64::{ZnEl, Zn, ZnBase};
use feanor_math::rings::zn::zn_rns;
use feanor_math::seq::{VectorView, VectorFn};
use tracing::instrument;

use crate::number_ring::quotient::{NumberRingQuotient, NumberRingQuotientEl};
use crate::number_ring::HECyclotomicNumberRing;
use crate::rnsconv::RNSOperation;

///
/// Code for fast polynomial division by a cyclotomic polynomial.
/// Used within [`single_rns_ring`].
/// 
pub mod poly_remainder;

///
/// Contains utilities to serialize/deserialize elements of rings that are based on RNS bases.
/// 
pub mod serialization;

///
/// Contains [`double_rns_ring::DoubleRNSRing`], an implementation of the ring `R/qR` for suitable `q`.
///  
pub mod double_rns_ring;

///
/// Contains [`single_rns_ring::SingleRNSRing`], an implementation of the ring `R/qR` for suitable `q`.
///  
pub mod single_rns_ring;

///
/// Contains [`double_rns_managed::ManagedDoubleRNSRing`], an implementation of the ring `R/qR` for suitable `q`
/// that is based on [`double_rns_ring::DoubleRNSRing`].
///  
pub mod double_rns_managed;

///
/// A ring whose elements have a "prepared multiplication"-representation, such that elements
/// in this representation can be multiplied faster than in their standard representation.
/// 
pub trait PreparedMultiplicationRing: RingBase {

    type PreparedMultiplicant;

    ///
    /// Converts an element of the ring into a `PreparedMultiplicant`, which can then be used
    /// to compute multiplications by this element faster.
    /// 
    fn prepare_multiplicant(&self, x: &Self::Element) -> Self::PreparedMultiplicant;

    ///
    /// Computes the product of two elements that have previously been "prepared" via
    /// [`PreparedMultiplicationRing::prepare_multiplicant()`].
    /// 
    fn mul_prepared(&self, lhs: &Self::PreparedMultiplicant, rhs: &Self::PreparedMultiplicant) -> Self::Element;

    ///
    /// Computes the inner product of two vectors over this ring, whose elements have previously
    /// been "prepared" via [`PreparedMultiplicationRing::prepare_multiplicant()`].
    /// 
    fn inner_product_prepared<'a, I>(&self, parts: I) -> Self::Element
        where I: IntoIterator<Item = (&'a Self::PreparedMultiplicant, &'a Self::PreparedMultiplicant)>,
            Self: 'a
    {
        parts.into_iter().fold(self.zero(), |current, (lhs, rhs)| self.add(current, self.mul_prepared(lhs, rhs)))
    }
}

///
/// Trait for rings `R/qR` with a number ring `R` and modulus `q = p1 ... pr` represented as 
/// RNS basis, which provide all necessary operations for use as ciphertext ring in BFV/BGV-style
/// HE schemes.
/// 
pub trait BGFVCiphertextRing: PreparedMultiplicationRing + FreeAlgebra + RingExtension<BaseRing = zn_rns::Zn<Zn, BigIntRing>> {

    type NumberRing: HECyclotomicNumberRing;

    fn number_ring(&self) -> &Self::NumberRing;

    ///
    /// Computes the ring `R_q'`, where `q'` is the product of all RNS factors of `q`,
    /// except those whose indices are mentioned in `drop_rns_factors`.
    /// 
    fn drop_rns_factor(&self, drop_rns_factors: &[usize]) -> Self;

    ///
    /// Reduces an element of `from` modulo `q`, where `q` must divide the modulus of `from`.
    /// 
    /// More concretely, the RNS factors of `q` must be exactly the RNS factors of `from.rns_base()`,
    /// except for the RNS factors whose indices occur in `dropped_rns_factors`.
    /// 
    fn drop_rns_factor_element(&self, from: &Self, dropped_rns_factors: &[usize], value: Self::Element) -> Self::Element;

    ///
    /// Reduces a `PreparedMultiplicant` of `from` modulo `q`, where `q` must divide the modulus of `from`.
    /// 
    /// More concretely, the RNS factors of `q` must be exactly the RNS factors of `from.rns_base()`,
    /// except for the RNS factors whose indices occur in `dropped_rns_factors`.
    /// 
    fn drop_rns_factor_prepared(&self, from: &Self, dropped_rns_factors: &[usize], value: Self::PreparedMultiplicant) -> Self::PreparedMultiplicant;

    ///
    /// Returns the length of the small generating set used for [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`]
    /// and [`BGFVCiphertextRing::from_representation_wrt_small_generating_set()`].
    /// 
    fn small_generating_set_len(&self) -> usize;

    ///
    /// Returns a view on the underlying representation of `x`. 
    /// 
    /// This is the counterpart of [`BGFVCiphertextRing::from_representation_wrt_small_generating_set()`].
    /// 
    /// More concretely, for some `Zq`-linear generating set `{ a_i | i }` consisting
    /// of ring elements of small canonical norm, each column of the returned matrix contains
    /// the RNS representation of some `x_i`, satisfying `x = sum_i a_i x_i`. The actual choice
    /// of the `a_i` is left to the ring implementation, and may change in future releases.
    /// The order of the rows (corresponding to the RNS factors of `Zq`) is the same as the
    /// order of the RNS factors in `self.base_ring()`.
    /// 
    /// This function is a compromise between encapsulating the storage of ring elements
    /// and exposing it (which is sometimes necessary for performance). 
    /// Hence, it is recommended to instead use [`FreeAlgebra::wrt_canonical_basis()`] and
    /// [`FreeAlgebra::from_canonical_basis()`], whose result is uniquely defined. However, note
    /// that these may incur costs for internal representation conversion, which may not always
    /// be acceptable.
    /// 
    /// Concrete representations:
    ///  - [`single_rns_ring::SingleRNSRing`] will currently return the coefficients of a polynomial
    ///    of degree `< m` (not necessarily `< phi(m)`) that gives the element when evaluated at `𝝵`
    ///  - [`double_rns_managed::ManagedDoubleRNSRing`] will currently return the coefficients w.r.t.
    ///    the powerful basis representation
    /// 
    /// Currently, this function is only used for gadget products and modulus-switching. In these
    /// cases, it is indeed ok if the representation is not unique, as long as it is w.r.t. a small
    /// generating set.
    /// 
    fn as_representation_wrt_small_generating_set<V>(&self, x: &Self::Element, output: SubmatrixMut<V, ZnEl>)
        where V: AsPointerToSlice<ZnEl>;

    ///
    /// Computes a subset of the rows of the representation that would be returned by
    /// [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`]. Since not all rows
    /// have to be computed, this may be faster than `as_representation_wrt_small_generating_set()`.
    /// 
    /// For details, [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`].
    /// 
    fn partial_representation_wrt_small_generating_set<V>(&self, x: &Self::Element, row_indices: &[usize], output: SubmatrixMut<V, ZnEl>)
        where V: AsPointerToSlice<ZnEl>;

    ///
    /// Creates a ring element from its underlying representation.
    /// 
    /// This is the counterpart of [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`],
    /// which contains a more detailed documentation.
    /// 
    /// This function is a compromise between encapsulating the storage of ring elements
    /// and exposing it (which is sometimes necessary for performance). 
    /// Hence, it is recommended to instead use [`FreeAlgebra::wrt_canonical_basis()`] and
    /// [`FreeAlgebra::from_canonical_basis()`], whose result is uniquely defined. However, note
    /// that these may incur costs for internal representation conversion, which may not always
    /// be acceptable.
    /// 
    fn from_representation_wrt_small_generating_set<V>(&self, data: Submatrix<V, ZnEl>) -> Self::Element
        where V: AsPointerToSlice<ZnEl>;

    ///
    /// Computes `[lhs[0] * rhs[0], lhs[0] * rhs[1] + lhs[1] * rhs[0], lhs[1] * rhs[1]]`, but might be
    /// faster than the naive way of evaluating this.
    /// 
    #[instrument(skip_all)]
    fn two_by_two_convolution(&self, lhs: [&Self::Element; 2], rhs: [&Self::Element; 2]) -> [Self::Element; 3] {
        let mut lhs_it = lhs.into_iter();
        let mut rhs_it = rhs.into_iter();
        let lhs: [_; 2] = std::array::from_fn(|_| self.prepare_multiplicant(lhs_it.next().unwrap()));
        let rhs: [_; 2] = std::array::from_fn(|_| self.prepare_multiplicant(rhs_it.next().unwrap()));
        [
            self.mul_prepared(&lhs[0], &rhs[0]),
            self.inner_product_prepared([(&lhs[0], &rhs[1]), (&lhs[1], &rhs[0])]),
            self.mul_prepared(&lhs[1], &rhs[1])
        ]
    }
}

///
/// Maps an element from a ring `from` to a quotient of the same number ring `to` (but with
/// a different modulus). This is done by applying the given RNS conversion to each coefficient
/// in the representation given by [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`].
/// 
/// Note that [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`] might not behave
/// exactly as expected, due to the need for a very performant implementation. See its doc for details.
/// 
#[instrument(skip_all)]
pub fn perform_rns_op<R, Op>(to: &R, from: &R, el: &R::Element, op: &Op) -> R::Element
    where R: BGFVCiphertextRing,
        Op: RNSOperation<RingType = ZnBase>
{
    assert!(from.number_ring() == to.number_ring());
    assert_eq!(op.input_rings().len(), from.base_ring().len());
    assert_eq!(op.output_rings().len(), to.base_ring().len());
    assert!(op.input_rings().iter().zip(from.base_ring().as_iter()).all(|(l, r)| l.get_ring() == r.get_ring()));
    assert!(op.output_rings().iter().zip(to.base_ring().as_iter()).all(|(l, r)| l.get_ring() == r.get_ring()));

    let mut el_repr = OwnedMatrix::zero(from.base_ring().len(), from.small_generating_set_len(), from.base_ring().at(0));
    from.as_representation_wrt_small_generating_set(el, el_repr.data_mut());
    let mut res_repr = Vec::with_capacity(el_repr.col_count() * to.base_ring().len());
    res_repr.resize(el_repr.col_count() * to.base_ring().len(), to.base_ring().at(0).zero());
    let mut res_repr = SubmatrixMut::from_1d(&mut res_repr, to.base_ring().len(), el_repr.col_count());
    op.apply(el_repr.data(), res_repr.reborrow());
    return to.from_representation_wrt_small_generating_set(res_repr.as_const());
}

#[instrument(skip_all)]
pub fn perform_rns_op_to_plaintext_ring<R, Op, A>(to: &NumberRingQuotient<R::NumberRing, Zn, A>, from: &R, el: &R::Element, op: &Op) -> NumberRingQuotientEl<R::NumberRing, Zn, A>
    where R: BGFVCiphertextRing,
        Op: RNSOperation<RingType = ZnBase>,
        A: Allocator + Clone
{
    assert!(from.number_ring() == to.get_ring().number_ring());
    assert_eq!(op.input_rings().len(), from.base_ring().len());
    assert_eq!(op.output_rings().len(), 1);
    assert!(op.input_rings().iter().zip(from.base_ring().as_iter()).all(|(l, r)| l.get_ring() == r.get_ring()));
    assert!(op.output_rings().at(0).get_ring() == to.base_ring().get_ring());

    let mut el_repr = Vec::with_capacity(from.rank() * from.base_ring().len());
    el_repr.resize(from.rank() * from.base_ring().len(), from.base_ring().at(0).zero());
    let mut el_repr = SubmatrixMut::from_1d(&mut el_repr, from.base_ring().len(), from.rank());
    for (j, c) in from.wrt_canonical_basis(el).iter().enumerate() {
        for (i, x) in from.base_ring().get_congruence(&c).as_iter().enumerate() {
            *el_repr.at_mut(i, j) = *x;
        }
    }

    let mut res_repr = Vec::with_capacity(el_repr.col_count());
    res_repr.resize(el_repr.col_count(), to.base_ring().zero());
    let mut res_repr = SubmatrixMut::from_1d(&mut res_repr, 1, el_repr.col_count());
    op.apply(el_repr.as_const(), res_repr.reborrow());
    return to.from_canonical_basis(res_repr.row_at(0).copy_els().iter());
}