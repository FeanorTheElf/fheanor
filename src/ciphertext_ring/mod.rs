use std::array::from_fn;
use std::convert::identity;

use feanor_math::integer::BigIntRing;
use feanor_math::matrix::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::zn_64::{ZnEl, Zn, ZnBase};
use feanor_math::rings::zn::zn_rns;
use feanor_math::seq::VectorView;
use tracing::instrument;

use crate::ciphertext_ring::indices::RNSFactorIndexList;
use crate::number_ring::NumberRingQuotient;
use crate::prepared_mul::PreparedMultiplicationRing;
use crate::rns_conv::RNSOperation;

pub mod indices;

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

pub enum RNSFactorCongruence<'a, R: ?Sized, E> {
    Zero,
    CongruentTo(&'a R, usize, &'a E)
}

pub fn drop_rns_factor_list_of_congruences<'a, R, E>(from: &'a R, dropped_rns_factors: &'a RNSFactorIndexList, element: &'a E) -> impl use<'a, R, E> + Iterator<Item = RNSFactorCongruence<'a, R, E>>
    where R: ?Sized + RingExtension<BaseRing = zn_rns::Zn<Zn, BigIntRing>>
{
    (0..from.base_ring().len()).scan(0, |drop_idx, factor_idx| {
        debug_assert!(*drop_idx == dropped_rns_factors.len() || factor_idx <= dropped_rns_factors[*drop_idx]);
        if *drop_idx < dropped_rns_factors.len() && factor_idx == dropped_rns_factors[*drop_idx] {
            *drop_idx += 1;
            return Some(None);
        } else {
            return Some(Some(RNSFactorCongruence::CongruentTo(from, factor_idx, element)));
        }
    }).filter_map(identity)
}

pub fn add_rns_factor_list_of_congruences<'a, R, E>(to: &'a R, from: &'a R, added_rns_factors: &'a RNSFactorIndexList, element: &'a E) -> impl use<'a, R, E> + Iterator<Item = RNSFactorCongruence<'a, R, E>>
    where R: ?Sized + RingExtension<BaseRing = zn_rns::Zn<Zn, BigIntRing>>
{
    (0..to.base_ring().len()).scan((0, 0), |(added_idx, from_factor_idx), factor_idx| {
        debug_assert!(*added_idx == added_rns_factors.len() || factor_idx <= added_rns_factors[*added_idx]);
        if *added_idx < added_rns_factors.len() && factor_idx == added_rns_factors[*added_idx] {
            *added_idx += 1;
            return Some(RNSFactorCongruence::Zero);
        } else {
            *from_factor_idx += 1;
            return Some(RNSFactorCongruence::CongruentTo(from, *from_factor_idx - 1, element));
        }
    })
}

///
/// Trait for rings `R/qR` with a number ring `R` and modulus `q = p1 ... pr` represented as 
/// RNS basis, which provide all necessary operations for use as ciphertext ring in BFV/BGV-style
/// HE schemes.
/// 
pub trait BGFVCiphertextRing: PreparedMultiplicationRing + NumberRingQuotient + RingExtension<BaseRing = zn_rns::Zn<Zn, BigIntRing>> {

    ///
    /// Computes the element of this ring that satisfies the given congruences.
    /// 
    /// More concretely, this function computes a ring element `x`, uniquely defined
    /// by the following: The iterator should return one element per RNS factor `p`
    /// of this ring. If the returned element is [`RNSFactorCongruence::Zero`], then
    /// `x = 0 mod p`. Otherwise, the returned element is [`RNSFactorCongruence::CongruentTo`]
    /// with a ring `R'` and index `i` and an element `y`. In that case, it is expected
    /// that the `i`-th RNS factor of `R'` is also `p`, and `x` will satisfy `x = y mod p`.
    /// 
    fn collect_rns_factors<'a, I>(&self, congruences: I) -> Self::Element
        where I: Iterator<Item = RNSFactorCongruence<'a, Self, Self::Element>>,
            Self: 'a;

    ///
    /// As [`BGFVCiphertextRing::collect_rns_factors()`] but for [`PreparedMultiplicationRing::PreparedMultiplicant`]s.
    /// 
    fn collect_rns_factors_prepared<'a, I>(&self, congruences: I) -> Self::PreparedMultiplicant
        where I: Iterator<Item = RNSFactorCongruence<'a, Self, Self::PreparedMultiplicant>>,
            Self: 'a;

    ///
    /// Computes the ring `R_q'`, where `q'` is the product of all RNS factors of `q`,
    /// except those whose indices are mentioned in `drop_rns_factors`.
    /// 
    fn drop_rns_factor(&self, drop_rns_factors: &RNSFactorIndexList) -> Self;

    ///
    /// Reduces an element of `from` modulo the modulus `q` of `self`, where `q` must divide the modulus `q'` of `from`.
    /// 
    /// More concretely, this computes the map
    /// ```text
    ///   R/q' -> R/q,  x -> x mod q
    /// ```
    /// In particular, the RNS factors of `q` must be exactly the RNS factors of `q'`,
    /// except for the RNS factors whose indices occur in `dropped_rns_factors`.
    /// 
    fn drop_rns_factor_element(&self, from: &Self, dropped_rns_factors: &RNSFactorIndexList, value: &Self::Element) -> Self::Element {
        assert_eq!(from.base_ring().len(), self.base_ring().len() + dropped_rns_factors.len());
        self.collect_rns_factors(drop_rns_factor_list_of_congruences(from, dropped_rns_factors, value))
    }

    ///
    /// As [`BGFVCiphertextRing::drop_rns_factor_element()`] but for [`PreparedMultiplicationRing::PreparedMultiplicant`]s.
    /// 
    fn drop_rns_factor_prepared_element(&self, from: &Self, dropped_rns_factors: &RNSFactorIndexList, value: &Self::PreparedMultiplicant) -> Self::PreparedMultiplicant {
        assert_eq!(from.base_ring().len(), self.base_ring().len() + dropped_rns_factors.len());
        self.collect_rns_factors_prepared(drop_rns_factor_list_of_congruences(from, dropped_rns_factors, value))
    }

    ///
    /// Computes the element modulus the modulus `q` of `self` that is congruent to the given element
    /// modulo the modulus `q'` of `from` and congruent to zero modulo `q/q'`.
    /// 
    /// More concretely, this computes the map
    /// ```text
    ///   R/q' -> R/q,  x -> x (q/q' mod q')^-1 q/q'
    /// ```
    /// In particular, the RNS factors of `q'` must be exactly the RNS factors of `q`,
    /// except for the RNS factors whose indices occur in `added_rns_factors`.
    /// 
    fn add_rns_factor_element(&self, from: &Self, added_rns_factors: &RNSFactorIndexList, value: &Self::Element) -> Self::Element {
        assert_eq!(self.base_ring().len(), from.base_ring().len() + added_rns_factors.len());
        self.collect_rns_factors(add_rns_factor_list_of_congruences(self, from, added_rns_factors, value))
    }

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
    /// Hence, it is recommended to instead use [`FreeAlgebra::wrt_canonical_basis()`]
    /// and [`FreeAlgebra::from_canonical_basis()`], whose
    /// result is uniquely defined. However, note that these may incur costs for internal
    /// representation conversion, which may not always be acceptable.
    /// 
    /// Concrete representations:
    ///  - [`single_rns_ring::SingleRNSRing`] will currently return the coefficients of a polynomial
    ///    of degree `< m` (not necessarily `< phi(m)`) that gives the element when evaluated at `𝝵`
    ///  - [`double_rns_managed::ManagedDoubleRNSRing`] will currently return the coefficients w.r.t.
    ///    the "small basis" as specified by [`AbstractNumberRing`]. If `m` is a product of two primes
    ///    and represented as a [`CompositeCyclotomicNumberRing`], this is the powerful basis.
    /// 
    /// Currently, this function is only used for gadget products and modulus-switching. In these
    /// cases, it is indeed ok if the representation is not unique, as long as it is w.r.t. a small
    /// generating set.
    /// 
    /// [`CompositeCyclotomicNumberRing`]: crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing
    /// [`AbstractNumberRing`]: crate::number_ring::AbstractNumberRing
    /// [`FreeAlgebra::from_canonical_basis()`]: feanor_math::rings::extension::FreeAlgebra::from_canonical_basis()
    /// [`FreeAlgebra::wrt_canonical_basis()`]: feanor_math::rings::extension::FreeAlgebra::wrt_canonical_basis()
    /// 
    fn as_representation_wrt_small_generating_set<V>(&self, x: &Self::Element, output: SubmatrixMut<V, ZnEl>)
        where V: AsPointerToSlice<ZnEl>;

    ///
    /// Creates a ring element from its underlying representation.
    /// 
    /// This is the counterpart of [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`],
    /// which contains a more detailed documentation.
    /// 
    /// This function is a compromise between encapsulating the storage of ring elements
    /// and exposing it (which is sometimes necessary for performance). 
    /// Hence, it is recommended to instead use [`FreeAlgebra::wrt_canonical_basis()`]
    /// and [`FreeAlgebra::from_canonical_basis()`], whose result
    /// is uniquely defined. However, note that these may incur costs for internal representation
    /// conversion, which may not always be acceptable.
    /// 
    /// [`FreeAlgebra::from_canonical_basis()`]: feanor_math::rings::extension::FreeAlgebra::from_canonical_basis()
    /// [`FreeAlgebra::wrt_canonical_basis()`]: feanor_math::rings::extension::FreeAlgebra::wrt_canonical_basis()
    /// 
    fn from_representation_wrt_small_generating_set<V>(&self, data: Submatrix<V, ZnEl>) -> Self::Element
        where V: AsPointerToSlice<ZnEl>;

    ///
    /// Computes `[lhs[0] * rhs[0], lhs[0] * rhs[1] + lhs[1] * rhs[0], lhs[1] * rhs[1]]`, but might be
    /// faster than the naive way of evaluating this.
    /// 
    #[instrument(skip_all)]
    fn two_by_two_convolution(&self, lhs: [&Self::Element; 2], rhs: [&Self::Element; 2]) -> [Self::Element; 3] {
        let lhs_prep: [_; 2] = from_fn(|i| self.prepare_multiplicant(lhs[i]));
        let rhs_prep: [_; 2] = from_fn(|i| self.prepare_multiplicant(rhs[i]));
        [
            self.mul_prepared(lhs[0], Some(&lhs_prep[0]), rhs[0], Some(&rhs_prep[0])),
            self.inner_product_prepared([(lhs[0], Some(&lhs_prep[0]), rhs[1], Some(&rhs_prep[1])), (lhs[1], Some(&lhs_prep[1]), rhs[0], Some(&rhs_prep[0]))]),
            self.mul_prepared(lhs[1], Some(&lhs_prep[1]), rhs[1], Some(&rhs_prep[1]))
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

#[cfg(test)]
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;

#[test]
fn test_drop_rns_factor_list_of_congruences() {
    let from = FreeAlgebraImpl::new(zn_rns::Zn::new(vec![Zn::new(17), Zn::new(19), Zn::new(23)], BigIntRing::RING), 1, []);
    let dummy = ();
    let dropped_rns_factors = RNSFactorIndexList::from([1], 3);

    let actual = drop_rns_factor_list_of_congruences(from.get_ring(), &dropped_rns_factors, &dummy).collect::<Vec<_>>();
    assert_eq!(2, actual.len());
    match actual[0] {
        RNSFactorCongruence::CongruentTo(_, i, ()) => assert_eq!(0, i),
        _ => unreachable!()
    }
    match actual[1] {
        RNSFactorCongruence::CongruentTo(_, i, ()) => assert_eq!(2, i),
        _ => unreachable!()
    }
}