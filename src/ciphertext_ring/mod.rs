use std::alloc::Allocator;
use std::array::from_fn;
use std::convert::identity;
use std::mem::MaybeUninit;
use std::ops::Range;

use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::{BigIntRing, IntegerRingStore, int_cast};
use feanor_math::matrix::*;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::pid::PrincipalIdealRingStore;
use feanor_math::ring::*;
use feanor_math::rings::zn::zn_64::{Zn, ZnBase, ZnEl};
use feanor_math::rings::zn::{ZnRingStore, zn_rns};
use feanor_math::seq::VectorView;
use tracing::instrument;

use crate::ciphertext_ring::indices::RNSFactorIndexList;
use crate::number_ring::NumberRingQuotient;
use crate::prepared_mul::PreparedMultiplicationRing;
use crate::rns_conv::bfv_rescale::{RNSRescaling, RNSRescalingConversion};
use crate::rns_conv::bgv_rescale::RNSCongruencePreservingBaseConversion;
use crate::rns_conv::{RNSOperation, UsedBaseConversion};
use crate::{ZZbig, ZZi64};

pub mod indices;

/// Contains utilities to serialize/deserialize elements of rings that are based on RNS bases.
pub mod serialization;

/// Contains [`double_rns_ring::DoubleRNSRing`], an implementation of the ring `R/qR` for suitable
/// `q`.  
pub mod double_rns_ring;

/// Contains [`single_rns_ring::SingleRNSRing`], an implementation of the ring `R/qR` for suitable
/// `q`.  
pub mod single_rns_ring;

/// Contains [`double_rns_managed::ManagedDoubleRNSRing`], an implementation of the ring `R/qR` for
/// suitable `q` that is based on [`double_rns_ring::DoubleRNSRing`].
///  
pub mod double_rns_managed;

pub enum RNSFactorCongruence<'a, R: ?Sized, E> {
    Zero,
    CongruentTo(&'a R, usize, &'a E),
}

pub fn drop_rns_factor_list_of_congruences<'a, R, E>(
    from: &'a R,
    dropped_rns_factors: &'a RNSFactorIndexList,
    element: &'a E,
) -> impl use<'a, R, E> + Iterator<Item = RNSFactorCongruence<'a, R, E>>
where
    R: ?Sized + RingExtension<BaseRing = zn_rns::Zn<Zn, BigIntRing>>,
{
    (0..from.base_ring().len())
        .scan(0, |drop_idx, factor_idx| {
            debug_assert!(*drop_idx == dropped_rns_factors.len() || factor_idx <= dropped_rns_factors[*drop_idx]);
            if *drop_idx < dropped_rns_factors.len() && factor_idx == dropped_rns_factors[*drop_idx] {
                *drop_idx += 1;
                return Some(None);
            } else {
                return Some(Some(RNSFactorCongruence::CongruentTo(from, factor_idx, element)));
            }
        })
        .filter_map(identity)
}

pub fn add_rns_factor_list_of_congruences<'a, R, E>(
    to: &'a R,
    from: &'a R,
    added_rns_factors: &'a RNSFactorIndexList,
    element: &'a E,
) -> impl use<'a, R, E> + Iterator<Item = RNSFactorCongruence<'a, R, E>>
where
    R: ?Sized + RingExtension<BaseRing = zn_rns::Zn<Zn, BigIntRing>>,
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

pub trait AsSubmatrix<T> {
    type V: Sync + AsPointerToSlice<T>;

    fn as_submatrix<'a>(&'a self) -> Submatrix<'a, Self::V, T>;
}

impl<'a, V: Sync + AsPointerToSlice<T>, T> AsSubmatrix<T> for Submatrix<'a, V, T> {
    type V = V;

    fn as_submatrix<'b>(&'b self) -> Submatrix<'b, Self::V, T> { *self }
}

impl<T: Sync, A: Allocator> AsSubmatrix<T> for OwnedMatrix<T, A> {
    type V = AsFirstElement<T>;

    fn as_submatrix<'b>(&'b self) -> Submatrix<'b, Self::V, T> { self.data() }
}

/// Trait for number ring quotients `R/qR` where the modulus `q` factors into distinct primes `q =
/// p1 ... pr`, and thus the Residue number system (RNS) is used to represent coefficients, or
/// generally elements of `Z/qZ`.
///
/// This trait also defines additional RNS-related functionality that is often required when
/// building FHE from such rings.
pub trait NumberRingRNSQuotient:
    Send + Sync + NumberRingQuotient + PreparedMultiplicationRing + RingExtension<BaseRing = zn_rns::Zn<Zn, BigIntRing>>
{
    /// Computes the element of this ring that satisfies the given congruences.
    ///
    /// More concretely, this function computes a ring element `x`, uniquely defined
    /// by the following: The iterator should return one element per RNS factor `p`
    /// of this ring. If the returned element is [`RNSFactorCongruence::Zero`], then
    /// `x = 0 mod p`. Otherwise, the returned element is [`RNSFactorCongruence::CongruentTo`]
    /// with a ring `R'` and index `i` and an element `y`. In that case, it is expected
    /// that the `i`-th RNS factor of `R'` is also `p`, and `x` will satisfy `x = y mod p`.
    fn collect_rns_factors<'a, I>(&self, congruences: I) -> Self::Element
    where
        I: Iterator<Item = RNSFactorCongruence<'a, Self, Self::Element>>,
        Self: 'a;

    /// As [`NumberRingRNSQuotient::collect_rns_factors()`] but for
    /// [`PreparedMultiplicationRing::PreparedMultiplicant`]s.
    fn collect_rns_factors_prepared<'a, I>(&self, congruences: I) -> Self::PreparedMultiplicant
    where
        I: Iterator<Item = RNSFactorCongruence<'a, Self, Self::PreparedMultiplicant>>,
        Self: 'a;

    /// Computes the ring `R_q'`, where `q'` is the product of all RNS factors of `q`,
    /// except those whose indices are mentioned in `drop_rns_factors`.
    fn drop_rns_factor(&self, drop_rns_factors: &RNSFactorIndexList) -> Self;

    /// Reduces a [`PreparedMultiplicationRing::PreparedMultiplicant`] of `from` modulo the
    /// modulus `q` of `self`, where `q` must divide the modulus `q'` of `from`.
    ///
    /// In particular, the RNS factors of `q` must be exactly the RNS factors of `q'`,
    /// except for the RNS factors whose indices occur in `dropped_rns_factors`. For ring
    /// elements, the same reduction is performed by [`NumberRingRNSQuotient::lift_from()`].
    fn drop_rns_factor_prepared_element(
        &self,
        from: &Self,
        dropped_rns_factors: &RNSFactorIndexList,
        value: &Self::PreparedMultiplicant,
    ) -> Self::PreparedMultiplicant {
        assert_eq!(
            from.base_ring().len(),
            self.base_ring().len() + dropped_rns_factors.len()
        );
        self.collect_rns_factors_prepared(drop_rns_factor_list_of_congruences(from, dropped_rns_factors, value))
    }

    /// Computes the element of this ring that is congruent to `value` modulo the modulus `q_from`
    /// of `from`, and congruent to zero modulo `q_self / q_from`, where `q_self` is the modulus of
    /// `self`.
    ///
    /// More concretely, this computes the map
    /// ```text
    ///   R/q_from R -> R/q_self R,  x -> x (q_self/q_from mod q_from)^-1 q_self/q_from
    /// ```
    /// This requires that `q_from` divides `q_self`, i.e. every RNS factor of `from` must also
    /// be an RNS factor of `self` (not necessarily in the same order).
    fn crt_lift_from(&self, from: &Self, value: &Self::Element) -> Self::Element {
        let positions_in_self = rns_factor_positions(from.base_ring(), self.base_ring())
            .expect("every RNS factor of `from` must also be an RNS factor of `self`");
        self.collect_rns_factors((0..self.base_ring().len()).map(|i| {
            match positions_in_self.iter().position(|j| *j == i) {
                Some(from_idx) => RNSFactorCongruence::CongruentTo(from, from_idx, value),
                None => RNSFactorCongruence::Zero,
            }
        }))
    }

    /// Returns the length of the small generating set used for
    /// [`NumberRingRNSQuotient::as_representation_wrt_small_generating_set()`]
    /// and [`NumberRingRNSQuotient::from_representation_wrt_small_generating_set()`].
    fn small_generating_set_len(&self) -> usize;

    /// Returns a view on the underlying representation of `x`.
    ///
    /// This is the counterpart of
    /// [`NumberRingRNSQuotient::from_representation_wrt_small_generating_set()`].
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
    ///  - [`double_rns_managed::ManagedDoubleRNSRing`] will currently return the coefficients
    ///    w.r.t. the "small basis" as specified by [`NumberRingDescriptor`]. If `m` is a product of
    ///    two primes and represented as a [`TensorProductNumberRing`], this is the powerful basis.
    ///
    /// Currently, this function is only used for gadget products and modulus-switching. In these
    /// cases, it is indeed ok if the representation is not unique, as long as it is w.r.t. a small
    /// generating set.
    ///
    /// [`TensorProductNumberRing`]: crate::number_ring::tensor_ring::TensorProductNumberRing
    /// [`NumberRingDescriptor`]: crate::number_ring::NumberRingDescriptor
    /// [`FreeAlgebra::from_canonical_basis()`]: feanor_math::rings::extension::FreeAlgebra::from_canonical_basis()
    /// [`FreeAlgebra::wrt_canonical_basis()`]: feanor_math::rings::extension::FreeAlgebra::wrt_canonical_basis()
    fn as_representation_wrt_small_generating_set<'a>(&'a self, x: &'a Self::Element) -> impl 'a + AsSubmatrix<ZnEl>;

    /// Creates a ring element from its underlying representation.
    ///
    /// This is the counterpart of
    /// [`NumberRingRNSQuotient::as_representation_wrt_small_generating_set()`], which contains
    /// a more detailed documentation.
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
    fn from_representation_wrt_small_generating_set<F>(&self, initializer: F) -> Self::Element
    where
        F: FnOnce(
            SubmatrixMut<AsFirstElement<MaybeUninit<ZnEl>>, MaybeUninit<ZnEl>>,
        ) -> SubmatrixMut<AsFirstElement<MaybeUninit<ZnEl>>, ZnEl>;

    /// Applies the given [`RNSOperation`] to the representation of `el` w.r.t. the small
    /// generating set (see
    /// [`NumberRingRNSQuotient::as_representation_wrt_small_generating_set()`]), and returns the
    /// element of this ring whose representation is the result.
    ///
    /// More concretely, the operation is applied to each coefficient of the representation,
    /// i.e. to each column of the matrix returned by
    /// [`NumberRingRNSQuotient::as_representation_wrt_small_generating_set()`]. Here
    /// [`RNSOperation::input_rings()`] must be a contiguous range of the RNS factors of `from`
    /// (in the same order), and the operation is applied only to the corresponding rows of the
    /// representation. Furthermore, [`RNSOperation::output_rings()`] must be exactly the RNS
    /// factors of this ring (in the same order). Finally, `from` and `self` must be quotients
    /// of the same number ring.
    ///
    /// As explained in [`NumberRingRNSQuotient::as_representation_wrt_small_generating_set()`],
    /// the representation depends on the ring implementation. Hence, the result of this function
    /// also depends on the ring implementation, unless the given [`RNSOperation`] is a ring
    /// homomorphism.
    fn apply_rns_op_to_representation<Op>(&self, from: &Self, el: &Self::Element, op: &Op) -> Self::Element
    where
        Op: RNSOperation<RingType = ZnBase>;

    /// Returns the almost-exact lifting map `R/q_from R -> R/q_self R`, where `q_from` resp.
    /// `q_self` are the moduli of `from` resp. `self`.
    ///
    /// This map operates on the representation w.r.t. the small generating set (see
    /// [`NumberRingRNSQuotient::as_representation_wrt_small_generating_set()`]). More
    /// concretely, it maps each coefficient `x_i` of the representation to
    /// `lift(x_i) + e_i q_from mod q_self`, where `lift(x_i)` is the shortest lift of `x_i`
    /// and `e_i in { -1, 0, 1 }`. If `|lift(x_i)| <= q_from / 4`, then it is guaranteed that
    /// `e_i = 0`. If `q_self` divides `q_from`, this map is the (exact) reduction modulo `q_self`.
    ///
    /// Since the representation depends on the ring implementation, so does the result of
    /// this map (except when it is the reduction modulo `q_self`).
    fn lift_from<'a>(&'a self, from: &'a Self) -> impl 'a + Send + Sync + Fn(&Self::Element) -> Self::Element
    where
        Self: Sized,
    {
        lift_from_default_impl(self, from, |_, _, delta| delta)
    }

    /// Returns the almost-exact rescaling map `R/q_from R -> R/q_self R, x -> round(x num / den)`,
    /// where `q_from` resp. `q_self` are the moduli of `from` resp. `self`.
    ///
    /// This map operates on the representation w.r.t. the small generating set (see
    /// [`NumberRingRNSQuotient::as_representation_wrt_small_generating_set()`]). More
    /// concretely, it maps each coefficient `x_i` of the representation to
    /// `round(lift(x_i) num / den) + e_i mod q_self`, where `lift(x_i)` is the shortest lift
    /// of `x_i` and `e_i in { -1, 0, 1 }`. Since the representation depends on the ring
    /// implementation, so does the result of this map.
    ///
    /// This requires that `num` and `den` are positive, that `den / gcd(num, den)` is a product
    /// of RNS factors of `q_from`, and that `|lift(x_i)| <= q_from / 4` for all coefficients
    /// `x_i` of the input (the latter is only checked in debug builds).
    ///
    /// The two main use cases are modulus-switching, i.e. `num = q_self` and `den = q_from`,
    /// and BFV-style rescaling after multiplication, i.e. `num = t` and `den = q_self`.
    fn rescale_from<'a>(
        &'a self,
        from: &'a Self,
        num: &El<BigIntRing>,
        den: &El<BigIntRing>,
    ) -> impl 'a + Send + Sync + Fn(&Self::Element) -> Self::Element
    where
        Self: Sized,
    {
        rescale_from_default_impl(self, from, num, den)
    }

    /// Returns the almost-exact congruence-preserving rescaling map `R/q_from R -> R/q_self R`,
    /// where `q_from` resp. `q_self` are the moduli of `from` resp. `self`. This is the
    /// rescaling used during BGV modulus-switching.
    ///
    /// This map operates on the representation w.r.t. the small generating set (see
    /// [`NumberRingRNSQuotient::as_representation_wrt_small_generating_set()`]). More
    /// concretely, it maps each coefficient `x_i` of the representation to `y_i mod q_self`,
    /// where `y_i` is (almost) the closest integer to `lift(x_i) q_self / q_from` that satisfies
    /// `q_from y_i = q_self lift(x_i) mod t`. Here `lift(x_i)` is the shortest lift of `x_i`.
    /// "Almost" means that `y_i` is either the closest or the second-closest such integer.
    /// Since the representation depends on the ring implementation, so does the result of
    /// this map.
    ///
    /// This requires that the modulus `t` of `Zt` is coprime to `q_from` and `q_self`.
    fn rescale_from_preserving_congruence<'a>(
        &'a self,
        from: &'a Self,
        Zt: Zn,
    ) -> impl 'a + Send + Sync + Fn(Self::Element) -> Self::Element
    where
        Self: Sized,
    {
        rescale_from_preserving_congruence_default_impl(self, from, Zt)
    }

    /// Computes `[lhs[0] * rhs[0], lhs[0] * rhs[1] + lhs[1] * rhs[0], lhs[1] * rhs[1]]`, but might
    /// be faster than the naive way of evaluating this.
    #[instrument(skip_all)]
    fn two_by_two_convolution(&self, lhs: [Self::Element; 2], rhs: [Self::Element; 2]) -> [Self::Element; 3] {
        let lhs_prep: [_; 2] = from_fn(|i| self.prepare_multiplicant(&lhs[i]));
        let rhs_prep: [_; 2] = from_fn(|i| self.prepare_multiplicant(&rhs[i]));
        [
            self.mul_prepared(&lhs[0], Some(&lhs_prep[0]), &rhs[0], Some(&rhs_prep[0])),
            self.inner_product_prepared([
                (&lhs[0], Some(&lhs_prep[0]), &rhs[1], Some(&rhs_prep[1])),
                (&lhs[1], Some(&lhs_prep[1]), &rhs[0], Some(&rhs_prep[0])),
            ]),
            self.mul_prepared(&lhs[1], Some(&lhs_prep[1]), &rhs[1], Some(&rhs_prep[1])),
        ]
    }

    /// Computes `[val[0] * val[0], 2 * val[0] * val[1], val[1] * val[1]]`, but might be
    /// faster than the naive way of evaluating this.
    #[instrument(skip_all)]
    fn two_by_two_convolution_square(&self, val: [Self::Element; 2]) -> [Self::Element; 3] {
        let val_prep: [_; 2] = from_fn(|i| self.prepare_multiplicant(&val[i]));
        let mut result = [
            self.mul_prepared(&val[0], Some(&val_prep[0]), &val[0], Some(&val_prep[0])),
            self.mul_prepared(&val[0], Some(&val_prep[0]), &val[1], Some(&val_prep[1])),
            self.mul_prepared(&val[1], Some(&val_prep[1]), &val[1], Some(&val_prep[1])),
        ];
        RingRef::new(self).int_hom().mul_assign_map(&mut result[1], 2);
        return result;
    }
}

/// Checks that the given [`RNSOperation`] can be applied to the representation of elements of
/// `from`, with the result being the representation of an element of `to`, as required by
/// [`NumberRingRNSQuotient::apply_rns_op_to_representation()`].
///
/// Returns the range of RNS factors of `from` that are the input of `op`.
pub(crate) fn rns_op_input_range<R, Op>(to: &R, from: &R, op: &Op) -> Range<usize>
where
    R: ?Sized + NumberRingRNSQuotient,
    Op: RNSOperation<RingType = ZnBase>,
{
    assert!(from.number_ring() == to.number_ring());
    assert_eq!(from.small_generating_set_len(), to.small_generating_set_len());
    assert!(
        !op.input_rings().is_empty(),
        "the RNS operation must have at least one input RNS factor"
    );
    let start = from
        .base_ring()
        .as_iter()
        .position(|rns_factor| rns_factor.get_ring() == op.input_rings()[0].get_ring())
        .expect("the input RNS factors of the RNS operation must be RNS factors of `from`");
    let end = start + op.input_rings().len();
    assert!(
        end <= from.base_ring().len()
            && op
                .input_rings()
                .iter()
                .zip(from.base_ring().as_iter().skip(start))
                .all(|(l, r)| l.get_ring() == r.get_ring()),
        "the input RNS factors of the RNS operation must be a contiguous range of the RNS factors of `from`"
    );
    assert!(
        op.output_rings().len() == to.base_ring().len()
            && op
                .output_rings()
                .iter()
                .zip(to.base_ring().as_iter())
                .all(|(l, r)| l.get_ring() == r.get_ring()),
        "the output RNS factors of the RNS operation must be exactly the RNS factors of `to`"
    );
    return start..end;
}

/// A map between two quotients of the same number ring, as returned e.g. by
/// [`NumberRingRNSQuotient::lift_from()`].
pub(crate) type PreparedRNSMap<'a, R> =
    Box<dyn 'a + Send + Sync + Fn(&<R as RingBase>::Element) -> <R as RingBase>::Element>;

fn rns_moduli(rns_base: &zn_rns::Zn<Zn, BigIntRing>) -> Vec<Zn> { rns_base.as_iter().cloned().collect() }

fn product_of_rns_factors(rns_base: &zn_rns::Zn<Zn, BigIntRing>, indices: &RNSFactorIndexList) -> El<BigIntRing> {
    ZZbig.prod(
        indices
            .iter()
            .map(|i| int_cast(*rns_base.at(*i).modulus(), ZZbig, ZZi64)),
    )
}

/// If every RNS factor of `subset` is also an RNS factor of `master`, returns, for every RNS
/// factor of `subset`, its index in `master`. Otherwise, returns `None`.
fn rns_factor_positions(
    subset: &zn_rns::Zn<Zn, BigIntRing>,
    master: &zn_rns::Zn<Zn, BigIntRing>,
) -> Option<Vec<usize>> {
    subset
        .as_iter()
        .map(|rns_factor| {
            master
                .as_iter()
                .position(|master_rns_factor| master_rns_factor.get_ring() == rns_factor.get_ring())
        })
        .collect()
}

/// Reduces `x` modulo the modulus of `to`, where `positions_in_from` contains, for every RNS
/// factor of `to`, its index in the RNS factors of `from`.
fn reduce_from<R: NumberRingRNSQuotient>(to: &R, from: &R, positions_in_from: &[usize], x: &R::Element) -> R::Element {
    to.collect_rns_factors(
        positions_in_from
            .iter()
            .map(|from_idx| RNSFactorCongruence::CongruentTo(from, *from_idx, x)),
    )
}

/// Default implementation of [`NumberRingRNSQuotient::lift_from()`].
///
/// If `q_from` divides `q_to`, the lift is computed by only converting to the additional RNS
/// factors of `q_to`. The result of this conversion (as an element of the ring that only consists
/// of these additional RNS factors) is passed to `prepare_delta`, together with the input element,
/// before it is combined with the input element. This allows ring implementations to control the
/// representation of the result.
pub(crate) fn lift_from_default_impl<'a, R, F>(to: &'a R, from: &'a R, prepare_delta: F) -> PreparedRNSMap<'a, R>
where
    R: NumberRingRNSQuotient,
    F: 'a + Send + Sync + Fn(&R, &R::Element, R::Element) -> R::Element,
{
    assert!(from.number_ring() == to.number_ring());
    if let Some(positions_in_from) = rns_factor_positions(to.base_ring(), from.base_ring()) {
        // `q_to | q_from`, so this is just a reduction
        return Box::new(move |x| reduce_from(to, from, &positions_in_from, x));
    }
    if let Some(positions_in_to) = rns_factor_positions(from.base_ring(), to.base_ring()) {
        let shared_rns_factors = RNSFactorIndexList::from(positions_in_to, to.base_ring().len());
        let C_delta = to.drop_rns_factor(&shared_rns_factors);
        let lift = UsedBaseConversion::new(rns_moduli(from.base_ring()), rns_moduli(C_delta.base_ring()));
        return Box::new(move |x| {
            let delta = prepare_delta(&C_delta, x, C_delta.apply_rns_op_to_representation(from, x, &lift));
            return to.add(to.crt_lift_from(from, x), to.crt_lift_from(&C_delta, &delta));
        });
    }
    let conversion = UsedBaseConversion::new(rns_moduli(from.base_ring()), rns_moduli(to.base_ring()));
    return Box::new(move |x| to.apply_rns_op_to_representation(from, x, &conversion));
}

/// Default implementation of [`NumberRingRNSQuotient::rescale_from()`].
fn rescale_from_default_impl<'a, R>(
    to: &'a R,
    from: &'a R,
    num: &El<BigIntRing>,
    den: &El<BigIntRing>,
) -> PreparedRNSMap<'a, R>
where
    R: NumberRingRNSQuotient,
{
    assert!(from.number_ring() == to.number_ring());
    assert!(ZZbig.is_pos(num) && ZZbig.is_pos(den));
    let gcd = ZZbig.abs(ZZbig.ideal_gen(num, den));
    let num = ZZbig.checked_div(num, &gcd).unwrap();
    let mut den_remaining = ZZbig.checked_div(den, &gcd).unwrap();
    let mut den_rns_factors = Vec::new();
    for (i, rns_factor) in from.base_ring().as_iter().enumerate() {
        if let Some(quo) = ZZbig.checked_div(&den_remaining, &int_cast(*rns_factor.modulus(), ZZbig, ZZi64)) {
            den_remaining = quo;
            den_rns_factors.push(i);
        }
    }
    assert!(
        ZZbig.is_one(&den_remaining),
        "`den / gcd(num, den)` must be a product of RNS factors of `from`"
    );

    // if this is a modulus-switch, i.e. `num/den = q_to/q_from`, we don't need a final base
    // conversion
    let only_from_rns_factors = RNSFactorIndexList::missing_from(to.base_ring(), from.base_ring());
    let only_to_rns_factors = RNSFactorIndexList::missing_from(from.base_ring(), to.base_ring());
    if only_from_rns_factors.iter().eq(den_rns_factors.iter())
        && ZZbig.eq_el(&num, &product_of_rns_factors(to.base_ring(), &only_to_rns_factors))
    {
        let rescaling = RNSRescaling::new(rns_moduli(from.base_ring()), rns_moduli(to.base_ring()));
        return Box::new(move |x| to.apply_rns_op_to_representation(from, x, &rescaling));
    }

    let rescaling = RNSRescalingConversion::new(
        rns_moduli(from.base_ring()),
        rns_moduli(to.base_ring()),
        &num,
        den_rns_factors,
    );
    return Box::new(move |x| to.apply_rns_op_to_representation(from, x, &rescaling));
}

/// Default implementation of [`NumberRingRNSQuotient::rescale_from_preserving_congruence()`].
fn rescale_from_preserving_congruence_default_impl<'a, R>(
    to: &'a R,
    from: &'a R,
    Zt: Zn,
) -> Box<dyn 'a + Send + Sync + Fn(R::Element) -> R::Element>
where
    R: NumberRingRNSQuotient,
{
    assert!(from.number_ring() == to.number_ring());
    let added_rns_factors = RNSFactorIndexList::missing_from(from.base_ring(), to.base_ring());
    let dropped_rns_factors = RNSFactorIndexList::missing_from(to.base_ring(), from.base_ring());
    let kept_rns_factors = dropped_rns_factors.complement(from.base_ring().len());
    let a = from
        .base_ring()
        .coerce(&ZZbig, product_of_rns_factors(to.base_ring(), &added_rns_factors));

    /// Maps `x` to the element of `to` that is congruent to `x` modulo all RNS factors
    /// that `to` and `from` have in common, and congruent to `0` modulo the RNS factors that
    /// only `to` has.
    fn map_kept_factors<R: NumberRingRNSQuotient>(
        to: &R,
        from: &R,
        added_rns_factors: &RNSFactorIndexList,
        x: R::Element,
    ) -> R::Element {
        to.collect_rns_factors((0..to.base_ring().len()).map(|idx| {
            if added_rns_factors.contains(idx) {
                RNSFactorCongruence::Zero
            } else {
                let from_idx = from
                    .base_ring()
                    .as_iter()
                    .position(|from_rns_factor| from_rns_factor.get_ring() == to.base_ring().at(idx).get_ring())
                    .unwrap();
                RNSFactorCongruence::CongruentTo(from, from_idx, &x)
            }
        }))
    }

    if kept_rns_factors.len() == from.base_ring().len() {
        if kept_rns_factors.len() == to.base_ring().len() {
            return Box::new(identity);
        } else {
            return Box::new(move |mut x| {
                RingRef::new(from).inclusion().mul_assign_ref_map(&mut x, &a);
                return map_kept_factors(to, from, &added_rns_factors, x);
            });
        }
    }

    let C_dropped = from.drop_rns_factor(&kept_rns_factors);
    let C_dropped_positions_in_from = rns_factor_positions(C_dropped.base_ring(), from.base_ring()).unwrap();
    let compute_delta =
        RNSCongruencePreservingBaseConversion::new(rns_moduli(C_dropped.base_ring()), rns_moduli(to.base_ring()), Zt);
    let b_inv = to
        .base_ring()
        .invert(
            &to.base_ring()
                .coerce(&ZZbig, product_of_rns_factors(from.base_ring(), &dropped_rns_factors)),
        )
        .unwrap();

    return Box::new(move |mut x| {
        RingRef::new(from).inclusion().mul_assign_ref_map(&mut x, &a);
        let x_dropped = reduce_from(&C_dropped, from, &C_dropped_positions_in_from, &x);
        let delta = to.apply_rns_op_to_representation(&C_dropped, &x_dropped, &compute_delta);
        return RingRef::new(to)
            .inclusion()
            .mul_ref_snd_map(to.sub(map_kept_factors(to, from, &added_rns_factors, x), delta), &b_inv);
    });
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use feanor_math::pid::EuclideanRingStore;
    use feanor_math::rings::extension::FreeAlgebraStore;
    use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
    use feanor_math::seq::VectorFn;

    use super::*;
    use crate::DefaultConvolution;
    use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;

    #[test]
    fn test_drop_rns_factor_list_of_congruences() {
        feanor_tracing::DelayedLogger::init_test();
        let from = FreeAlgebraImpl::new(
            zn_rns::Zn::new(vec![Zn::new(17), Zn::new(19), Zn::new(23)], BigIntRing::RING),
            1,
            [],
        );
        let dummy = ();
        let dropped_rns_factors = RNSFactorIndexList::from([1], 3);

        let actual =
            drop_rns_factor_list_of_congruences(from.get_ring(), &dropped_rns_factors, &dummy).collect::<Vec<_>>();
        assert_eq!(2, actual.len());
        match actual[0] {
            RNSFactorCongruence::CongruentTo(_, i, ()) => assert_eq!(0, i),
            _ => unreachable!(),
        }
        match actual[1] {
            RNSFactorCongruence::CongruentTo(_, i, ()) => assert_eq!(2, i),
            _ => unreachable!(),
        }
    }

    /// Returns `n` integers in `(-bound, bound)`, which are "pseudo-random" enough for tests
    fn sample_integers(n: usize, bound: &El<BigIntRing>, seed: i32) -> Vec<El<BigIntRing>> {
        let range = ZZbig.int_hom().mul_ref_map(bound, &2);
        (0..n)
            .map(|i| {
                let value = ZZbig.pow(ZZbig.int_hom().map(i as i32 + seed * 1000 + 3), 13);
                ZZbig.sub_ref_snd(ZZbig.euclidean_rem(value, &range), bound)
            })
            .collect()
    }

    fn element_from_coefficients<R: NumberRingRNSQuotient>(ring: &R, coefficients: &[El<BigIntRing>]) -> R::Element {
        RingRef::new(ring).from_canonical_basis(
            coefficients
                .iter()
                .map(|c| ring.base_ring().coerce(&ZZbig, ZZbig.clone_el(c))),
        )
    }

    fn coefficients_of<R: NumberRingRNSQuotient>(ring: &R, x: &R::Element) -> Vec<El<BigIntRing>> {
        let ring = RingRef::new(ring);
        let coefficients = ring.wrt_canonical_basis(x);
        (0..coefficients.len())
            .map(|i| ring.base_ring().smallest_lift(coefficients.at(i)))
            .collect()
    }

    /// Asserts that the given elements of `Z/qZ` (given by their shortest lifts) differ by at most
    /// `tolerance`
    fn assert_close_mod(q: &El<BigIntRing>, expected: &El<BigIntRing>, actual: &El<BigIntRing>, tolerance: i32) {
        let mut difference = ZZbig.euclidean_rem(ZZbig.sub_ref(actual, expected), q);
        if ZZbig.is_gt(&ZZbig.int_hom().mul_ref_map(&difference, &2), q) {
            ZZbig.sub_assign_ref(&mut difference, q);
        }
        assert!(
            ZZbig.is_leq(&ZZbig.abs(difference), &ZZbig.int_hom().map(tolerance)),
            "expected {} to be {} +/- {} modulo {}",
            ZZbig.format(actual),
            ZZbig.format(expected),
            tolerance,
            ZZbig.format(q)
        );
    }

    /// Tests [`NumberRingRNSQuotient::lift_from()`], [`NumberRingRNSQuotient::rescale_from()`] and
    /// [`NumberRingRNSQuotient::rescale_from_preserving_congruence()`] for two rings, where the RNS
    /// factors of `C` are the first RNS factors of `C_large`.
    ///
    /// The number ring must be a power-of-two cyclotomic number ring, so that the small generating
    /// set is (closely related to) the canonical basis. Since the representation of
    /// [`single_rns_ring::SingleRNSRing`] has `2 rank` columns, which are mapped independently, we
    /// allow twice the usual error when comparing canonical coefficients.
    fn test_rns_maps<R: NumberRingRNSQuotient + Send + Sync>(C: &R, C_large: &R) {
        let n = C.rank();
        let q = C.base_ring().modulus();
        let Q = C_large.base_ring().modulus();
        assert!(ZZbig.checked_div(Q, q).is_some());

        // lifting small elements is exact, in both directions
        let small_coefficients = sample_integers(n, &ZZbig.int_hom().map(1000), 0);
        let x = element_from_coefficients(C, &small_coefficients);
        let x_large = C_large.lift_from(C)(&x);
        assert!(
            coefficients_of(C_large, &x_large)
                .iter()
                .zip(small_coefficients.iter())
                .all(|(l, r)| ZZbig.eq_el(l, r))
        );
        let x_reduced = C.lift_from(C_large)(&x_large);
        assert!(C.eq_el(&x, &x_reduced));

        let large_coefficients = sample_integers(n, &ZZbig.rounded_div(ZZbig.clone_el(Q), &ZZbig.int_hom().map(8)), 1);
        let x = element_from_coefficients(C_large, &large_coefficients);

        // modulus-switching
        let actual = coefficients_of(C, &C.rescale_from(C_large, q, Q)(&x));
        for (x_i, actual_i) in large_coefficients.iter().zip(actual.iter()) {
            let expected_i = ZZbig.rounded_div(ZZbig.mul_ref(x_i, q), Q);
            assert_close_mod(q, &expected_i, actual_i, 2);
        }

        // BFV-style rescaling, both with small `t` and large `t`
        for t in [ZZbig.int_hom().map(17), ZZbig.add(ZZbig.power_of_two(60), ZZbig.one())] {
            let actual = coefficients_of(C, &C.rescale_from(C_large, &t, q)(&x));
            for (x_i, actual_i) in large_coefficients.iter().zip(actual.iter()) {
                let expected_i = ZZbig.rounded_div(ZZbig.mul_ref(x_i, &t), q);
                assert_close_mod(q, &expected_i, actual_i, 2);
            }
        }

        // BGV-style rescaling
        let t = 17;
        let x_copy = C_large.clone_el(&x);
        let actual = coefficients_of(
            C,
            &C.rescale_from_preserving_congruence(C_large, Zn::new(t as u64))(x_copy),
        );
        for (x_i, y_i) in large_coefficients.iter().zip(actual.iter()) {
            let congruence_diff = ZZbig.sub(ZZbig.mul_ref(Q, y_i), ZZbig.mul_ref(q, x_i));
            assert!(ZZbig.is_zero(&ZZbig.euclidean_rem(congruence_diff, &ZZbig.int_hom().map(t))));
            assert_close_mod(q, &ZZbig.rounded_div(ZZbig.mul_ref(x_i, q), Q), y_i, 2 * t);
        }
    }

    #[test]
    fn test_rns_maps_double_rns() {
        feanor_tracing::DelayedLogger::init_test();
        let number_ring = Pow2CyclotomicNumberRing::new(64);
        let C = double_rns_ring::DoubleRNSRingBase::new_with_modulus_size(number_ring.clone(), None, 100..120);
        let C_large =
            double_rns_ring::DoubleRNSRingBase::new_with_modulus_size(number_ring, Some(C.base_ring()), 250..270);
        test_rns_maps(C.get_ring(), C_large.get_ring());
    }

    #[test]
    fn test_rns_maps_managed_double_rns() {
        feanor_tracing::DelayedLogger::init_test();
        let number_ring = Pow2CyclotomicNumberRing::new(64);
        let C =
            double_rns_managed::ManagedDoubleRNSRingBase::new_with_modulus_size(number_ring.clone(), None, 100..120);
        let C_large = double_rns_managed::ManagedDoubleRNSRingBase::new_with_modulus_size(
            number_ring,
            Some(C.base_ring()),
            250..270,
        );
        test_rns_maps(C.get_ring(), C_large.get_ring());
    }

    #[test]
    fn test_rns_maps_single_rns() {
        feanor_tracing::DelayedLogger::init_test();
        let number_ring = Pow2CyclotomicNumberRing::new(64);
        let C = single_rns_ring::SingleRNSRingBase::<_, Global, DefaultConvolution>::new_with_modulus_size(
            number_ring.clone(),
            None,
            100..120,
        );
        let C_large = single_rns_ring::SingleRNSRingBase::<_, Global, DefaultConvolution>::new_with_modulus_size(
            number_ring,
            Some(C.base_ring()),
            250..270,
        );
        test_rns_maps(C.get_ring(), C_large.get_ring());
    }
}
