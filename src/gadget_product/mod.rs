use std::alloc::{Allocator, Global};
use std::ops::Range;

use feanor_math::group::AbelianGroupStore;
use feanor_math::integer::BigIntRing;
use feanor_math::matrix::*;
use feanor_math::primitive_int::StaticRing;
use feanor_math::rings::zn::zn_64;
use feanor_math::ring::*;
use feanor_math::rings::zn::{zn_64::Zn, zn_rns};
use feanor_math::seq::{VectorFn, VectorView};
use feanor_math::homomorphism::Homomorphism;

use crate::ciphertext_ring::double_rns_ring::{DoubleRNSRing, DoubleRNSRingBase, SmallBasisEl};
use crate::ciphertext_ring::indices::RNSFactorIndexList;
use crate::ciphertext_ring::BGFVCiphertextRing;
use crate::number_ring::galois::*;
use crate::number_ring::{AbstractNumberRing, NumberRingQuotient};
use crate::prepared_mul::PreparedMultiplicationRing;
use crate::rns_conv::{RNSOperation, UsedBaseConversion};
use crate::gadget_product::digits::RNSGadgetVectorDigitIndices;

///
/// Contains the type [`RNSGadgetVectorDigitIndices`] which is used to
/// specify the digit set used for RNS gadget products.
/// 
pub mod digits;

type GadgetProductBaseConversion<A> = UsedBaseConversion<A>;

///
/// Represents the left-hand side operand of a gadget product.
/// 
/// In other words, this stores a "gadget-decomposition" of a single ring element `x`,
/// i.e. small ring elements `x[i]` such that `x = sum_i g[i] x[i]` for a gadget vector
/// `g`. The only supported gadget vectors are RNS-based gadget vectors, see 
/// [`RNSGadgetProductRhsOperand::gadget_vector_digits()`].
/// 
/// For more details, see [`RNSGadgetProductLhsOperand::gadget_product()`].
/// 
pub struct RNSGadgetProductLhsOperand<R: PreparedMultiplicationRing> {
    /// `i`-th entry stores a `i`-th part of the gadget decomposition of the represented element.
    /// We store the element once as `PreparedMultiplicant` for fast computation of gadget products, and 
    /// once as the element itself, since there currently is no way of getting the ring element out of
    /// a `PreparedMultiplicant`
    element_decomposition: Vec<(R::PreparedMultiplicant, R::Element)>
}

impl<R: BGFVCiphertextRing> RNSGadgetProductLhsOperand<R> {

    ///
    /// Creates a [`RNSGadgetProductLhsOperand`] w.r.t. the gadget vector given by `digits`.
    /// For an explanation of gadget products, see [`RNSGadgetProductLhsOperand::gadget_product()`].
    /// 
    pub fn from_element_with(ring: &R, el: &R::Element, digits: &RNSGadgetVectorDigitIndices) -> Self {
        Self::from_element_map_ring_with(ring, el, digits, ring)
    }

    /// 
    /// Creates a [`RNSGadgetProductLhsOperand`] w.r.t. the RNS gadget vector that has `digits` digits.
    /// For an explanation of gadget products, see [`RNSGadgetProductLhsOperand::gadget_product()`].
    /// 
    pub fn from_element(ring: &R, el: &R::Element, digits: usize) -> Self {
        Self::from_element_with(ring, el, &RNSGadgetVectorDigitIndices::select_digits(digits, ring.base_ring().len()))
    }

    /// 
    /// Creates a [`RNSGadgetProductLhsOperand`] w.r.t. the gadget vector given by `digits` over a different
    /// ring that the original element is contained in.
    /// 
    /// More concretely, if we have a number ring modulo two different moduli `q, q'`, we can decompose
    /// an element `x in Rq` as `x = sum_i g[i] x[i]` (the gadget vector is also defined modulo `q`), but
    /// then map every `x[i]` into `Rq'`, via `shortest-lift(x[i]) mod q'`.
    /// 
    /// There are two use cases I can think of:
    ///  - If `q | q'`, we basically compute a decomposition of `s * x`, where `s = 0 mod q'/q` and `s = 1 mod q`.
    ///    This is necessary during hybrid key switching
    ///  - If `q' < q` and the result of the gadget product is small, this allows to perform the computation for
    ///    less RNS factors, improving performance. This is similiar to the LKSS key switching algorithm.
    /// 
    pub fn from_element_map_ring_with(ring: &R, el: &R::Element, digits: &RNSGadgetVectorDigitIndices, out_ring: &R) -> Self {
        assert!(ring.number_ring() == out_ring.number_ring());
        assert!(digits.iter().all(|digit| digit.end > digit.start));
        let decomposition = gadget_decompose(ring, el, digits, out_ring);
        return Self {
            element_decomposition: decomposition
        };
    }
}

impl<NumberRing, A> RNSGadgetProductLhsOperand<DoubleRNSRingBase<NumberRing, A>> 
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    ///
    /// Creates a [`RNSGadgetProductLhsOperand`] w.r.t. the gadget vector given by `digits`.
    /// For an explanation of gadget products, see [`RNSGadgetProductLhsOperand::gadget_product()`].
    /// 
    pub fn from_double_rns_ring_with(ring: &DoubleRNSRingBase<NumberRing, A>, el: &SmallBasisEl<NumberRing, A>, digits: &RNSGadgetVectorDigitIndices) -> Self {
        assert!(digits.iter().all(|digit| digit.end > digit.start));
        let decomposition = gadget_decompose_doublerns(ring, el, digits);
        return Self {
            element_decomposition: decomposition
        };
    }

    /// 
    /// Creates a [`RNSGadgetProductLhsOperand`] w.r.t. the RNS gadget vector that has `digits` digits.
    /// For an explanation of gadget products, see [`RNSGadgetProductLhsOperand::gadget_product()`].
    /// 
    pub fn from_double_rns_ring(ring: &DoubleRNSRingBase<NumberRing, A>, el: &SmallBasisEl<NumberRing, A>, digits: usize) -> Self {
        Self::from_double_rns_ring_with(ring, el, &RNSGadgetVectorDigitIndices::select_digits(digits, ring.base_ring().len()))
    }
}

impl<R: PreparedMultiplicationRing> RNSGadgetProductLhsOperand<R> {

    pub fn apply_galois_action(&self, ring: &R, g: &GaloisGroupEl) -> Self 
        where R: NumberRingQuotient
    {
        Self {
            element_decomposition: self.element_decomposition.iter().map(|(_prepared_el, el)| {
                let new_el = ring.apply_galois_action(el, g);
                return (ring.prepare_multiplicant(&new_el), new_el);
            }).collect()
        }
    }

    pub fn apply_galois_action_many(self, ring: &R, gs: &[GaloisGroupEl]) -> Vec<Self>
        where R: NumberRingQuotient
    {
        let mut result = Vec::with_capacity(gs.len());
        result.resize_with(gs.len(), || RNSGadgetProductLhsOperand { element_decomposition: Vec::new() });
        for (prepared_el, el) in self.element_decomposition {
            let mut prepared_el = Some(prepared_el);
            let new_els = ring.apply_galois_action_many(&el, gs);
            for (i, (new_el, g)) in new_els.into_iter().zip(gs.iter()).enumerate() {
                if ring.acting_galois_group().is_identity(g) {
                    result[i].element_decomposition.push((prepared_el.take().unwrap(), new_el));
                } else {
                    result[i].element_decomposition.push((ring.prepare_multiplicant(&new_el), new_el));
                }
            }
        }
        return result;
    }

    ///
    /// Computes the "RNS-gadget product" of two elements in this ring, as often required
    /// in HE scenarios. A "gadget product" computes the approximate product of two
    /// ring elements `x` and `y` by using `y` and multiple scaled & noisy approximations 
    /// to `x`. This function only supports the gadget vector given by a decomposition
    /// `q = D1 ... Dr` into coprime "digits".
    /// 
    /// Note that this performs just a gadget product, and no additional scalings as in
    /// hybrid key switching. These can be built on top of the gadget product.
    /// 
    /// # What exactly is a "gadget product"?
    /// 
    /// In an HE setting, we often have a noisy approximation to some value `x`, say
    /// `x + e`. Now the normal product `(x + e)y = xy + ey` includes an error of `ey`, which
    /// (if `y` is arbitrary) is not in any way an approximation to `xy` anymore. Instead,
    /// we can take a so-called "gadget vector" `g` and provide multiple noisy scalings of `x`, 
    /// say `g[1] * x + e1` to `g[r] * x + er`.
    /// Using these, we can approximate `xy` by computing a gadget-decomposition 
    /// `y = g[1] * y1 + ... + g[m] * ym` of `y`, where the values `yi` are small, and then use 
    /// `y1 (g[1] * x + e1) + ... + ym (g[m] * x + em)` as an approximation to `xy`.
    /// 
    /// The gadget vector used for this "RNS-gadget product" is the one given by the unit vectors
    /// in the decomposition `q = D1 ... Dr` into pairwise coprime "digits". In the simplest case,
    /// those digits are just the prime factors of `q`. However, it is usually beneficial to
    /// group multiple prime factors into a single digit, since decreasing the number of digits
    /// will significantly decrease the work we have to do when computing the inner product
    /// `sum_i (g[i] xi + ei) yi`. Note that this will of course decrease the quality of 
    /// approximation to `xy` (i.e. increase the error `sum_i yi ei`). Hence, choose the
    /// parameter `digits` appropriately. The gadget vector used in a specific case can be
    /// queried using [`RNSGadgetProductRhsOperand::gadget_vector()`]. 
    /// 
    /// # Example
    /// ```
    /// # use feanor_math::ring::*;
    /// # use feanor_math::assert_el_eq;
    /// # use feanor_math::homomorphism::*;
    /// # use feanor_math::rings::zn::*;
    /// # use feanor_math::rings::zn::zn_64::*;
    /// # use feanor_math::rings::finite::*;
    /// # use feanor_math::integer::BigIntRing;
    /// # use feanor_math::algorithms::fft::cooley_tuckey::CooleyTuckeyFFT;
    /// # use feanor_math::rings::extension::FreeAlgebraStore;
    /// # use feanor_math::seq::*;
    /// # use anonymizedhelibrary::ciphertext_ring::double_rns_managed::*;
    /// # use anonymizedhelibrary::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
    /// # use anonymizedhelibrary::gadget_product::*;
    /// let rns_base = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    /// let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(16);
    /// let ring = ManagedDoubleRNSRingBase::new(number_ring, zn_rns::Zn::new(rns_base.clone(), BigIntRing::RING));
    /// let mut rng = oorandom::Rand64::new(1);
    /// // we have digits == rns_base.len(), so the gadget vector has entries exactly the "CRT unit vectors" ei with ei = 1 mod pi, ei = 0 mod pj for j != i
    /// let digits = 3;
    /// 
    /// // build the right-hand side operand
    /// let rhs = ring.random_element(|| rng.rand_u64());
    /// let mut rhs_op = RNSGadgetProductRhsOperand::new(ring.get_ring(), digits);
    /// for i in 0..3 {
    ///     // set the i-th component to `gadget_vector(i) * rhs`, for now without noise
    ///     let component_at_i = ring.inclusion().mul_ref_map(&rhs, &rhs_op.gadget_vector(ring.get_ring()).at(i));
    ///     rhs_op.set_rns_factor(ring.get_ring(), i, component_at_i);
    /// }
    /// 
    /// // compute the gadget product
    /// let lhs = ring.random_element(|| rng.rand_u64());
    /// let lhs_op = RNSGadgetProductLhsOperand::from_element(ring.get_ring(), &lhs, digits);
    /// let actual = lhs_op.gadget_product(&rhs_op, ring.get_ring());
    /// assert_el_eq!(&ring, &ring.mul_ref(&lhs, &rhs), actual);
    /// ```
    /// To demonstrate how this keeps small error terms small, consider the following variation of the previous example:
    /// ```
    /// # use feanor_math::ring::*;
    /// # use feanor_math::assert_el_eq;
    /// # use feanor_math::homomorphism::*;
    /// # use feanor_math::rings::zn::*;
    /// # use feanor_math::rings::zn::zn_64::*;
    /// # use feanor_math::rings::finite::*;
    /// # use feanor_math::rings::extension::FreeAlgebra;
    /// # use feanor_math::integer::*;
    /// # use feanor_math::primitive_int::StaticRing;
    /// # use feanor_math::algorithms::fft::cooley_tuckey::CooleyTuckeyFFT;
    /// # use feanor_math::rings::extension::FreeAlgebraStore;
    /// # use feanor_math::seq::*;
    /// # use anonymizedhelibrary::ciphertext_ring::double_rns_managed::*;
    /// # use anonymizedhelibrary::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
    /// # use anonymizedhelibrary::gadget_product::*;
    /// # let rns_base = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    /// # let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(16);
    /// # let ring = ManagedDoubleRNSRingBase::new(number_ring, zn_rns::Zn::new(rns_base.clone(), BigIntRing::RING));
    /// # let mut rng = oorandom::Rand64::new(1);
    /// # let digits = 3;
    /// // build the ring just as before
    /// let rhs = ring.random_element(|| rng.rand_u64());
    /// let mut rhs_op = RNSGadgetProductRhsOperand::new(ring.get_ring(), digits);
    /// // this time include some error when building `rhs_op`
    /// let mut create_small_error = || ring.get_ring().from_canonical_basis((0..ring.rank()).map(|i| ring.base_ring().int_hom().map((rng.rand_u64() % 3) as i32 - 1)));
    /// for i in 0..3 {
    ///     // set the i-th component to `gadget_vector(i) * rhs`, with possibly some error included
    ///     let component_at_i = ring.inclusion().mul_ref_map(&rhs, &rhs_op.gadget_vector(ring.get_ring()).at(i));
    ///     rhs_op.set_rns_factor(ring.get_ring(), i, ring.add(component_at_i, create_small_error()));
    /// }
    /// 
    /// // compute the gadget product
    /// let lhs = ring.random_element(|| rng.rand_u64());
    /// let lhs_op = RNSGadgetProductLhsOperand::from_element(ring.get_ring(), &lhs, digits);
    /// let actual = lhs_op.gadget_product(&rhs_op, ring.get_ring());
    /// 
    /// // the final result should be close to `lhs * rhs`, except for some noise
    /// let expected = ring.mul_ref(&lhs, &rhs);
    /// let error = ring.sub(expected, actual);
    /// let error_coefficients = ring.wrt_canonical_basis(&error);
    /// let max_allowed_error = (113 / 2) * 8 * 3;
    /// assert!((0..8).all(|i| int_cast(ring.base_ring().smallest_lift(error_coefficients.at(i)), StaticRing::<i64>::RING, BigIntRing::RING).abs() <= max_allowed_error));
    /// ```
    /// 
    pub fn gadget_product(&self, rhs: &RNSGadgetProductRhsOperand<R>, ring: &R) -> R::Element {
        assert_eq!(self.element_decomposition.len(), rhs.scaled_element.len(), "Gadget product operands created w.r.t. different digit sets");
        return ring.inner_product_prepared(
            self.element_decomposition.iter().zip(rhs.scaled_element.iter())
                .filter_map(|((lhs_prep, lhs), rhs)| rhs.as_ref().map(|(rhs_prep, rhs)| (lhs, lhs_prep, rhs, rhs_prep)))
                .collect::<Vec<_>>()
        );
    }
}
 
fn gadget_decompose<R, S, V>(ring: &R, el: &R::Element, digits: V, out_ring: &S) -> Vec<(S::PreparedMultiplicant, S::Element)>
    where R: BGFVCiphertextRing,
        S: BGFVCiphertextRing,
        V: VectorFn<Range<usize>>
{
    assert!(digits.iter().all(|digit| digit.end <= ring.base_ring().len()));
    let ZZi64 = StaticRing::<i64>::RING;
    let mut result = Vec::new();
    let mut el_as_matrix = OwnedMatrix::zero(ring.base_ring().len(), ring.small_generating_set_len(), ring.base_ring().at(0));
    ring.as_representation_wrt_small_generating_set(el, el_as_matrix.data_mut());
    
    let homs = out_ring.base_ring().as_iter().map(|Zp| Zp.can_hom(&ZZi64).unwrap()).collect::<Vec<_>>();
    let mut current_row = Vec::new();
    current_row.resize_with(homs.len() * el_as_matrix.col_count(), || out_ring.base_ring().at(0).zero());
    let mut current_row = SubmatrixMut::from_1d(&mut current_row[..], homs.len(), el_as_matrix.col_count());
    
    for i in 0..digits.len() {
        
        let digit = digits.at(i);
        let conversion = GadgetProductBaseConversion::new_with_alloc(
            digit.iter().map(|idx| *ring.base_ring().at(idx)).collect::<Vec<_>>(),
            homs.iter().map(|h| **h.codomain()).collect::<Vec<_>>(),
            Global
        );
        
        conversion.apply(
            el_as_matrix.data().restrict_rows(digit.clone()),
            current_row.reborrow()
        );

        let decomposition_part = out_ring.from_representation_wrt_small_generating_set(current_row.as_const());
        result.push((
            out_ring.prepare_multiplicant(&decomposition_part),
            decomposition_part
        ));
    }
    return result;
}

fn gadget_decompose_doublerns<NumberRing, A, V>(ring: &DoubleRNSRingBase<NumberRing, A>, el: &SmallBasisEl<NumberRing, A>, digits: V) -> Vec<(<DoubleRNSRingBase<NumberRing, A> as PreparedMultiplicationRing>::PreparedMultiplicant, El<DoubleRNSRing<NumberRing, A>>)>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone,
        V: VectorFn<Range<usize>>
{
    let ZZi64 = StaticRing::<i64>::RING;
    let mut result = Vec::new();
    let el_as_matrix = ring.as_matrix_wrt_small_basis(el);
    let homs = ring.base_ring().as_iter().map(|Zp| Zp.can_hom(&ZZi64).unwrap()).collect::<Vec<_>>();
    
    for i in 0..digits.len() {
        
        let digit = digits.at(i);
        let conversion = GadgetProductBaseConversion::new_with_alloc(
            digit.iter().map(|idx| *ring.base_ring().at(idx)).collect::<Vec<_>>(),
            homs.iter().map(|h| **h.codomain()).collect::<Vec<_>>(),
            Global
        );
        
        let mut decomposition_part = ring.zero_non_fft();
        conversion.apply(
            el_as_matrix.restrict_rows(digit.clone()),
            ring.as_matrix_wrt_small_basis_mut(&mut decomposition_part)
        );

        let decomposition_part = ring.do_fft(decomposition_part);
        result.push((
            ring.prepare_multiplicant(&decomposition_part),
            decomposition_part
        ));
    }
    return result;
}

///
/// Represents the right-hand side operand of a gadget product.
/// 
/// In other words, this stores a multiple "noisy" approximations to a `g[i] * x`, for
/// a ring element `x` and a gadget vector `g`. The only supported gadget vectors
/// are RNS-based gadget vectors, see [`RNSGadgetProductRhsOperand::gadget_vector_digits()`].
/// 
/// For more details, see [`RNSGadgetProductLhsOperand::gadget_product()`].
/// 
pub struct RNSGadgetProductRhsOperand<R: PreparedMultiplicationRing> {
    /// `i`-th entry stores a (noisy) encryption/encoding/whatever of the represented element,
    /// scaled by the `i`-th entry of the gadget vector. `None` represents zero. We store the
    /// element once as `PreparedMultiplicant` for fast computation of gadget products, and once
    /// as the element itself, since there currently is no way of getting the ring element out of
    /// a `PreparedMultiplicant`
    scaled_element: Vec<Option<(R::PreparedMultiplicant, R::Element)>>,
    /// representation of the used gadget vector, the `i`-th entry of the gadget vector is the
    /// RNS unit vector that is 1 modulo exactly the RNS factors contained in the digit at index
    /// `i` of this list
    digits: Box<RNSGadgetVectorDigitIndices>
}

impl<R: PreparedMultiplicationRing> RNSGadgetProductRhsOperand<R> {

    pub fn clone(&self, ring: &R) -> Self {
        Self {
            scaled_element: self.scaled_element.iter().map(|el| el.as_ref().map(|el| (ring.prepare_multiplicant(&el.1), ring.clone_el(&el.1)))).collect(),
            digits: self.digits.clone()
        }
    }

    ///
    /// Returns the gadget vector `g` that this gadget product operand has been created for.
    /// 
    /// More concretely, the returned vectors `g` consists of values of `Z/(q)`, and this
    /// gadget product operand then stored `g[i] * x` for all `i` and a ring element `x`. The
    /// gadget vector should have the propery that any ring element `y` can be represented as
    /// a linear combination `sum_i g[i] * y[i]` with small ring elements `y[i]`.
    /// 
    pub fn gadget_vector<'b>(&'b self, ring: &'b R) -> impl VectorFn<El<zn_rns::Zn<Zn, BigIntRing>>> + use<'b, R>
        where R: RingExtension,
            R::BaseRing: RingStore<Type = zn_rns::ZnBase<zn_64::Zn, BigIntRing>>
    {
        self.gadget_vector_digits().map_fn(|digit| ring.base_ring().get_ring().from_congruence((0..ring.base_ring().get_ring().len()).map(|i| if digit.contains(&i) {
            ring.base_ring().get_ring().at(i).one()
        } else {
            ring.base_ring().get_ring().at(i).zero()
        })))
    }

    ///
    /// Returns the RNS factor indices that correspond to each entry of the underlying
    /// gadget vector.
    /// 
    /// More concretely, [`RNSGadgetProductLhsOperand`] and [`RNSGadgetProductRhsOperand`] use
    /// gadget vectors that are based on the RNS representation of `q = p1 ... pr`. In other
    /// words, the gadget vector `g` is defined as
    /// ```text
    ///   g[i] = 1 mod pj    if j in digits[i]
    ///   g[i] = 0 mod pj    otherwise
    /// ```
    /// where `digits` is the vector of ranges that is returned by this function.
    /// 
    /// For some more details, see [`RNSGadgetVectorDigitIndices`].
    /// 
    pub fn gadget_vector_digits<'b>(&'b self) -> &'b RNSGadgetVectorDigitIndices {
        &self.digits
    }

    ///
    /// Sets the noisy approximation to `g[i] * x` to the given element.
    /// 
    /// This will change the element represented by this [`RNSGadgetProductRhsOperand`].
    /// 
    pub fn set_rns_factor(&mut self, ring: &R, i: usize, el: R::Element) {
        self.scaled_element[i] = Some((ring.prepare_multiplicant(&el), el));
    }
    
    ///
    /// Returns the noisy approximation to `g[i] * x`, if it was previously set
    /// via [`RNSGadgetProductRhsOperand::set_rns_factor()`].
    /// 
    pub fn get_rns_factor<'a>(&'a self, _ring: &R, i: usize) -> Option<&'a R::Element> {
        self.scaled_element[i].as_ref().map(|(_, x)| x)
    }

    /// 
    /// Creates a [`RNSGadgetProductRhsOperand`] representing `0` w.r.t. the RNS-based gadget vector that has `digits` digits.
    /// 
    /// For an explanation of gadget products, see [`RNSGadgetProductLhsOperand::gadget_product()`].
    /// 
    pub fn new(ring: &R, digits: usize) -> Self 
        where R: RingExtension,
            R::BaseRing: RingStore<Type = zn_rns::ZnBase<zn_64::Zn, BigIntRing>>
    {
        Self::new_with_digits(ring, RNSGadgetVectorDigitIndices::select_digits(digits, ring.base_ring().get_ring().len()))
    }

    /// 
    /// Creates a [`RNSGadgetProductRhsOperand`] representing `0` w.r.t. the RNS-based gadget vector given by `digits`.
    /// For the exact description how the gadget vector is constructed based on `digits`, see 
    /// [`RNSGadgetProductRhsOperand::gadget_vector_digits()`].
    /// 
    /// For an explanation of gadget products, see [`RNSGadgetProductLhsOperand::gadget_product()`].
    /// 
    pub fn new_with_digits(_ring: &R, digits: Box<RNSGadgetVectorDigitIndices>) -> Self 
        where R: RingExtension,
            R::BaseRing: RingStore<Type = zn_rns::ZnBase<zn_64::Zn, BigIntRing>>
    {
        assert!(digits.iter().all(|digit| digit.end > digit.start));
        let mut operands = Vec::with_capacity(digits.len());
        operands.extend((0..digits.len()).map(|_| None));
        return Self {
            scaled_element: operands,
            digits: digits
        };
    }
}

impl<R: BGFVCiphertextRing> RNSGadgetProductRhsOperand<R> {

    pub fn modulus_switch(&self, to: &R, dropped_rns_factors: &RNSFactorIndexList, from: &R) -> Self {
        assert_eq!(to.base_ring().get_ring().len() + dropped_rns_factors.len(), from.base_ring().get_ring().len());
        debug_assert_eq!(self.digits.len(), self.scaled_element.len());
        let mut result_scaled_el = Vec::new();
        for (digit, scaled_el) in self.digits.iter().zip(self.scaled_element.iter()) {
            let old_digit_len = digit.end - digit.start;
            let dropped_from_digit = dropped_rns_factors.num_within(&digit);
            assert!(dropped_from_digit <= old_digit_len);
            if dropped_from_digit == old_digit_len {
                continue;
            }
            if let Some((scaled_el_prepared, scaled_el)) = scaled_el {
                let new_scaled_el = to.drop_rns_factor_element(from, dropped_rns_factors, scaled_el);
                result_scaled_el.push(Some((to.drop_rns_factor_prepared_element(from, dropped_rns_factors, scaled_el_prepared), new_scaled_el)));
            } else {
                result_scaled_el.push(None);
            }
        }
        return Self {
            digits: self.digits.remove_indices(dropped_rns_factors),
            scaled_element: result_scaled_el
        };
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::ciphertext_ring::single_rns_ring::SingleRNSRingBase;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use crate::DefaultConvolution;

#[test]
fn test_gadget_decomposition() {
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(4);
    let ring = SingleRNSRingBase::<_, Global, DefaultConvolution>::new(number_ring, zn_rns::Zn::create_from_primes(vec![17, 97, 113], BigIntRing::RING));
    let rns_base = ring.base_ring();
    let from_congruence = |data: &[i32]| rns_base.from_congruence(data.iter().enumerate().map(|(i, c)| rns_base.at(i).int_hom().map(*c)));
    let hom_i32 = ring.base_ring().can_hom(&StaticRing::<i32>::RING).unwrap();

    let mut rhs = RNSGadgetProductRhsOperand::new(ring.get_ring(), 2);
    rhs.set_rns_factor(ring.get_ring(), 0, ring.inclusion().map(from_congruence(&[1, 1, 0])));
    rhs.set_rns_factor(ring.get_ring(), 1, ring.inclusion().map(from_congruence(&[0, 0, 1])));

    let lhs = RNSGadgetProductLhsOperand::from_element(ring.get_ring(), &ring.inclusion().map(hom_i32.map(1000)), 2);

    assert_el_eq!(ring, ring.inclusion().map(hom_i32.map(1000)), lhs.gadget_product(&rhs, ring.get_ring()));
}

#[test]
fn test_modulus_switch() {
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(4);
    let ring = SingleRNSRingBase::<_, Global, DefaultConvolution>::new(number_ring.clone(), zn_rns::Zn::create_from_primes(vec![17, 97, 113], BigIntRing::RING));
    let rns_base = ring.base_ring();
    let from_congruence = |data: &[i32]| rns_base.from_congruence(data.iter().enumerate().map(|(i, c)| rns_base.at(i).int_hom().map(*c)));

    let mut rhs = RNSGadgetProductRhsOperand::new(ring.get_ring(), 2);
    rhs.set_rns_factor(ring.get_ring(), 0, ring.inclusion().map(from_congruence(&[1, 1, 0])));
    rhs.set_rns_factor(ring.get_ring(), 1, ring.inclusion().map(from_congruence(&[0, 0, 1])));

    let smaller_ring = SingleRNSRingBase::<_, Global, DefaultConvolution>::new(number_ring.clone(), zn_rns::Zn::create_from_primes(vec![17, 113], BigIntRing::RING));
    let rhs = rhs.modulus_switch(smaller_ring.get_ring(), RNSFactorIndexList::from_ref(&[1], rns_base.len()), ring.get_ring());
    let lhs = RNSGadgetProductLhsOperand::from_element(smaller_ring.get_ring(), &smaller_ring.int_hom().map(1000), 2);

    assert_el_eq!(&smaller_ring, smaller_ring.int_hom().map(1000), lhs.gadget_product(&rhs, smaller_ring.get_ring()));

    let ring = SingleRNSRingBase::<_, Global, DefaultConvolution>::new(number_ring.clone(), zn_rns::Zn::create_from_primes(vec![17, 97, 113, 193, 241], BigIntRing::RING));
    let rns_base = ring.base_ring();
    let from_congruence = |data: &[i32]| rns_base.from_congruence(data.iter().enumerate().map(|(i, c)| rns_base.at(i).int_hom().map(*c)));

    let mut rhs = RNSGadgetProductRhsOperand::new(ring.get_ring(), 3);
    rhs.set_rns_factor(ring.get_ring(), 0, ring.inclusion().map(from_congruence(&[1000, 1000, 0, 0, 0])));
    rhs.set_rns_factor(ring.get_ring(), 1, ring.inclusion().map(from_congruence(&[0, 0, 1000, 1000, 0])));
    rhs.set_rns_factor(ring.get_ring(), 2, ring.inclusion().map(from_congruence(&[0, 0, 0, 0, 1000])));

    let smaller_ring = SingleRNSRingBase::<_, Global, DefaultConvolution>::new(number_ring, zn_rns::Zn::create_from_primes(vec![17, 193, 241], BigIntRing::RING));
    let rhs = rhs.modulus_switch(smaller_ring.get_ring(), RNSFactorIndexList::from_ref(&[1, 2], rns_base.len()), ring.get_ring());
    let lhs = RNSGadgetProductLhsOperand::from_element(smaller_ring.get_ring(), &smaller_ring.int_hom().map(1000), 3);

    assert_el_eq!(&smaller_ring, smaller_ring.int_hom().map(1000000), lhs.gadget_product(&rhs, smaller_ring.get_ring()));
}