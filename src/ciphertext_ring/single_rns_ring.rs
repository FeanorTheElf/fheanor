use std::alloc::{Allocator, Global};
use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::Arc;

use feanor_math::algorithms::convolution::ntt::NTTConvolution;
use feanor_math::algorithms::convolution::*;
use feanor_math::iters::{multi_cartesian_product, MultiProduct};
use feanor_math::primitive_int::*;
use feanor_math::serialization::*;
use feanor_math::specialization::{FiniteRingOperation, FiniteRingSpecializable};
use feanor_math::ring::*;
use feanor_math::homomorphism::*;
use feanor_math::integer::*;
use feanor_math::rings::extension::*;
use feanor_math::rings::finite::{FiniteRing, FiniteRingStore};
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::seq::*;
use feanor_math::matrix::*;

use serde::Serialize;
use serde::de::DeserializeSeed;
use tracing::instrument;

use crate::number_ring::HECyclotomicNumberRing;
use crate::ciphertext_ring::poly_remainder::CyclotomicPolyReducer;
use crate::cyclotomic::*;
use crate::ciphertext_ring::double_rns_ring::DoubleRNSRingBase;
use crate::ntt::HERingConvolution;

use super::serialization::{deserialize_rns_data, serialize_rns_data};
use super::{BGFVCiphertextRing, PreparedMultiplicationRing};

///
/// Implementation of the ring `Z[𝝵_n]/(q)`, where `q = p1 ... pr` is a product of "RNS factors".
/// Elements are stored in single-RNS-representation, using NTTs for multiplication.
/// 
/// As opposed to [`DoubleRNSRing`], this means multiplications are more expensive, but non-arithmetic
/// operations like [`FreeAlgebra::wrt_canonical_basis()`] or [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`]
/// are faster. Note that repeated multiplications with a fixed element will get significantly faster when using
/// [`PreparedMultiplicationRing::prepare_multiplicant()`] and [`PreparedMultiplicationRing::mul_prepared()`].
///  
/// # Mathematical details
/// 
/// Elements are stored as polynomials, with coefficients represented w.r.t. this RNS base.
/// In other words, the coefficients are stored by their cosets modulo each `pi`. Multiplication
/// is done by computing the convolution of coefficients with the configured convolution algorithm,
/// followed by a reduction modulo `Phi_n` (or rather `X^n - 1`, see below).
/// 
/// Furthermore, we currently store polynomials of degree `< n` (instead of degree `< phi(n) = deg(Phi_n)`) 
/// to avoid expensive polynomial division by `Phi_n` (polynomial division by `X^n - 1` is very cheap).
/// The reduction modulo `Phi_n` is only done when necessary, e.g. in [`RingBase::eq_el()`] or
/// in [`SingleRNSRingBase::to_matrix()`].
/// 
/// # Why require `NumberRing` to be cyclotomic?
/// 
/// Because otherwise I haven't thought about how to efficiently perform reductions modulo the
/// generating polynomial of the number ring. In particular, for cyclotomic rings, we can just reduce
/// modulo `X^n - 1` (and only compute the full reduction modulo `Phi_n(X)` when necessary), which
/// is extremely cheap. I don't know if there is something similar that we can do for general number
/// rings.
/// 
pub struct SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    number_ring: NumberRing,
    element_allocator: A,
    rns_base: zn_rns::Zn<Zn, BigIntRing>,
    /// Convolution algorithms to use to compute convolutions over each `Fp` in the RNS base
    convolutions: Vec<Arc<C>>,
    /// Used to compute the polynomial division by `Phi_n` when necessary
    poly_moduli: Vec<Arc<CyclotomicPolyReducer<Zn, Arc<C>>>>
}

///
/// [`RingStore`] for [`SingleRNSRingBase`]
/// 
pub type SingleRNSRing<NumberRing, A = Global, C = NTTConvolution<Zn, Global>> = RingValue<SingleRNSRingBase<NumberRing, A, C>>;

///
/// Type of elements of [`SingleRNSRingBase`]
/// 
pub struct SingleRNSRingEl<NumberRing, A, C>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnBase>
{
    /// we allow coefficients up to `n` (and not `phi(n)`) to avoid intermediate reductions modulo `Phi_n`
    coefficients: Vec<ZnEl, A>,
    convolutions: PhantomData<C>,
    number_ring: PhantomData<NumberRing>
}

pub struct SingleRNSRingPreparedMultiplicant<NumberRing, A, C>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    pub(super) element: PhantomData<SingleRNSRingEl<NumberRing, A, C>>,
    pub(super) number_ring: PhantomData<NumberRing>,
    pub(super) data: Vec<C::PreparedConvolutionOperand, A>
}

impl<NumberRing, C> SingleRNSRingBase<NumberRing, Global, C> 
    where NumberRing: HECyclotomicNumberRing,
        C: HERingConvolution<Zn>
{
    ///
    /// Creates a new [`SingleRNSRing`].
    /// 
    /// It must be possible to create a convolution of type `C` for each RNS factors 
    /// `Z/(pi)` in `rns_base`.
    /// 
    #[instrument(skip_all)]
    pub fn new(number_ring: NumberRing, rns_base: zn_rns::Zn<Zn, BigIntRing>) -> RingValue<Self> {
        let max_log2_n = StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.n() as i64 * 2)).unwrap();
        let convolutions = rns_base.as_iter().map(|Zp| Arc::new(C::new(Zp.clone(), max_log2_n))).collect();
        Self::new_with(number_ring, rns_base, Global, convolutions)
    }
}

impl<NumberRing, A, C> Clone for SingleRNSRingBase<NumberRing, A, C>
    where NumberRing: HECyclotomicNumberRing + Clone,
        A: Allocator + Clone,
        C: HERingConvolution<Zn>
{
    fn clone(&self) -> Self {
        Self {
            rns_base: self.rns_base.clone(),
            element_allocator: self.element_allocator.clone(),
            number_ring: self.number_ring.clone(),
            convolutions: self.convolutions.clone(),
            poly_moduli: self.poly_moduli.clone()
        }
    }
}

impl<NumberRing, A, C> SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    ///
    /// Creates a new [`SingleRNSRing`].
    /// 
    /// The list of convolutions `convolutions` must contain one convolution for each RNS factor
    /// `Z/(pi)` in `rns_base`. If there is one convolution object that supports computing convolutions
    /// over every `Z/(pi)` (like [`STANDARD_CONVOLUTION`]), `convolutions` should contain multiple `Arc`s 
    /// all pointing to this one convolution object.
    /// 
    #[instrument(skip_all)]
    pub fn new_with(number_ring: NumberRing, rns_base: zn_rns::Zn<Zn, BigIntRing>, allocator: A, convolutions: Vec<Arc<C>>) -> RingValue<Self> {
        assert!(rns_base.len() > 0);
        assert_eq!(rns_base.len(), convolutions.len());
        for i in 0..rns_base.len() {
            assert!(convolutions[i].supports_ring(rns_base.at(i)));
        }
        
        RingValue::from(Self {
            poly_moduli: rns_base.as_iter().zip(convolutions.iter()).map(|(Zp, conv)| CyclotomicPolyReducer::new(*Zp, number_ring.n() as i64, conv.clone())).map(Arc::new).collect::<Vec<_>>(),
            rns_base: rns_base,
            element_allocator: allocator,
            number_ring: number_ring,
            convolutions: convolutions,
        })
    }

    ///
    /// Performs reduction modulo `X^n - 1`.
    /// 
    #[instrument(skip_all)]
    pub(super) fn reduce_modulus_partly(&self, k: usize, buffer: &mut [ZnEl], output: &mut [ZnEl]) {
        assert_eq!(self.n(), output.len());
        let Zp = self.base_ring().at(k);
                for i in 0..self.n() {
            output[i] = Zp.sum((i..buffer.len()).step_by(self.n()).map(|j| buffer[j]));
        }
    }

    ///
    /// Performs reduction modulo `Phi_n`.
    /// 
    #[instrument(skip_all)]
    pub(super) fn reduce_modulus_complete(&self, el: &mut SingleRNSRingEl<NumberRing, A, C>) {
        let mut el_matrix = self.coefficients_as_matrix_mut(el);
        for k in 0..self.base_ring().len() {
            self.poly_moduli[k].remainder(el_matrix.row_mut_at(k));
        }
    }

    fn check_valid(&self, el: &SingleRNSRingEl<NumberRing, A, C>) {
        assert_eq!(self.n() as usize * self.base_ring().len(), el.coefficients.len());
    }

    pub(super) fn coefficients_as_matrix<'a>(&self, element: &'a SingleRNSRingEl<NumberRing, A, C>) -> Submatrix<'a, AsFirstElement<ZnEl>, ZnEl> {
        Submatrix::from_1d(&element.coefficients, self.base_ring().len(), self.n())
    }

    pub(super) fn coefficients_as_matrix_mut<'a>(&self, element: &'a mut SingleRNSRingEl<NumberRing, A, C>) -> SubmatrixMut<'a, AsFirstElement<ZnEl>, ZnEl> {
        SubmatrixMut::from_1d(&mut element.coefficients, self.base_ring().len(), self.n())
    }

    pub fn to_matrix<'a>(&self, element: &'a mut SingleRNSRingEl<NumberRing, A, C>) -> Submatrix<'a, AsFirstElement<ZnEl>, ZnEl> {
        self.reduce_modulus_complete(element);
        return self.coefficients_as_matrix(element).restrict_cols(0..self.rank());
    }

    pub fn allocator(&self) -> &A {
        &self.element_allocator
    }

    pub fn convolutions<'a>(&'a self) -> impl VectorFn<&'a C> + use<'a, NumberRing, A, C> {
        self.convolutions.as_fn().map_fn(|conv| &**conv)
    }
}

impl<NumberRing, A, C> PreparedMultiplicationRing for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    type PreparedMultiplicant = SingleRNSRingPreparedMultiplicant<NumberRing, A, C>;

    #[instrument(skip_all)]
    fn prepare_multiplicant(&self, el: &SingleRNSRingEl<NumberRing, A, C>) -> SingleRNSRingPreparedMultiplicant<NumberRing, A, C> {
        let el_as_matrix = self.coefficients_as_matrix(el);
        let mut result = Vec::new_in(self.allocator().clone());
        result.extend(self.base_ring().as_iter().enumerate().map(|(i, Zp)| self.convolutions[i].prepare_convolution_operand(el_as_matrix.row_at(i), Zp)));
        SingleRNSRingPreparedMultiplicant {
            element: PhantomData,
            data: result,
            number_ring: PhantomData
        }
    }

    #[instrument(skip_all)]
    fn mul_prepared(&self, lhs: &SingleRNSRingPreparedMultiplicant<NumberRing, A, C>, rhs: &SingleRNSRingPreparedMultiplicant<NumberRing, A, C>) -> SingleRNSRingEl<NumberRing, A, C> {
        let mut unreduced_result = Vec::with_capacity_in(2 * self.n(), self.allocator());
        let mut result = self.zero();
        
        for k in 0..self.base_ring().len() {
            let Zp = self.base_ring().at(k);
            unreduced_result.clear();
            unreduced_result.resize_with(self.n() * 2, || Zp.zero());
            
            self.convolutions[k].compute_convolution_prepared(
                rhs.data.at(k),
                lhs.data.at(k),
                &mut unreduced_result,
                Zp
            );
            self.reduce_modulus_partly(k, &mut unreduced_result, self.coefficients_as_matrix_mut(&mut result).row_mut_at(k));
        }
        return result;
    }

    #[instrument(skip_all)]
    fn inner_product_prepared<'a, I>(&self, parts: I) -> Self::Element
        where I: IntoIterator<Item = (&'a Self::PreparedMultiplicant, &'a Self::PreparedMultiplicant)>,
            Self: 'a
    {
        let mut result = self.zero();
        let mut unreduced_result = Vec::with_capacity_in(2 * self.n(), self.allocator());
        let parts = parts.into_iter().collect::<Vec<_>>();
        for k in 0..self.base_ring().len() {
            let Zp = self.base_ring().at(k);
            unreduced_result.clear();
            unreduced_result.resize_with(self.n() * 2, || Zp.zero());
            self.convolutions[k].compute_convolution_inner_product_prepared(parts.iter().copied().map(|(lhs, rhs)| (&lhs.data[k], &rhs.data[k])), &mut unreduced_result, Zp);
            self.reduce_modulus_partly(k, &mut unreduced_result, self.coefficients_as_matrix_mut(&mut result).row_mut_at(k));
        }
        return result;
    }
}

impl<NumberRing, A, C> BGFVCiphertextRing for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    type NumberRing = NumberRing;
    
    fn number_ring(&self) -> &NumberRing {
        &self.number_ring
    }

    #[instrument(skip_all)]
    fn drop_rns_factor(&self, drop_rns_factors: &[usize]) -> Self {
        Self {
            rns_base: zn_rns::Zn::new(self.base_ring().as_iter().enumerate().filter(|(i, _)| !drop_rns_factors.contains(i)).map(|(_, x)| x.clone()).collect(), BigIntRing::RING),
            element_allocator: self.allocator().clone(),
            number_ring: self.number_ring.clone(),
            convolutions: self.convolutions.iter().enumerate().filter(|(i, _)| !drop_rns_factors.contains(i)).map(|(_, conv)| conv.clone()).collect(),
            poly_moduli: self.poly_moduli.iter().enumerate().filter(|(i, _)| !drop_rns_factors.contains(i)).map(|(_, modulus)| modulus.clone()).collect()
        }
    }

    #[instrument(skip_all)]
    fn drop_rns_factor_element(&self, from: &Self, drop_factors: &[usize], value: Self::Element) -> Self::Element {
        assert_eq!(self.n(), from.n());
        assert_eq!(self.base_ring().len() + drop_factors.len(), from.base_ring().len());
        assert!(drop_factors.iter().all(|i| *i < from.base_ring().len()));

        let mut result = self.zero();
        let mut result_as_matrix = self.coefficients_as_matrix_mut(&mut result);
        debug_assert_eq!(self.base_ring().len(), result_as_matrix.row_count());
        debug_assert_eq!(self.n(), result_as_matrix.col_count());

        let value_as_matrix = from.coefficients_as_matrix(&value);
        debug_assert_eq!(from.base_ring().len(), value_as_matrix.row_count());
        debug_assert_eq!(from.n(), value_as_matrix.col_count());

        let mut i_self = 0;
        for i_from in 0..from.base_ring().len() {
            if drop_factors.contains(&i_from) {
                continue;
            }
            assert!(self.base_ring().at(i_self).get_ring() == from.base_ring().at(i_from).get_ring());
            for j in 0..result_as_matrix.col_count() {
                *result_as_matrix.at_mut(i_self, j) = *value_as_matrix.at(i_from, j);
            }
            i_self += 1;
        }

        return result;
    }

    #[instrument(skip_all)]
    fn drop_rns_factor_prepared(&self, from: &Self, drop_factors: &[usize], value: Self::PreparedMultiplicant) -> Self::PreparedMultiplicant {
        assert_eq!(self.n(), from.n());
        assert_eq!(self.base_ring().len() + drop_factors.len(), from.base_ring().len());
        assert!(drop_factors.iter().all(|i| *i < from.base_ring().len()));
        debug_assert_eq!(from.base_ring().len(), value.data.len());

        let mut result = Vec::with_capacity_in(self.base_ring().len(), self.allocator().clone());
        let mut i_self = 0;
        for (i_from, operand) in value.data.into_iter().enumerate() {
            if drop_factors.contains(&i_from) {
                continue;
            }
            assert!(self.base_ring().at(i_self).get_ring() == from.base_ring().at(i_from).get_ring());
            result.push(operand);
            i_self += 1;
        }

        return SingleRNSRingPreparedMultiplicant {
            data: result,
            element: PhantomData,
            number_ring: PhantomData
        };
    }

    fn small_generating_set_len(&self) -> usize {
        self.n()
    }

    fn as_representation_wrt_small_generating_set<V>(&self, x: &Self::Element, mut output: SubmatrixMut<V, ZnEl>)
        where V: AsPointerToSlice<ZnEl>
    {
        let matrix = self.coefficients_as_matrix(x);
        assert_eq!(output.row_count(), matrix.row_count());
        assert_eq!(output.col_count(), matrix.col_count());
        for i in 0..matrix.row_count() {
            for j in 0..matrix.col_count() {
                *output.at_mut(i, j) = *matrix.at(i, j);
            }
        }
    }

    fn partial_representation_wrt_small_generating_set<V>(&self, x: &Self::Element, row_indices: &[usize], mut output: SubmatrixMut<V, ZnEl>)
        where V: AsPointerToSlice<ZnEl>
    {
        let matrix = self.coefficients_as_matrix(x);
        assert_eq!(output.row_count(), row_indices.len());
        assert_eq!(output.col_count(), matrix.col_count());
        for (i_out, i_in) in row_indices.iter().enumerate() {
            for j in 0..matrix.col_count() {
                *output.at_mut(i_out, j) = *matrix.at(*i_in, j);
            }
        }
    }

    #[instrument(skip_all)]
    fn from_representation_wrt_small_generating_set<V>(&self, data: Submatrix<V, ZnEl>) -> Self::Element
        where V: AsPointerToSlice<ZnEl>
    {
        let mut result = self.zero();
        let mut result_matrix = self.coefficients_as_matrix_mut(&mut result);
        assert_eq!(result_matrix.row_count(), data.row_count());
        assert_eq!(result_matrix.col_count(), data.col_count());
        for i in 0..result_matrix.row_count() {
            let Zp = self.base_ring().at(i);
            for j in 0..result_matrix.col_count() {
                *result_matrix.at_mut(i, j) = Zp.clone_el(data.at(i, j));
            }
        }
        return result;
    }

    #[instrument(skip_all)]
    fn two_by_two_convolution(&self, lhs: [&Self::Element; 2], rhs: [&Self::Element; 2]) -> [Self::Element; 3] {
        enum OwnedOrBorrowed<'a, T> {
            Owned(T),
            Borrowed(&'a T)
        }
        impl<'a, T> Deref for OwnedOrBorrowed<'a, T> {
            type Target = T;
            fn deref(&self) -> &Self::Target {
                match self {
                    Self::Owned(x) => x,
                    Self::Borrowed(x) => *x
                }
            }
        }
        let lhs0_prepared = self.prepare_multiplicant(lhs[0]);
        let lhs1_prepared = if std::ptr::eq(lhs[0], lhs[1]) {
            OwnedOrBorrowed::Borrowed(&lhs0_prepared)
        } else {
            OwnedOrBorrowed::Owned(self.prepare_multiplicant(lhs[1]))
        };
        let rhs0_prepared = if std::ptr::eq(lhs[0], rhs[0]) {
            OwnedOrBorrowed::Borrowed(&lhs0_prepared)
        } else if std::ptr::eq(lhs[1], rhs[0]) {
            OwnedOrBorrowed::Borrowed(&*lhs1_prepared)
        } else {
            OwnedOrBorrowed::Owned(self.prepare_multiplicant(rhs[0]))
        };
        let rhs1_prepared = if std::ptr::eq(lhs[0], rhs[1]) {
            OwnedOrBorrowed::Borrowed(&lhs0_prepared)
        } else if std::ptr::eq(lhs[1], rhs[1]) {
            OwnedOrBorrowed::Borrowed(&*lhs1_prepared)
        } else if std::ptr::eq(rhs[0], rhs[1]) {
            OwnedOrBorrowed::Borrowed(&*rhs0_prepared)
        } else {
            OwnedOrBorrowed::Owned(self.prepare_multiplicant(rhs[1]))
        };
        return [
            self.mul_prepared(&lhs0_prepared, &*rhs0_prepared),
            self.inner_product_prepared([(&lhs0_prepared, &*rhs1_prepared), (&*lhs1_prepared, &*rhs0_prepared)]),
            self.mul_prepared(&*lhs1_prepared, &*rhs1_prepared)
        ];
    }
}

pub struct SingleRNSRingBaseElVectorRepresentation<'a, NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    element: SingleRNSRingEl<NumberRing, A, C>,
    ring: &'a SingleRNSRingBase<NumberRing, A, C>
}

impl<'a, NumberRing, A, C> VectorFn<El<zn_rns::Zn<Zn, BigIntRing>>> for SingleRNSRingBaseElVectorRepresentation<'a, NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    fn len(&self) -> usize {
        self.ring.rank()
    }

    fn at(&self, i: usize) -> El<zn_rns::Zn<Zn, BigIntRing>> {
        assert!(i < self.len());
        self.ring.base_ring().from_congruence(self.ring.coefficients_as_matrix(&self.element).col_at(i).as_iter().enumerate().map(|(i, x)| self.ring.base_ring().at(i).clone_el(x)))
    }
}

impl<NumberRing, A, C> PartialEq for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    fn eq(&self, other: &Self) -> bool {
        self.number_ring() == other.number_ring() && self.base_ring().get_ring() == other.base_ring().get_ring()
    }
}

impl<NumberRing, A, C> RingBase for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing, 
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    type Element = SingleRNSRingEl<NumberRing, A, C>;

    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        self.check_valid(val);
        let mut result = Vec::with_capacity_in(val.coefficients.len(), self.allocator().clone());
        result.extend((0..val.coefficients.len()).map(|i| self.base_ring().at(i / self.n()).clone_el(&val.coefficients[i])));
        SingleRNSRingEl {
            coefficients: result,
            number_ring: PhantomData,
            convolutions: PhantomData
        }
    }

    #[instrument(skip_all)]
    fn add_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        self.check_valid(lhs);
        self.check_valid(rhs);
        let mut lhs_matrix = self.coefficients_as_matrix_mut(lhs);
        let rhs_matrix = self.coefficients_as_matrix(rhs);
        for i in 0..self.base_ring().len() {
            for j in 0..self.n() {
                self.base_ring().at(i).add_assign_ref(lhs_matrix.at_mut(i, j), rhs_matrix.at(i, j));
            }
        }
    }

    fn add_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        self.add_assign_ref(lhs, &rhs);
    }

    #[instrument(skip_all)]
    fn sub_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        self.check_valid(lhs);
        self.check_valid(rhs);
        let mut lhs_matrix = self.coefficients_as_matrix_mut(lhs);
        let rhs_matrix = self.coefficients_as_matrix(rhs);
        for i in 0..self.base_ring().len() {
            for j in 0..self.n() {
                self.base_ring().at(i).sub_assign_ref(lhs_matrix.at_mut(i, j), rhs_matrix.at(i, j));
            }
        }
    }

    #[instrument(skip_all)]
    fn negate_inplace(&self, lhs: &mut Self::Element) {
        self.check_valid(lhs);
        let mut lhs_matrix = self.coefficients_as_matrix_mut(lhs);
        for i in 0..self.base_ring().len() {
            for j in 0..self.n() {
                self.base_ring().at(i).negate_inplace(lhs_matrix.at_mut(i, j));
            }
        }
    }

    fn mul_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        self.mul_assign_ref(lhs, &rhs);
    }

    #[instrument(skip_all)]
    fn mul_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        self.check_valid(lhs);
        self.check_valid(rhs);
        let mut unreduced_result = Vec::with_capacity_in(2 * self.n(), self.allocator());
        
        let rhs_matrix = self.coefficients_as_matrix(rhs);
        let mut lhs_matrix = self.coefficients_as_matrix_mut(lhs);
        for k in 0..self.base_ring().len() {
            let Zp = self.base_ring().at(k);
            unreduced_result.clear();
            unreduced_result.resize_with(self.n() * 2, || Zp.zero());
            
            self.convolutions[k].compute_convolution(
                rhs_matrix.row_at(k),
                lhs_matrix.row_at(k),
                &mut unreduced_result,
                Zp
            );
            self.reduce_modulus_partly(k, &mut unreduced_result, lhs_matrix.row_mut_at(k));
        }
    }
    
    #[instrument(skip_all)]
    fn from_int(&self, value: i32) -> Self::Element {
        self.from(self.base_ring().get_ring().from_int(value))
    }

    #[instrument(skip_all)]
    fn mul_assign_int(&self, lhs: &mut Self::Element, rhs: i32) {
        self.check_valid(lhs);
        let mut lhs_matrix = self.coefficients_as_matrix_mut(lhs);
        for i in 0..self.base_ring().len() {
            let rhs_mod_p = self.base_ring().at(i).get_ring().from_int(rhs);
            for j in 0..self.n() {
                self.base_ring().at(i).mul_assign_ref(lhs_matrix.at_mut(i, j), &rhs_mod_p);
            }
        }
    }

    fn zero(&self) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.n() * self.base_ring().len(), self.allocator().clone());
        result.extend(self.base_ring().as_iter().flat_map(|Zp| (0..self.n()).map(|_| Zp.zero())));
        return SingleRNSRingEl {
            coefficients: result,
            number_ring: PhantomData,
            convolutions: PhantomData
        };
    }

    #[instrument(skip_all)]
    fn eq_el(&self, lhs: &Self::Element, rhs: &Self::Element) -> bool {
        let mut lhs = self.clone_el(lhs);
        let lhs = self.to_matrix(&mut lhs);
        let mut rhs = self.clone_el(rhs);
        let rhs = self.to_matrix(&mut rhs);
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                if !self.base_ring().at(i).eq_el(lhs.at(i, j), rhs.at(i, j)) {
                    return false;
                }
            }
        }
        return true;
    }
    
    fn is_commutative(&self) -> bool { true }
    fn is_noetherian(&self) -> bool { true }
    fn is_approximate(&self) -> bool { false }

    fn dbg_within<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>, env: EnvBindingStrength) -> std::fmt::Result {
        let poly_ring = DensePolyRing::new(self.base_ring(), "X");
        poly_ring.get_ring().dbg_within(&RingRef::new(self).poly_repr(&poly_ring, value, self.base_ring().identity()), out, env)
    }

    fn characteristic<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        self.base_ring().characteristic(ZZ)     
    }
}

impl<NumberRing, A, C> RingExtension for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    type BaseRing = zn_rns::Zn<Zn, BigIntRing>;

    fn base_ring<'a>(&'a self) -> &'a Self::BaseRing {
        &self.rns_base
    }

    #[instrument(skip_all)]
    fn from(&self, x: El<Self::BaseRing>) -> Self::Element {
        let mut result = self.zero();
        let mut result_matrix = self.coefficients_as_matrix_mut(&mut result);
        let x_congruence = self.base_ring().get_congruence(&x);
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            *result_matrix.at_mut(i, 0) = Zp.clone_el(x_congruence.at(i));
        }
        return result;
    }

    #[instrument(skip_all)]
    fn mul_assign_base(&self, lhs: &mut Self::Element, rhs: &El<Self::BaseRing>) {
        let x_congruence = self.base_ring().get_congruence(rhs);
        let mut lhs_matrix = self.coefficients_as_matrix_mut(lhs);
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.n() {
                Zp.mul_assign_ref(lhs_matrix.at_mut(i, j), x_congruence.at(i));
            }
        }
    }
}

impl<NumberRing, A, C> FreeAlgebra for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    type VectorRepresentation<'a> = SingleRNSRingBaseElVectorRepresentation<'a, NumberRing, A, C> 
        where Self: 'a;

        #[instrument(skip_all)]
    fn canonical_gen(&self) -> SingleRNSRingEl<NumberRing, A, C> {
        let mut result = self.zero();
        let mut result_matrix = self.coefficients_as_matrix_mut(&mut result);
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            *result_matrix.at_mut(i, 1) = Zp.one();
        }
        return result;
    }

    fn rank(&self) -> usize {
        self.number_ring().rank()
    }

    #[instrument(skip_all)]
    fn wrt_canonical_basis<'a>(&'a self, el: &'a SingleRNSRingEl<NumberRing, A, C>) -> Self::VectorRepresentation<'a> {
        let mut reduced_el = self.clone_el(el);
        self.reduce_modulus_complete(&mut reduced_el);
        SingleRNSRingBaseElVectorRepresentation {
            ring: self,
            element: reduced_el
        }
    }

    #[instrument(skip_all)]
    fn from_canonical_basis<V>(&self, vec: V) -> SingleRNSRingEl<NumberRing, A, C>
        where V: IntoIterator<Item = El<Self::BaseRing>>
    {
        let mut result = self.zero();
        let mut result_matrix = self.coefficients_as_matrix_mut(&mut result);
        for (j, x) in vec.into_iter().enumerate() {
            assert!(j < self.rank());
            let congruence = self.base_ring().get_ring().get_congruence(&x);
            for i in 0..self.base_ring().len() {
                *result_matrix.at_mut(i, j) = self.base_ring().at(i).clone_el(congruence.at(i));
            }
        }
        return result;
    }
}

impl<NumberRing, A, C> CyclotomicRing for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    fn n(&self) -> usize {
        self.number_ring.n()
    }

    fn galois_group(&self) -> CyclotomicGaloisGroup {
        self.number_ring.galois_group()
    }

    #[instrument(skip_all)]
    fn apply_galois_action(&self, el: &Self::Element, s: CyclotomicGaloisGroupEl) -> Self::Element {
        let Gal = self.galois_group();
        let Gal_Zn = Gal.underlying_ring();
        let s = Gal.to_ring_el(s);
        let mut result = self.zero();
        let mut result_matrix = self.coefficients_as_matrix_mut(&mut result);
        let el_matrix = self.coefficients_as_matrix(el);
        for j in 0..self.n() {
            let in_j = j;
            let out_j: usize = Gal_Zn.smallest_positive_lift(Gal_Zn.mul(s, Gal_Zn.get_ring().from_int_promise_reduced(in_j as i64))).try_into().unwrap();
            for i in 0..self.base_ring().len() {
                *result_matrix.at_mut(i, out_j) = *el_matrix.at(i, in_j);
            }
        }
        return result;
    }
}

pub struct WRTCanonicalBasisElementCreator<'a, NumberRing, A, C>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    ring: &'a SingleRNSRingBase<NumberRing, A, C>
}

impl<'a, 'b, NumberRing, A, C> Clone for WRTCanonicalBasisElementCreator<'a, NumberRing, A, C>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    fn clone(&self) -> Self {
        Self { ring: self.ring }
    }
}

impl<'a, 'b, NumberRing, A, C> Fn<(&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, A, C>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    extern "rust-call" fn call(&self, args: (&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)) -> Self::Output {
        self.ring.from_canonical_basis(args.0.iter().map(|x| self.ring.base_ring().clone_el(x)))
    }
}

impl<'a, 'b, NumberRing, A, C> FnMut<(&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, A, C>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    extern "rust-call" fn call_mut(&mut self, args: (&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)) -> Self::Output {
        self.call(args)
    }
}

impl<'a, 'b, NumberRing, A, C> FnOnce<(&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, A, C>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    type Output = SingleRNSRingEl<NumberRing, A, C>;

    extern "rust-call" fn call_once(self, args: (&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)) -> Self::Output {
        self.call(args)
    }
}

impl<NumberRing, A, C> FiniteRingSpecializable for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    fn specialize<O: FiniteRingOperation<Self>>(op: O) -> Result<O::Output, ()> {
        Ok(op.execute())
    }
}

impl<NumberRing, A, C> SerializableElementRing for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    fn serialize<S>(&self, el: &Self::Element, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        if serializer.is_human_readable() {
            return SerializableNewtype::new("RingEl", SerializableSeq::new(self.wrt_canonical_basis(el).map_fn(|c| SerializeOwnedWithRing::new(c, self.base_ring())))).serialize(serializer);
        } else {
            let mut reduced = self.clone_el(el);
            self.reduce_modulus_complete(&mut reduced);
            let reduced_as_matrix = self.coefficients_as_matrix(&reduced).restrict_cols(0..self.rank());
            return SerializableNewtype::new("SingleRNSEl", &serialize_rns_data(self.base_ring(), reduced_as_matrix)).serialize(serializer);
        }
    }

    fn deserialize<'de, D>(&self, deserializer: D) -> Result<Self::Element, D::Error>
        where D: serde::Deserializer<'de>
    {
        if deserializer.is_human_readable() {
            let data = DeserializeSeedNewtype::new("RingEl", DeserializeSeedSeq::new(
                (0..self.rank()).map(|_| DeserializeWithRing::new(self.base_ring())),
                Vec::with_capacity_in(self.rank(), self.allocator()),
                |mut current, next| { current.push(next); current }
            )).deserialize(deserializer)?;
            if data.len() != self.rank() {
                return Err(serde::de::Error::invalid_length(data.len(), &format!("expected a sequence of {} elements of Z/qZ", self.rank()).as_str()));
            }
            return Ok(self.from_canonical_basis(data.into_iter()));
        } else {
            let mut result = self.zero();
            let result_as_matrix = self.coefficients_as_matrix_mut(&mut result).restrict_cols(0..self.rank());
            DeserializeSeedNewtype::new("SingleRNSEl", deserialize_rns_data(self.base_ring(), result_as_matrix)).deserialize(deserializer)?;
            return Ok(result);
        }
    }
}

impl<NumberRing, A, C> FiniteRing for SingleRNSRingBase<NumberRing, A, C> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone,
        C: PreparedConvolutionAlgorithm<ZnBase>
{
    type ElementsIter<'a> = MultiProduct<
        <zn_rns::ZnBase<Zn, BigIntRing> as FiniteRing>::ElementsIter<'a>, 
        WRTCanonicalBasisElementCreator<'a, NumberRing, A, C>, 
        CloneRingEl<&'a zn_rns::Zn<Zn, BigIntRing>>,
        SingleRNSRingEl<NumberRing, A, C>
    > where Self: 'a;

    fn elements<'a>(&'a self) -> Self::ElementsIter<'a> {
        multi_cartesian_product((0..self.rank()).map(|_| self.base_ring().elements()), WRTCanonicalBasisElementCreator { ring: self }, CloneRingEl(self.base_ring()))
    }

    fn size<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        let modulus = self.base_ring().size(ZZ)?;
        if ZZ.get_ring().representable_bits().is_none() || ZZ.get_ring().representable_bits().unwrap() >= self.rank() * ZZ.abs_log2_ceil(&modulus).unwrap() {
            Some(ZZ.pow(modulus, self.rank()))
        } else {
            None
        }
    }

    fn random_element<G: FnMut() -> u64>(&self, mut rng: G) -> <Self as RingBase>::Element {
        let mut result = self.zero();
        let mut result_matrix = self.coefficients_as_matrix_mut(&mut result);
        for j in 0..self.rank() {
            for i in 0..self.base_ring().len() {
                *result_matrix.at_mut(i, j) = self.base_ring().at(i).random_element(&mut rng);
            }
        }
        return result;
    }
}

impl<NumberRing, A1, A2, C1, C2> CanHomFrom<SingleRNSRingBase<NumberRing, A2, C2>> for SingleRNSRingBase<NumberRing, A1, C1>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C1: PreparedConvolutionAlgorithm<ZnBase>,
        C2: PreparedConvolutionAlgorithm<ZnBase>
{
    type Homomorphism = Vec<<ZnBase as CanHomFrom<ZnBase>>::Homomorphism>;

    fn has_canonical_hom(&self, from: &SingleRNSRingBase<NumberRing, A2, C2>) -> Option<Self::Homomorphism> {
        if self.base_ring().len() == from.base_ring().len() && self.number_ring() == from.number_ring() {
            (0..self.base_ring().len()).map(|i| self.base_ring().at(i).get_ring().has_canonical_hom(from.base_ring().at(i).get_ring()).ok_or(())).collect::<Result<Vec<_>, ()>>().ok()
        } else {
            None
        }
    }

    fn map_in(&self, from: &SingleRNSRingBase<NumberRing, A2, C2>, el: <SingleRNSRingBase<NumberRing, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.map_in_ref(from, &el, hom)
    }

    fn map_in_ref(&self, from: &SingleRNSRingBase<NumberRing, A2, C2>, el: &<SingleRNSRingBase<NumberRing, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        let el_as_matrix = from.coefficients_as_matrix(&el);
        let mut result = self.zero();
        let mut result_matrix = self.coefficients_as_matrix_mut(&mut result);
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.n() {
                *result_matrix.at_mut(i, j) = Zp.get_ring().map_in_ref(from.base_ring().at(i).get_ring(), el_as_matrix.at(i, j), &hom[i]);
            }
        }
        return result;
    }
}

impl<NumberRing, A1, A2, C1> CanHomFrom<DoubleRNSRingBase<NumberRing, A2>> for SingleRNSRingBase<NumberRing, A1, C1>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C1: PreparedConvolutionAlgorithm<ZnBase>
{
    type Homomorphism = <DoubleRNSRingBase<NumberRing, A2> as CanIsoFromTo<Self>>::Isomorphism;

    fn has_canonical_hom(&self, from: &DoubleRNSRingBase<NumberRing, A2>) -> Option<Self::Homomorphism> {
        from.has_canonical_iso(self)
    }

    fn map_in(&self, from: &DoubleRNSRingBase<NumberRing, A2>, el: <DoubleRNSRingBase<NumberRing, A2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        from.map_out(self, el, hom)
    }
}

impl<NumberRing, A1, A2, C1> CanIsoFromTo<DoubleRNSRingBase<NumberRing, A2>> for SingleRNSRingBase<NumberRing, A1, C1>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C1: PreparedConvolutionAlgorithm<ZnBase>
{
    type Isomorphism = <DoubleRNSRingBase<NumberRing, A2> as CanHomFrom<Self>>::Homomorphism;

    fn has_canonical_iso(&self, from: &DoubleRNSRingBase<NumberRing, A2>) -> Option<Self::Isomorphism> {
        from.has_canonical_hom(self)
    }

    fn map_out(&self, from: &DoubleRNSRingBase<NumberRing, A2>, el: Self::Element, iso: &Self::Isomorphism) -> <DoubleRNSRingBase<NumberRing, A2> as RingBase>::Element {
        from.map_in(self, el, iso)
    }
}

impl<NumberRing, A1, A2, C1, C2> CanIsoFromTo<SingleRNSRingBase<NumberRing, A2, C2>> for SingleRNSRingBase<NumberRing, A1, C1>
    where NumberRing: HECyclotomicNumberRing, 
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C1: PreparedConvolutionAlgorithm<ZnBase>,
        C2: PreparedConvolutionAlgorithm<ZnBase>
{
    type Isomorphism = Vec<<ZnBase as CanIsoFromTo<ZnBase>>::Isomorphism>;

    fn has_canonical_iso(&self, from: &SingleRNSRingBase<NumberRing, A2, C2>) -> Option<Self::Isomorphism> {
        if self.base_ring().len() == from.base_ring().len() && self.number_ring() == from.number_ring() {
            (0..self.base_ring().len()).map(|i| self.base_ring().at(i).get_ring().has_canonical_iso(from.base_ring().at(i).get_ring()).ok_or(())).collect::<Result<Vec<_>, ()>>().ok()
        } else {
            None
        }
    }

    fn map_out(&self, from: &SingleRNSRingBase<NumberRing, A2, C2>, el: Self::Element, iso: &Self::Isomorphism) -> <SingleRNSRingBase<NumberRing, A2, C2> as RingBase>::Element {
        let el_as_matrix = self.coefficients_as_matrix(&el);
        let mut result = from.zero();
        let mut result_matrix = from.coefficients_as_matrix_mut(&mut result);
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.n() {
                *result_matrix.at_mut(i, j) = Zp.get_ring().map_out(from.base_ring().at(i).get_ring(), Zp.clone_el(el_as_matrix.at(i, j)), &iso[i]);
            }
        }
        return result;
    }
}

#[cfg(test)]
use crate::number_ring::odd_cyclotomic::OddCyclotomicNumberRing;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
#[cfg(test)]
use feanor_math::rings::poly::PolyRingStore;
#[cfg(test)]
use crate::number_ring::odd_cyclotomic::CompositeCyclotomicNumberRing;

#[cfg(any(test, feature = "generic_tests"))]
pub fn test_with_number_ring<NumberRing: Clone + HECyclotomicNumberRing>(number_ring: NumberRing) {
    use feanor_math::algorithms::eea::signed_lcm;
    use feanor_math::assert_el_eq;
    use crate::number_ring::largest_prime_leq_congruent_to_one;

    let required_root_of_unity = signed_lcm(
        number_ring.mod_p_required_root_of_unity() as i64, 
        1 << (StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.n() as i64)).unwrap() + 2), 
        StaticRing::<i64>::RING
    );
    let p1 = largest_prime_leq_congruent_to_one(20000, required_root_of_unity).unwrap();
    let p2 = largest_prime_leq_congruent_to_one(p1 - 1, required_root_of_unity).unwrap();
    assert!(p1 != p2);
    let rank = number_ring.rank();
    let base_ring = zn_rns::Zn::new(vec![Zn::new(p1 as u64), Zn::new(p2 as u64)], BigIntRing::RING);
    let ring = SingleRNSRingBase::<_, _, NTTConvolution<_>>::new(number_ring.clone(), base_ring.clone());

    let base_ring = ring.base_ring();
    let elements = vec![
        ring.zero(),
        ring.one(),
        ring.neg_one(),
        ring.int_hom().map(p1 as i32),
        ring.int_hom().map(p2 as i32),
        ring.canonical_gen(),
        ring.pow(ring.canonical_gen(), rank - 1),
        ring.int_hom().mul_map(ring.canonical_gen(), p1 as i32),
        ring.int_hom().mul_map(ring.pow(ring.canonical_gen(), rank - 1), p1 as i32),
        ring.add(ring.canonical_gen(), ring.one())
    ];

    feanor_math::ring::generic_tests::test_ring_axioms(&ring, elements.iter().map(|x| ring.clone_el(x)));
    feanor_math::ring::generic_tests::test_self_iso(&ring, elements.iter().map(|x| ring.clone_el(x)));
    feanor_math::rings::extension::generic_tests::test_free_algebra_axioms(&ring);

    for a in &elements {
        for b in &elements {
            for c in &elements {
                let actual = ring.get_ring().two_by_two_convolution([a, b], [c, &ring.one()]);
                assert_el_eq!(&ring, ring.mul_ref(a, c), &actual[0]);
                assert_el_eq!(&ring, ring.add_ref_snd(ring.mul_ref(b, c), a), &actual[1]);
                assert_el_eq!(&ring, b, &actual[2]);
            }
        }
    }

    let double_rns_ring = DoubleRNSRingBase::new(number_ring.clone(), base_ring.clone());
    feanor_math::ring::generic_tests::test_hom_axioms(&ring, &double_rns_ring, elements.iter().map(|x| ring.clone_el(x)));
    
    let dropped_rns_factor_ring = SingleRNSRingBase::new(number_ring.clone(), zn_rns::Zn::new(vec![Zn::new(p2 as u64)], BigIntRing::RING));

    for a in &elements {
        assert_el_eq!(
            &dropped_rns_factor_ring,
            dropped_rns_factor_ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| dropped_rns_factor_ring.base_ring().from_congruence([*ring.base_ring().get_congruence(&c).at(1)].into_iter()))),
            dropped_rns_factor_ring.get_ring().drop_rns_factor_element(ring.get_ring(), &[0], ring.clone_el(a))
        );
    }

    feanor_math::serialization::generic_tests::test_serialization(&ring, elements.iter().map(|x| ring.clone_el(x)));
}

#[test]
fn test_multiple_representations() {
    let rns_base = zn_rns::Zn::new(vec![Zn::new(2113), Zn::new(2689)], BigIntRing::RING);
    let ring: SingleRNSRing<_> = SingleRNSRingBase::new(OddCyclotomicNumberRing::new(3), rns_base.clone());

    let from_raw_representation = |data: [i32; 3]| SingleRNSRingEl {
        coefficients: ring.get_ring().base_ring().as_iter().flat_map(|Zp| data.iter().map(|x| Zp.int_hom().map(*x))).collect(),
        convolutions: PhantomData,
        number_ring: PhantomData
    };
    let from_reduced_representation = |data: [i32; 2]| ring.from_canonical_basis(data.iter().map(|x| ring.base_ring().int_hom().map(*x)));

    let elements = [
        (from_reduced_representation([0, 0]), from_raw_representation([1, 1, 1])),
        (from_reduced_representation([1, 0]), from_raw_representation([0, -1, -1])),
        (from_reduced_representation([1, 1]), from_raw_representation([0, 0, -1])),
        (from_reduced_representation([0, 1]), from_raw_representation([-1, 0, -1])),
        (from_reduced_representation([2, 2]), from_raw_representation([1, 1, -1])),
        (from_reduced_representation([1, 2]), from_raw_representation([-1, 0, -2]))
    ];

    for (red, unred) in &elements {
        assert_el_eq!(&ring, red, unred);
        assert_el_eq!(&ring, red, ring.from_canonical_basis(ring.wrt_canonical_basis(unred).iter()));
        assert_el_eq!(&ring, ring.negate(ring.clone_el(red)), ring.negate(ring.clone_el(unred)));
    }
    for (red1, unred1) in &elements {
        for (red2, unred2) in &elements {
            assert_el_eq!(&ring, ring.add_ref(red1, red2), ring.add_ref(red1, unred2));
            assert_el_eq!(&ring, ring.add_ref(red1, red2), ring.add_ref(unred1, red2));
            assert_el_eq!(&ring, ring.add_ref(red1, red2), ring.add_ref(unred1, unred2));
            
            assert_el_eq!(&ring, ring.sub_ref(red1, red2), ring.sub_ref(red1, unred2));
            assert_el_eq!(&ring, ring.sub_ref(red1, red2), ring.sub_ref(unred1, red2));
            assert_el_eq!(&ring, ring.sub_ref(red1, red2), ring.sub_ref(unred1, unred2));
            
            assert_el_eq!(&ring, ring.mul_ref(red1, red2), ring.mul_ref(red1, unred2));
            assert_el_eq!(&ring, ring.mul_ref(red1, red2), ring.mul_ref(unred1, red2));
            assert_el_eq!(&ring, ring.mul_ref(red1, red2), ring.mul_ref(unred1, unred2));
        }
    }

    let doublerns_ring = DoubleRNSRingBase::new(OddCyclotomicNumberRing::new(3), rns_base);
    let iso = doublerns_ring.can_iso(&ring).unwrap();
    for (red, unred) in &elements {
        assert_el_eq!(&doublerns_ring, iso.inv().map_ref(red), iso.inv().map_ref(unred));
        assert_el_eq!(&ring, iso.map(iso.inv().map_ref(red)), iso.map(iso.inv().map_ref(unred)));
    }
}

#[test]
fn test_two_by_two_convolution() {
    let rns_base = zn_rns::Zn::new(vec![Zn::new(65537), Zn::new(2689)], BigIntRing::RING);
    let ring: SingleRNSRing<_> = SingleRNSRingBase::new(OddCyclotomicNumberRing::new(3), rns_base.clone());

    let a = ring.from_canonical_basis([1, 2].into_iter().map(|c| ring.base_ring().int_hom().map(c)));
    let b = ring.from_canonical_basis([3, 5].into_iter().map(|c| ring.base_ring().int_hom().map(c)));
    let c = ring.from_canonical_basis([7, 2].into_iter().map(|c| ring.base_ring().int_hom().map(c)));
    let d = ring.from_canonical_basis([9, 8].into_iter().map(|c| ring.base_ring().int_hom().map(c)));

    for lhs0 in [&a, &b, &c, &d] {
        for lhs1 in [&a, &b, &c, &d] {
            for rhs0 in [&a, &b, &c, &d] {
                for rhs1 in [&a, &b, &c, &d] {
                    let [res0, res1, res2] = ring.get_ring().two_by_two_convolution([lhs0, lhs1], [rhs0, rhs1]);
                    assert_el_eq!(&ring, ring.mul_ref(lhs0, rhs0), res0);
                    assert_el_eq!(&ring, ring.add(ring.mul_ref(lhs0, rhs1), ring.mul_ref(lhs1, rhs0)), res1);
                    assert_el_eq!(&ring, ring.mul_ref(lhs1, rhs1), res2);
                }
            }
        }
    }
}

#[test]
fn test_galois_automorphisms() {
    let rns_base = zn_rns::Zn::new(vec![Zn::new(65537), Zn::new(4481)], BigIntRing::RING);
    let ring: SingleRNSRing<_> = SingleRNSRingBase::new(CompositeCyclotomicNumberRing::new(5, 7), rns_base.clone());
    let poly_ring = DensePolyRing::new(ring.base_ring(), "X");
    let ZZX = DensePolyRing::new(StaticRing::<i64>::RING, "X");
    let Phi_n = poly_ring.coerce(&ZZX, cyclotomic_polynomial(&ZZX, 35));
    let Gal = ring.galois_group();
    let g = Gal.from_representative(4);
    let from_poly = |f| ring.from_canonical_basis_extended((0..=poly_ring.degree(&f).unwrap()).map(|k| poly_ring.base_ring().clone_el(poly_ring.coefficient_at(&f, k))));

    for i in 0..24 {
        for j in 0..24 {
            let input = poly_ring.from_terms([(poly_ring.base_ring().one(), i), (poly_ring.base_ring().int_hom().map(10), j)]);
            let expected = from_poly(poly_ring.div_rem_monic(poly_ring.evaluate(&input, &poly_ring.pow(poly_ring.indeterminate(), 4), poly_ring.inclusion()), &Phi_n).1);
            let actual = ring.apply_galois_action(&from_poly(input), g);
            assert_el_eq!(&ring, &expected, &actual);
        }
    }
}