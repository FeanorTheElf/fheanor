use std::alloc::Allocator;
use std::alloc::Global;
use std::marker::PhantomData;
use std::sync::Arc;

use feanor_math::algorithms::convolution::ConvolutionAlgorithm;
use feanor_math::algorithms::matmul::ComputeInnerProduct;
use feanor_math::divisibility::*;
use feanor_math::integer::*;
use feanor_math::iters::multi_cartesian_product;
use feanor_math::iters::MultiProduct;
use feanor_math::matrix::*;
use feanor_math::rings::extension::*;
use feanor_math::rings::finite::*;
use feanor_math::ring::*;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::homomorphism::*;
use feanor_math::seq::*;
use feanor_math::serialization::*;
use feanor_math::specialization::{FiniteRingOperation, FiniteRingSpecializable};

use serde::Deserializer;
use serde::Serialize;
use serde::de::DeserializeSeed;
use tracing::instrument;

use crate::cyclotomic::{CyclotomicGaloisGroupEl, CyclotomicRing};
use crate::number_ring::*;
use super::serialization::deserialize_rns_data;
use super::serialization::serialize_rns_data;
use super::single_rns_ring::*;
use super::BGFVCiphertextRing;
use super::PreparedMultiplicationRing;

///
/// Implementation of the ring `Z[𝝵_m]/(q)`, where `q = p1 ... pr` is a product of "RNS factors".
/// Elements are (by default) stored in double-RNS-representation for efficient arithmetic.
/// 
/// As opposed to [`SingleRNSRing`], this means multiplications are very cheap, but non-arithmetic
/// operations like [`FreeAlgebra::from_canonical_basis()`] and [`FreeAlgebra::wrt_canonical_basis()`] 
/// are expensive, and in some cases only supported for elements that have explicitly been converted 
/// to [`SmallBasisEl`] via [`DoubleRNSRingBase::undo_fft()`]. This conversion is expensive in terms of
/// performance.
/// 
/// # Mathematical details
/// 
/// The "double-RNS representation" refers to the representation of an element via its value modulo
/// each prime ideal of `Z[𝝵_m]/(q)`. Since we require each `Z/(pi)` to have a primitive `m`-th root
/// of unity `z`, these prime ideals are of the form `(pi, 𝝵_m - z^j)` with `j in (Z/mZ)*`.
/// In other words, the double-RNS representation refers to the evaluation of an element (considered
/// as polyomial in `𝝵_m`) at all primitive `m`-th roots of unity, modulo each `pi`.
/// This is also the multiplicative basis, as specified by [`HENumberRingMod`].
/// In particular, multiplication of elements refers to component-wise multiplication of these vectors.
/// 
pub struct DoubleRNSRingBase<NumberRing, A = Global> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    /// The number ring whose quotient we represent
    number_ring: NumberRing,
    /// The number ring modulo each RNS factor `pi`, use for conversion between small and multiplicative basis
    ring_decompositions: Vec<Arc<<NumberRing as HENumberRing>::Decomposed>>,
    /// The current RNS base
    rns_base: zn_rns::Zn<Zn, BigIntRing>,
    /// Use to allocate memory for ring elements
    allocator: A
}

///
/// [`RingStore`] for [`DoubleRNSRingBase`].
/// 
pub type DoubleRNSRing<NumberRing, A = Global> = RingValue<DoubleRNSRingBase<NumberRing, A>>;

///
/// A [`DoubleRNSRing`] element, stored by its coefficients w.r.t. the multiplicative basis.
/// In particular, this is the only representation that allows for multiplications.
/// 
pub struct DoubleRNSEl<NumberRing, A = Global>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    number_ring: PhantomData<NumberRing>,
    allocator: PhantomData<A>,
    el_wrt_mult_basis: Vec<ZnEl, A>
}

///
/// A [`DoubleRNSRing`] element, stored by its coefficients w.r.t. the "small basis".
/// 
pub struct SmallBasisEl<NumberRing, A = Global>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    number_ring: PhantomData<NumberRing>,
    allocator: PhantomData<A>,
    el_wrt_small_basis: Vec<ZnEl, A>
}

impl<NumberRing> DoubleRNSRingBase<NumberRing> 
    where NumberRing: HENumberRing
{
    ///
    /// Creates a new [`DoubleRNSRing`].
    /// 
    /// Each RNS factor `Z/(pi)` in `rns_base` must have suitable roots of unity,
    /// as specified by [`HENumberRing::mod_p_required_root_of_unity()`].
    /// 
    #[instrument(skip_all)]
    pub fn new(number_ring: NumberRing, rns_base: zn_rns::Zn<Zn, BigIntRing>) -> RingValue<Self> {
        Self::new_with(number_ring, rns_base, Global)
    }
}

impl<NumberRing, A> Clone for DoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing + Clone,
        A: Allocator + Clone
{
    fn clone(&self) -> Self {
        Self {
            allocator: self.allocator.clone(),
            number_ring: self.number_ring.clone(),
            ring_decompositions: self.ring_decompositions.clone(),
            rns_base: self.rns_base.clone()
        }
    }
}

impl<NumberRing, A> DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing + Clone,
        A: Allocator + Clone
{
    #[instrument(skip_all)]
    pub fn drop_rns_factor(&self, drop_rns_factors: &[usize]) -> RingValue<Self> {
        RingValue::from(Self {
            ring_decompositions: self.ring_decompositions.iter().enumerate().filter(|(i, _)| !drop_rns_factors.contains(i)).map(|(_, x)| x.clone()).collect(),
            number_ring: self.number_ring().clone(),
            rns_base: zn_rns::Zn::new(self.base_ring().as_iter().enumerate().filter(|(i, _)| !drop_rns_factors.contains(i)).map(|(_, x)| x.clone()).collect(), BigIntRing::RING),
            allocator: self.allocator().clone()
        })
    }
}

impl<NumberRing, A> DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    ///
    /// Creates a new [`DoubleRNSRing`].
    /// 
    /// Each RNS factor `Z/(pi)` in `rns_base` must have suitable roots of unity,
    /// as specified by [`HENumberRing::mod_p_required_root_of_unity()`].
    /// 
    #[instrument(skip_all)]
    pub fn new_with(number_ring: NumberRing, rns_base: zn_rns::Zn<Zn, BigIntRing>, allocator: A) -> RingValue<Self> {
        assert!(rns_base.len() > 0);
        RingValue::from(Self {
            ring_decompositions: rns_base.as_iter().map(|Fp| Arc::new(number_ring.mod_p(Fp.clone()))).collect(),
            number_ring: number_ring,
            rns_base: rns_base,
            allocator: allocator
        })
    }

    ///
    /// Returns the decompositions of the used [`HENumberRing`] modulo the RNS factors,
    /// which are used to represent elements of the ring (and change their representations).
    /// 
    pub fn ring_decompositions<'a>(&'a self) -> impl VectorFn<&'a <NumberRing as HENumberRing>::Decomposed> + use<'a, NumberRing, A> {
        self.ring_decompositions.as_fn().map_fn(|x| &**x)
    }

    fn element_len(&self) -> usize {
        self.rank() * self.base_ring().len()
    }

    ///
    /// Returns a view on the representation of the given element w.r.t. the small basis. 
    /// In particular, the `i`-th row of the returned matrix contains the coefficients of the element 
    /// modulo the `i`-th RNS factor w.r.t. the small basis, as specified by the `i`-th ring decomposition.
    /// 
    /// Note that the actual choice of the "small basis" is up to the used [`HENumberRing`].
    /// 
    pub fn as_matrix_wrt_small_basis<'a>(&self, element: &'a SmallBasisEl<NumberRing, A>) -> Submatrix<'a, AsFirstElement<ZnEl>, ZnEl> {
        Submatrix::from_1d(&element.el_wrt_small_basis, self.base_ring().len(), self.rank())
    }

    ///
    /// Returns a mutable view on the representation of the given element w.r.t. the small basis. 
    /// In particular, the `i`-th row of the returned matrix contains the coefficients of the element 
    /// modulo the `i`-th RNS factor w.r.t. the small basis, as specified by the `i`-th ring decomposition.
    /// 
    /// Note that the actual choice of the "small basis" is up to the used [`HENumberRing`].
    /// 
    pub fn as_matrix_wrt_small_basis_mut<'a>(&self, element: &'a mut SmallBasisEl<NumberRing, A>) -> SubmatrixMut<'a, AsFirstElement<ZnEl>, ZnEl> {
        SubmatrixMut::from_1d(&mut element.el_wrt_small_basis, self.base_ring().len(), self.rank())
    }

    ///
    /// Returns a view on the representation of the given element w.r.t. the multiplicative basis. 
    /// In particular, the `i`-th row of the returned matrix contains the coefficients of the element 
    /// modulo the `i`-th RNS factor w.r.t. the multiplicative basis, as specified by the `i`-th ring decomposition.
    /// 
    /// Note that the actual choice of the "multiplicative basis" is up to the used [`HENumberRing`].
    ///
    pub fn as_matrix_wrt_mult_basis<'a>(&self, element: &'a DoubleRNSEl<NumberRing, A>) -> Submatrix<'a, AsFirstElement<ZnEl>, ZnEl> {
        Submatrix::from_1d(&element.el_wrt_mult_basis, self.base_ring().len(), self.rank())
    }

    ///
    /// Returns a mutable view on the representation of the given element w.r.t. the multiplicative basis. 
    /// In particular, the `i`-th row of the returned matrix contains the coefficients of the element 
    /// modulo the `i`-th RNS factor w.r.t. the multiplicative basis, as specified by the `i`-th ring decomposition.
    /// 
    /// Note that the actual choice of the "multiplicative basis" is up to the used [`HENumberRing`].
    ///
    pub fn as_matrix_wrt_mult_basis_mut<'a>(&self, element: &'a mut DoubleRNSEl<NumberRing, A>) -> SubmatrixMut<'a, AsFirstElement<ZnEl>, ZnEl> {
        SubmatrixMut::from_1d(&mut element.el_wrt_mult_basis, self.base_ring().len(), self.rank())
    }

    pub fn number_ring(&self) -> &NumberRing {
        &self.number_ring
    }

    ///
    /// Converts the element to its representation w.r.t. the small basis.
    /// 
    /// The coefficients w.r.t. this basis can be accessed using [`DoubleRNSRingBase::as_matrix_wrt_small_basis()`].
    /// 
    #[instrument(skip_all)]
    pub fn undo_fft(&self, element: DoubleRNSEl<NumberRing, A>) -> SmallBasisEl<NumberRing, A> {
        assert_eq!(element.el_wrt_mult_basis.len(), self.element_len());
        let mut result = element.el_wrt_mult_basis;
        for i in 0..self.base_ring().len() {
            self.ring_decompositions[i].mult_basis_to_small_basis(&mut result[(i * self.rank())..((i + 1) * self.rank())]);
        }
        SmallBasisEl {
            el_wrt_small_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }

    ///
    /// Like [`DoubleRNSRingBase::undo_fft()`], this converts an element to its representation w.r.t.
    /// the small basis. However, unlike [`DoubleRNSRingBase::undo_fft()`], it only outputs the result
    /// for a subset of RNS factors. Thus, the output cannot be a [`SmallBasisEl`], but instead this
    /// function directly writes the small basis representation of the output to the given matrix.
    /// This representation is the same that would be returned when calling [`DoubleRNSRingBase::as_matrix_wrt_small_basis()`].
    /// 
    #[instrument(skip_all)]
    pub fn undo_fft_partial<V>(&self, element: &DoubleRNSEl<NumberRing, A>, required_rns_factors: &[usize], mut output: SubmatrixMut<V, ZnEl>)
        where V: AsPointerToSlice<ZnEl>
    {
        assert_eq!(element.el_wrt_mult_basis.len(), self.element_len());
        assert_eq!(output.col_count(), self.rank());
        assert_eq!(output.row_count(), required_rns_factors.len());
        for (i_out, i_in) in required_rns_factors.iter().copied().enumerate() {
            assert!(i_in < self.base_ring().len());
            for j in 0..self.rank() {
                *output.at_mut(i_out, j) = element.el_wrt_mult_basis[i_in * self.rank() + j];
            }
            self.ring_decompositions[i_in].mult_basis_to_small_basis(output.row_mut_at(i_out));
        }
    }

    pub fn allocator(&self) -> &A {
        &self.allocator
    }

    pub fn zero_non_fft(&self) -> SmallBasisEl<NumberRing, A> {
        SmallBasisEl {
            el_wrt_small_basis: self.zero().el_wrt_mult_basis,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }

    pub fn from_non_fft(&self, x: El<<Self as RingExtension>::BaseRing>) -> SmallBasisEl<NumberRing, A> {
        let mut result = Vec::with_capacity_in(self.element_len(), self.allocator.clone());
        let x = self.base_ring().get_congruence(&x);
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            result.push(Zp.clone_el(x.at(i)));
            for _ in 1..self.rank() {
                result.push(Zp.zero());
            }
            self.ring_decompositions[i].coeff_basis_to_small_basis(&mut result[(i * self.rank())..((i + 1) * self.rank())]);
        }
        SmallBasisEl {
            el_wrt_small_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }

    ///
    /// Converts the element to its representation w.r.t. the multiplicative basis.
    /// 
    /// The main use of this basis is to compute multiplications (via [`RingBase::mul()`] etc.).
    /// You can also access the coefficients w.r.t. the multiplicative basis using [`DoubleRNSRingBase::as_matrix_wrt_mult_basis()`].
    /// 
    #[instrument(skip_all)]
    pub fn do_fft(&self, element: SmallBasisEl<NumberRing, A>) -> DoubleRNSEl<NumberRing, A> {
        assert_eq!(element.el_wrt_small_basis.len(), self.element_len());
        let mut result = element.el_wrt_small_basis;
        for i in 0..self.base_ring().len() {
            self.ring_decompositions[i].small_basis_to_mult_basis(&mut result[(i * self.rank())..((i + 1) * self.rank())]);
        }
        DoubleRNSEl {
            el_wrt_mult_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }

    ///
    /// Creates the ring element whose coefficients (w.r.t. the coefficient basis) are given 
    /// by repeated calls to the given function.
    /// 
    #[instrument(skip_all)]
    pub fn sample_from_coefficient_distribution<G: FnMut() -> i32>(&self, mut distribution: G) -> SmallBasisEl<NumberRing, A> {
        let mut result = self.zero_non_fft().el_wrt_small_basis;
        for j in 0..self.rank() {
            let c = distribution();
            for i in 0..self.base_ring().len() {
                result[j + i * self.rank()] = self.base_ring().at(i).int_hom().map(c);
            }
        }
        for i in 0..self.base_ring().len() {
            self.ring_decompositions[i].coeff_basis_to_small_basis(&mut result[(i * self.rank())..((i + 1) * self.rank())]);
        }
        return SmallBasisEl {
            el_wrt_small_basis: result,
            allocator: PhantomData,
            number_ring: PhantomData
        };
    }

    #[instrument(skip_all)]
    pub fn clone_el_non_fft(&self, val: &SmallBasisEl<NumberRing, A>) -> SmallBasisEl<NumberRing, A> {
        assert_eq!(self.element_len(), val.el_wrt_small_basis.len());
        let mut result = Vec::with_capacity_in(self.element_len(), self.allocator.clone());
        result.extend((0..self.element_len()).map(|i| self.base_ring().at(i / self.rank()).clone_el(&val.el_wrt_small_basis[i])));
        SmallBasisEl {
            el_wrt_small_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }

    #[instrument(skip_all)]
    pub fn eq_el_non_fft(&self, lhs: &SmallBasisEl<NumberRing, A>, rhs: &SmallBasisEl<NumberRing, A>) -> bool {
        assert_eq!(self.element_len(), lhs.el_wrt_small_basis.len());
        assert_eq!(self.element_len(), rhs.el_wrt_small_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                if !self.base_ring().at(i).eq_el(&lhs.el_wrt_small_basis[i * self.rank() + j], &rhs.el_wrt_small_basis[i * self.rank() + j]) {
                    return false;
                }
            }
        }
        return true;
    }

    #[instrument(skip_all)]
    pub fn negate_inplace_non_fft(&self, val: &mut SmallBasisEl<NumberRing, A>) {
        assert_eq!(self.element_len(), val.el_wrt_small_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).negate_inplace(&mut val.el_wrt_small_basis[i * self.rank() + j]);
            }
        }
    }

    #[instrument(skip_all)]
    pub fn negate_non_fft(&self, mut val: SmallBasisEl<NumberRing, A>) -> SmallBasisEl<NumberRing, A> {
        self.negate_inplace_non_fft(&mut val);
        return val;
    }

    #[instrument(skip_all)]
    pub fn sub_assign_non_fft(&self, lhs: &mut SmallBasisEl<NumberRing, A>, rhs: &SmallBasisEl<NumberRing, A>) {
        assert_eq!(self.element_len(), lhs.el_wrt_small_basis.len());
        assert_eq!(self.element_len(), rhs.el_wrt_small_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).sub_assign_ref(&mut lhs.el_wrt_small_basis[i * self.rank() + j], &rhs.el_wrt_small_basis[i * self.rank() + j]);
            }
        }
    }

    #[instrument(skip_all)]
    pub fn mul_scalar_assign_non_fft(&self, lhs: &mut SmallBasisEl<NumberRing, A>, rhs: &El<zn_rns::Zn<Zn, BigIntRing>>) {
        assert_eq!(self.element_len(), lhs.el_wrt_small_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).mul_assign_ref(&mut lhs.el_wrt_small_basis[i * self.rank() + j], self.base_ring().get_congruence(rhs).at(i));
            }
        }
    }

    #[instrument(skip_all)]
    pub fn add_assign_non_fft(&self, lhs: &mut SmallBasisEl<NumberRing, A>, rhs: &SmallBasisEl<NumberRing, A>) {
        assert_eq!(self.element_len(), lhs.el_wrt_small_basis.len());
        assert_eq!(self.element_len(), rhs.el_wrt_small_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).add_assign_ref(&mut lhs.el_wrt_small_basis[i * self.rank() + j], &rhs.el_wrt_small_basis[i * self.rank() + j]);
            }
        }
    }

    #[instrument(skip_all)]
    pub fn from_canonical_basis_non_fft<V>(&self, vec: V) -> SmallBasisEl<NumberRing, A>
        where V: IntoIterator<Item = El<<Self as RingExtension>::BaseRing>>
    {
        let mut result = self.zero_non_fft().el_wrt_small_basis;
        for (j, x) in vec.into_iter().enumerate() {
            let congruence = self.base_ring().get_ring().get_congruence(&x);
            for i in 0..self.base_ring().len() {
                result[i * self.rank() + j] = self.base_ring().at(i).clone_el(congruence.at(i));
            }
        }
        for i in 0..self.base_ring().len() {
            self.ring_decompositions[i].coeff_basis_to_small_basis(&mut result[(i * self.rank())..((i + 1) * self.rank())]);
        }
        return SmallBasisEl {
            el_wrt_small_basis: result,
            allocator: PhantomData,
            number_ring: PhantomData
        };
    }

    #[instrument(skip_all)]
    pub fn wrt_canonical_basis_non_fft<'a>(&'a self, el: SmallBasisEl<NumberRing, A>) -> DoubleRNSRingBaseElVectorRepresentation<'a, NumberRing, A> {
        let mut result = el.el_wrt_small_basis;
        for i in 0..self.base_ring().len() {
            self.ring_decompositions[i].small_basis_to_coeff_basis(&mut result[(i * self.rank())..((i + 1) * self.rank())]);
        }
        return DoubleRNSRingBaseElVectorRepresentation {
            ring: self,
            el_wrt_coeff_basis: result
        };
    }

    ///
    /// Computes the isomorphism between a `SingleRNSRing` and a `DoubleRNSRing` (if it exists, i.e.
    /// both number ring and RNS base match). This is very similar to using the implementation of
    /// [`CanHomFrom`], but returns the result as [`SmallBasisEl`] instead of [`DoubleRNSEl`].
    /// 
    #[instrument(skip_all)]
    pub fn map_in_from_singlerns<A2, C>(&self, from: &SingleRNSRingBase<NumberRing, A2, C>, mut el: El<SingleRNSRing<NumberRing, A2, C>>, hom: &<Self as CanHomFrom<SingleRNSRingBase<NumberRing, A2, C>>>::Homomorphism) -> SmallBasisEl<NumberRing, A>
        where NumberRing: HECyclotomicNumberRing,
            A2: Allocator + Clone,
            C: ConvolutionAlgorithm<ZnBase>
    {
        let mut result = Vec::with_capacity_in(self.element_len(), self.allocator.clone());
        let el_as_matrix = from.to_matrix(&mut el);
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.rank() {
                result.push(Zp.get_ring().map_in_ref(from.base_ring().at(i).get_ring(), el_as_matrix.at(i, j), &hom[i]));
            }
        }
        for i in 0..self.base_ring().len() {
            self.ring_decompositions().at(i).coeff_basis_to_small_basis(&mut result[(i * self.rank())..((i + 1) * self.rank())]);
        }
        SmallBasisEl {
            el_wrt_small_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }

    ///
    /// Computes the isomorphism between a `SingleRNSRing` and a `DoubleRNSRing` (if it exists, i.e.
    /// both number ring and RNS base match). This is very similar to using the implementation of
    /// [`CanHomFrom`], but takes the argument as [`SmallBasisEl`] instead of [`DoubleRNSEl`].
    /// 
    #[instrument(skip_all)]
    pub fn map_out_to_singlerns<A2, C>(&self, to: &SingleRNSRingBase<NumberRing, A2, C>, el: SmallBasisEl<NumberRing, A>, iso: &<Self as CanIsoFromTo<SingleRNSRingBase<NumberRing, A2, C>>>::Isomorphism) -> El<SingleRNSRing<NumberRing, A2, C>>
        where NumberRing: HECyclotomicNumberRing,
            A2: Allocator + Clone,
            C: ConvolutionAlgorithm<ZnBase>
    {
        let mut result = to.zero();
        let mut result_matrix = to.coefficients_as_matrix_mut(&mut result);
        let mut el_coeff = el.el_wrt_small_basis;
        for i in 0..self.base_ring().len() {
            self.ring_decompositions().at(i).small_basis_to_coeff_basis(&mut el_coeff[(i * self.rank())..((i + 1) * self.rank())]);
        }
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.rank() {
                *result_matrix.at_mut(i, j) = Zp.get_ring().map_out(to.base_ring().at(i).get_ring(), Zp.clone_el(&el_coeff[i * self.rank() + j]), &iso[i]);
            }
        }
        return result;
    }
    
    #[instrument(skip_all)]
    pub fn drop_rns_factor_element(&self, from: &Self, drop_factors: &[usize], value: &DoubleRNSEl<NumberRing, A>) -> DoubleRNSEl<NumberRing, A> {
        assert!(self.number_ring() == from.number_ring());
        assert_eq!(self.base_ring().len() + drop_factors.len(), from.base_ring().len());
        assert!(drop_factors.iter().all(|i| *i < from.base_ring().len()));
        assert_eq!(from.element_len(), value.el_wrt_mult_basis.len());

        let mut result = self.zero();
        let mut i_self = 0;
        for i_from in 0..from.base_ring().len() {
            if drop_factors.contains(&i_from) {
                continue;
            }
            assert!(self.base_ring().at(i_self).get_ring() == from.base_ring().at(i_from).get_ring());
            for j in 0..self.rank() {
                result.el_wrt_mult_basis[j + i_self * self.rank()] = value.el_wrt_mult_basis[j + i_from * from.rank()];
            }
            i_self += 1;
        }

        return result;
    }

    #[instrument(skip_all)]
    pub fn add_rns_factor_element(&self, from: &Self, add_rns_factors: &[usize], value: &DoubleRNSEl<NumberRing, A>) -> DoubleRNSEl<NumberRing, A> {
        assert!(self.number_ring() == from.number_ring());
        assert_eq!(self.base_ring().len(), from.base_ring().len() + add_rns_factors.len());
        assert!(add_rns_factors.iter().all(|i| *i < self.base_ring().len()));
        assert_eq!(from.element_len(), value.el_wrt_mult_basis.len());

        let mut result = self.zero();
        let mut i_from = 0;
        for i_self in 0..self.base_ring().len() {
            if add_rns_factors.contains(&i_self) {
                continue;
            }
            assert!(self.base_ring().at(i_self).get_ring() == from.base_ring().at(i_from).get_ring());
            for j in 0..self.rank() {
                result.el_wrt_mult_basis[j + i_self * self.rank()] = value.el_wrt_mult_basis[j + i_from * from.rank()];
            }
            i_from += 1;
        }

        return result;
    }

    #[instrument(skip_all)]
    pub fn drop_rns_factor_non_fft_element(&self, from: &Self, drop_factors: &[usize], value: &SmallBasisEl<NumberRing, A>) -> SmallBasisEl<NumberRing, A> {
        assert!(self.number_ring() == from.number_ring());
        assert_eq!(self.base_ring().len() + drop_factors.len(), from.base_ring().len());
        assert!(drop_factors.iter().all(|i| *i < from.base_ring().len()));
        assert_eq!(from.element_len(), value.el_wrt_small_basis.len());

        let mut result = self.zero_non_fft();
        let mut result_as_matrix = self.as_matrix_wrt_small_basis_mut(&mut result);
        let value_as_matrix = from.as_matrix_wrt_small_basis(&value);
        let mut i_self = 0;
        for i_from in 0..from.base_ring().len() {
            if drop_factors.contains(&i_from) {
                continue;
            }
            assert!(self.base_ring().at(i_self).get_ring() == from.base_ring().at(i_from).get_ring());
            for j in 0..self.rank() {
                *result_as_matrix.at_mut(i_self, j) = *value_as_matrix.at(i_from, j);
            }
            i_self += 1;
        }

        return result;
    }

    #[instrument(skip_all)]
    pub fn add_rns_factor_non_fft_element(&self, from: &Self, add_rns_factors: &[usize], value: &SmallBasisEl<NumberRing, A>) -> SmallBasisEl<NumberRing, A> {
        assert!(self.number_ring() == from.number_ring());
        assert_eq!(self.base_ring().len(), from.base_ring().len() + add_rns_factors.len());
        assert!(add_rns_factors.iter().all(|i| *i < self.base_ring().len()));
        assert_eq!(from.element_len(), value.el_wrt_small_basis.len());

        let mut result = self.zero_non_fft();
        let mut result_as_matrix = self.as_matrix_wrt_small_basis_mut(&mut result);
        let value_as_matrix = from.as_matrix_wrt_small_basis(&value);
        let mut i_from = 0;
        for i_self in 0..self.base_ring().len() {
            if add_rns_factors.contains(&i_self) {
                continue;
            }
            assert!(self.base_ring().at(i_self).get_ring() == from.base_ring().at(i_from).get_ring());
            for j in 0..self.rank() {
                *result_as_matrix.at_mut(i_self, j) = *value_as_matrix.at(i_from, j);
            }
            i_from += 1;
        }

        return result;
    }

    fn inner_product_base<'a, I: Clone + Iterator<Item = (&'a DoubleRNSEl<NumberRing, A>, &'a DoubleRNSEl<NumberRing, A>)>>(&self, els: I) -> DoubleRNSEl<NumberRing, A>
        where Self: 'a
    {
        let mut result = self.zero();
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                let idx = i * self.rank() + j;
                result.el_wrt_mult_basis[idx] = <_ as ComputeInnerProduct>::inner_product(
                    self.base_ring().at(i).get_ring(), 
                    els.clone().map(|(l, r)| (l.el_wrt_mult_basis[idx], r.el_wrt_mult_basis[idx]))
                )
            }
        }
        return result;
    } 
}

impl<NumberRing, A> PartialEq for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn eq(&self, other: &Self) -> bool {
        self.number_ring == other.number_ring && self.rns_base.get_ring() == other.rns_base.get_ring()
    }
}

impl<NumberRing, A> RingBase for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type Element = DoubleRNSEl<NumberRing, A>;

    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        assert_eq!(self.element_len(), val.el_wrt_mult_basis.len());
        let mut result = Vec::with_capacity_in(self.element_len(), self.allocator.clone());
        result.extend((0..self.element_len()).map(|i| self.base_ring().at(i / self.rank()).clone_el(&val.el_wrt_mult_basis[i])));
        DoubleRNSEl {
            el_wrt_mult_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }

    #[instrument(skip_all)]
    fn add_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        assert_eq!(self.element_len(), lhs.el_wrt_mult_basis.len());
        assert_eq!(self.element_len(), rhs.el_wrt_mult_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).add_assign_ref(&mut lhs.el_wrt_mult_basis[i * self.rank() + j], &rhs.el_wrt_mult_basis[i * self.rank() + j]);
            }
        }
    }

    fn add_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        self.add_assign_ref(lhs, &rhs);
    }

    #[instrument(skip_all)]
    fn sub_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        assert_eq!(self.element_len(), lhs.el_wrt_mult_basis.len());
        assert_eq!(self.element_len(), rhs.el_wrt_mult_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).sub_assign_ref(&mut lhs.el_wrt_mult_basis[i * self.rank() + j], &rhs.el_wrt_mult_basis[i * self.rank() + j]);
            }
        }
    }

    #[instrument(skip_all)]
    fn negate_inplace(&self, lhs: &mut Self::Element) {
        assert_eq!(self.element_len(), lhs.el_wrt_mult_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).negate_inplace(&mut lhs.el_wrt_mult_basis[i * self.rank() + j]);
            }
        }
    }

    fn mul_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        self.mul_assign_ref(lhs, &rhs);
    }

    #[instrument(skip_all)]
    fn mul_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        assert_eq!(self.element_len(), lhs.el_wrt_mult_basis.len());
        assert_eq!(self.element_len(), rhs.el_wrt_mult_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).mul_assign_ref(&mut lhs.el_wrt_mult_basis[i * self.rank() + j], &rhs.el_wrt_mult_basis[i * self.rank() + j]);
            }
        }
    }
    
    fn from_int(&self, value: i32) -> Self::Element {
        self.from(self.base_ring().get_ring().from_int(value))
    }

    #[instrument(skip_all)]
    fn mul_assign_int(&self, lhs: &mut Self::Element, rhs: i32) {
        assert_eq!(self.element_len(), lhs.el_wrt_mult_basis.len());
        for i in 0..self.base_ring().len() {
            let rhs_mod_p = self.base_ring().at(i).get_ring().from_int(rhs);
            for j in 0..self.rank() {
                self.base_ring().at(i).mul_assign_ref(&mut lhs.el_wrt_mult_basis[i * self.rank() + j], &rhs_mod_p);
            }
        }
    }

    fn zero(&self) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.element_len(), self.allocator.clone());
        result.extend(self.base_ring().as_iter().flat_map(|Zp| (0..self.rank()).map(|_| Zp.zero())));
        return DoubleRNSEl {
            el_wrt_mult_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        };
    }

    #[instrument(skip_all)]
    fn eq_el(&self, lhs: &Self::Element, rhs: &Self::Element) -> bool {
        assert_eq!(self.element_len(), lhs.el_wrt_mult_basis.len());
        assert_eq!(self.element_len(), rhs.el_wrt_mult_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                if !self.base_ring().at(i).eq_el(&lhs.el_wrt_mult_basis[i * self.rank() + j], &rhs.el_wrt_mult_basis[i * self.rank() + j]) {
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

    fn dbg<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>) -> std::fmt::Result {
        self.dbg_within(value, out, EnvBindingStrength::Weakest)
    }

    #[instrument(skip_all)]
    fn square(&self, value: &mut Self::Element) {
        assert_eq!(self.element_len(), value.el_wrt_mult_basis.len());
        for i in 0..self.base_ring().len() {
            for j in 0..self.rank() {
                self.base_ring().at(i).square(&mut value.el_wrt_mult_basis[i * self.rank() + j]);
            }
        }
    }

    fn characteristic<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        self.base_ring().characteristic(ZZ)     
    }
}

impl<NumberRing, A> CyclotomicRing for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone
{
    fn m(&self) -> usize {
        self.number_ring.m() as usize
    }

    #[instrument(skip_all)]
    fn apply_galois_action(&self, el: &Self::Element, g: CyclotomicGaloisGroupEl) -> Self::Element {
        assert_eq!(self.element_len(), el.el_wrt_mult_basis.len());
        let mut result = self.zero();
        for (i, _) in self.base_ring().as_iter().enumerate() {
            self.ring_decompositions().at(i).permute_galois_action(
                &el.el_wrt_mult_basis[(i * self.rank())..((i + 1) * self.rank())],
                &mut result.el_wrt_mult_basis[(i * self.rank())..((i + 1) * self.rank())],
                g
            );
        }
        return result;
    }
}

impl<NumberRing, A> ComputeInnerProduct for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    #[instrument(skip_all)]
    fn inner_product<I: Iterator<Item = (Self::Element, Self::Element)>>(&self, els: I) -> Self::Element {
        let data = els.collect::<Vec<_>>();
        return self.inner_product_base(data.iter().map(|(l, r)| (l, r)));
    }

    #[instrument(skip_all)]
    fn inner_product_ref<'a, I: Iterator<Item = (&'a Self::Element, &'a Self::Element)>>(&self, els: I) -> Self::Element
        where Self: 'a
    {
        let data = els.collect::<Vec<_>>();
        return self.inner_product_base(data.iter().map(|(l, r)| (*l, *r)));
    }

    #[instrument(skip_all)]
    fn inner_product_ref_fst<'a, I: Iterator<Item = (&'a Self::Element, Self::Element)>>(&self, els: I) -> Self::Element
        where Self::Element: 'a,
            Self: 'a
    {
        let data = els.collect::<Vec<_>>();
        return self.inner_product_base(data.iter().map(|(l, r)| (*l, r)));
    }
}

impl<NumberRing, A> DivisibilityRing for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    #[instrument(skip_all)]
    fn checked_left_div(&self, lhs: &Self::Element, rhs: &Self::Element) -> Option<Self::Element> {
        let mut result = Vec::with_capacity_in(self.element_len(), self.allocator.clone());
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.rank() {
                result.push(Zp.checked_div(&lhs.el_wrt_mult_basis[i * self.rank() + j], &rhs.el_wrt_mult_basis[i * self.rank() + j])?);
            }
        }
        return Some(DoubleRNSEl { el_wrt_mult_basis: result, number_ring: PhantomData, allocator: PhantomData })
    }

    fn is_unit(&self, x: &Self::Element) -> bool {
        x.el_wrt_mult_basis.iter().enumerate().all(|(index, c)| self.base_ring().at(index / self.rank()).is_unit(c))
    }
}

pub struct DoubleRNSRingBaseElVectorRepresentation<'a, NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    el_wrt_coeff_basis: Vec<ZnEl, A>,
    ring: &'a DoubleRNSRingBase<NumberRing, A>
}

impl<'a, NumberRing, A> VectorFn<El<zn_rns::Zn<Zn, BigIntRing>>> for DoubleRNSRingBaseElVectorRepresentation<'a, NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn len(&self) -> usize {
        self.ring.rank()
    }

    fn at(&self, i: usize) -> El<zn_rns::Zn<Zn, BigIntRing>> {
        assert!(i < self.len());
        self.ring.base_ring().from_congruence(self.el_wrt_coeff_basis[i..].iter().step_by(self.ring.rank()).enumerate().map(|(i, x)| self.ring.base_ring().at(i).clone_el(x)))
    }
}

impl<NumberRing, A> FreeAlgebra for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type VectorRepresentation<'a> = DoubleRNSRingBaseElVectorRepresentation<'a, NumberRing, A> 
        where Self: 'a;

    #[instrument(skip_all)]
    fn canonical_gen(&self) -> Self::Element {
        let mut result = self.zero_non_fft().el_wrt_small_basis;
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            result[i * self.rank() + 1] = Zp.one();
            self.ring_decompositions[i].coeff_basis_to_small_basis(&mut result[(i * self.rank())..((i + 1) * self.rank())]);
        }
        return self.do_fft(SmallBasisEl {
            el_wrt_small_basis: result,
            allocator: PhantomData,
            number_ring: PhantomData
        });
    }

    fn rank(&self) -> usize {
        self.ring_decompositions[0].rank()
    }

    #[instrument(skip_all)]
    fn wrt_canonical_basis<'a>(&'a self, el: &'a Self::Element) -> Self::VectorRepresentation<'a> {
        self.wrt_canonical_basis_non_fft(self.undo_fft(self.clone_el(el)))
    }

    #[instrument(skip_all)]
    fn from_canonical_basis<V>(&self, vec: V) -> Self::Element
        where V: IntoIterator<Item = El<Self::BaseRing>>
    {
        return self.do_fft(self.from_canonical_basis_non_fft(vec));
    }
}

impl<NumberRing, A> RingExtension for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type BaseRing = zn_rns::Zn<Zn, BigIntRing>;

    fn base_ring<'a>(&'a self) -> &'a Self::BaseRing {
        &self.rns_base
    }

    fn from(&self, x: El<Self::BaseRing>) -> Self::Element {
        self.from_ref(&x)
    }

    #[instrument(skip_all)]
    fn from_ref(&self, x: &El<Self::BaseRing>) -> Self::Element {
        let x_congruence = self.base_ring().get_congruence(x);
        let mut result = Vec::with_capacity_in(self.element_len(), self.allocator.clone());
        // this works, since the mult basis is, by definition, given by an isomorphism `R/p -> Fp^n`, so
        // in particular `Fp` mapsto to the diagonal `(x, ..., x) <= Fp^n`
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for _ in 0..self.rank() {
                result.push(Zp.clone_el(x_congruence.at(i)));
            }
        }
        return DoubleRNSEl {
            el_wrt_mult_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        };
    }

    #[instrument(skip_all)]
    fn mul_assign_base(&self, lhs: &mut Self::Element, rhs: &El<Self::BaseRing>) {
        let x_congruence = self.base_ring().get_congruence(rhs);
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.rank() {
                Zp.mul_assign_ref(&mut lhs.el_wrt_mult_basis[i * self.rank() + j], x_congruence.at(i));
            }
        }
    }
}

impl<NumberRing, A> PreparedMultiplicationRing for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type PreparedMultiplicant = Self::Element;

    fn prepare_multiplicant(&self, x: &Self::Element) -> Self::PreparedMultiplicant {
        self.clone_el(x)
    }

    fn mul_prepared(&self, lhs: &Self::PreparedMultiplicant, rhs: &Self::PreparedMultiplicant) -> Self::Element {
        self.mul_ref(lhs, rhs)
    }
}

pub struct WRTCanonicalBasisElementCreator<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    ring: &'a DoubleRNSRingBase<NumberRing, A>
}

impl<'a, 'b, NumberRing, A> Clone for WRTCanonicalBasisElementCreator<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn clone(&self) -> Self {
        Self { ring: self.ring }
    }
}

impl<'a, 'b, NumberRing, A> Fn<(&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    extern "rust-call" fn call(&self, args: (&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)) -> Self::Output {
        self.ring.from_canonical_basis(args.0.iter().map(|x| self.ring.base_ring().clone_el(x)))
    }
}

impl<'a, 'b, NumberRing, A> FnMut<(&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    extern "rust-call" fn call_mut(&mut self, args: (&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)) -> Self::Output {
        self.call(args)
    }
}

impl<'a, 'b, NumberRing, A> FnOnce<(&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type Output = El<DoubleRNSRing<NumberRing, A>>;

    extern "rust-call" fn call_once(self, args: (&'b [El<zn_rns::Zn<Zn, BigIntRing>>],)) -> Self::Output {
        self.call(args)
    }
}

impl<NumberRing, A> FiniteRingSpecializable for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn specialize<O: FiniteRingOperation<Self>>(op: O) -> O::Output {
        op.execute()
    }
}

impl<NumberRing, A> FiniteRing for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type ElementsIter<'a> = MultiProduct<
        <zn_rns::ZnBase<Zn, BigIntRing> as FiniteRing>::ElementsIter<'a>, 
        WRTCanonicalBasisElementCreator<'a, NumberRing, A>, 
        CloneRingEl<&'a zn_rns::Zn<Zn, BigIntRing>>,
        El<DoubleRNSRing<NumberRing, A>>
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
        for j in 0..self.rank() {
            for i in 0..self.base_ring().len() {
                result.el_wrt_mult_basis[j + i * self.rank()] = self.base_ring().at(i).random_element(&mut rng);
            }
        }
        return result;
    }
}

pub struct SerializableSmallBasisElWithRing<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    ring: &'a DoubleRNSRingBase<NumberRing, A>,
    el: &'a SmallBasisEl<NumberRing, A>
}

impl<'a, NumberRing, A> SerializableSmallBasisElWithRing<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    pub fn new(ring: &'a DoubleRNSRingBase<NumberRing, A>, el: &'a SmallBasisEl<NumberRing, A>) -> Self {
        Self { ring, el }
    }
}

impl<'a, NumberRing, A> serde::Serialize for SerializableSmallBasisElWithRing<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer 
    {
        if serializer.is_human_readable() {
            SerializableNewtype::new("RingEl", SerializableSeq::new(self.ring.wrt_canonical_basis_non_fft(self.ring.clone_el_non_fft(self.el)).map_fn(|c| SerializeOwnedWithRing::new(c, self.ring.base_ring())))).serialize(serializer)
        } else {
            SerializableNewtype::new("SmallBasisEl", &serialize_rns_data(self.ring.base_ring(), self.ring.as_matrix_wrt_small_basis(self.el))).serialize(serializer)
        }
    }
}
pub struct DeserializeSeedSmallBasisElWithRing<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    ring: &'a DoubleRNSRingBase<NumberRing, A>,
}

impl<'a, 'de, NumberRing, A> DeserializeSeedSmallBasisElWithRing<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    pub fn new(ring: &'a DoubleRNSRingBase<NumberRing, A>) -> Self {
        Self { ring }
    }
}

impl<'a, 'de, NumberRing, A> serde::de::DeserializeSeed<'de> for DeserializeSeedSmallBasisElWithRing<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type Value = SmallBasisEl<NumberRing, A>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
    {
        if deserializer.is_human_readable() {
            let data = DeserializeSeedNewtype::new("RingEl", DeserializeSeedSeq::new(
                (0..self.ring.rank()).map(|_| DeserializeWithRing::new(self.ring.base_ring())),
                Vec::with_capacity_in(self.ring.rank(), &self.ring.allocator),
                |mut current, next| { current.push(next); current }
            )).deserialize(deserializer)?;
            if data.len() != self.ring.rank() {
                return Err(serde::de::Error::invalid_length(data.len(), &format!("expected a sequence of {} elements of Z/qZ", self.ring.rank()).as_str()));
            }
            return Ok(self.ring.from_canonical_basis_non_fft(data.into_iter()));
        } else {
            let mut result = self.ring.zero_non_fft();
            DeserializeSeedNewtype::new("SmallBasisEl", deserialize_rns_data(self.ring.base_ring(), self.ring.as_matrix_wrt_small_basis_mut(&mut result))).deserialize(deserializer)?;
            return Ok(result);
        }
    }
}

impl<NumberRing, A> SerializableElementRing for DoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn serialize<S>(&self, el: &Self::Element, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        if serializer.is_human_readable() {
            SerializableNewtype::new("RingEl", &SerializableSmallBasisElWithRing::new(self, &self.undo_fft(self.clone_el(el)))).serialize(serializer)
        } else {
            SerializableNewtype::new("DoubleRNSEl", &serialize_rns_data(self.base_ring(), self.as_matrix_wrt_mult_basis(el))).serialize(serializer)
        }
    }

    fn deserialize<'de, D>(&self, deserializer: D) -> Result<Self::Element, D::Error>
        where D: serde::Deserializer<'de>
    {
        if deserializer.is_human_readable() {
            DeserializeSeedNewtype::new("RingEl", DeserializeSeedSmallBasisElWithRing::new(self)).deserialize(deserializer).map(|x| self.do_fft(x))
        } else {
            let mut result = self.zero();
            DeserializeSeedNewtype::new("DoubleRNSEl", deserialize_rns_data(self.base_ring(), self.as_matrix_wrt_mult_basis_mut(&mut result))).deserialize(deserializer)?;
            return Ok(result);
        }
    }
}

impl<NumberRing, A1, A2> CanHomFrom<DoubleRNSRingBase<NumberRing, A2>> for DoubleRNSRingBase<NumberRing, A1>
    where NumberRing: HENumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
{
    type Homomorphism = Vec<<ZnBase as CanHomFrom<ZnBase>>::Homomorphism>;

    fn has_canonical_hom(&self, from: &DoubleRNSRingBase<NumberRing, A2>) -> Option<Self::Homomorphism> {
        if self.base_ring().len() == from.base_ring().len() && self.number_ring() == from.number_ring() {
            (0..self.base_ring().len()).map(|i| self.base_ring().at(i).get_ring().has_canonical_hom(from.base_ring().at(i).get_ring()).ok_or(())).collect::<Result<Vec<_>, ()>>().ok()
        } else {
            None
        }
    }

    fn map_in(&self, from: &DoubleRNSRingBase<NumberRing, A2>, el: <DoubleRNSRingBase<NumberRing, A2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.map_in_ref(from, &el, hom)
    }

    fn map_in_ref(&self, from: &DoubleRNSRingBase<NumberRing, A2>, el: &<DoubleRNSRingBase<NumberRing, A2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.element_len(), self.allocator.clone());
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.rank() {
                result.push(Zp.get_ring().map_in_ref(from.base_ring().at(i).get_ring(), &el.el_wrt_mult_basis[i * self.rank() + j], &hom[i]));
            }
        }
        DoubleRNSEl {
            el_wrt_mult_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }
}

impl<NumberRing, A1, A2, C2> CanHomFrom<SingleRNSRingBase<NumberRing, A2, C2>> for DoubleRNSRingBase<NumberRing, A1>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnBase>
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
        self.do_fft(self.map_in_from_singlerns(from, el, hom))
    }
}

impl<NumberRing, A1, A2, C2> CanIsoFromTo<SingleRNSRingBase<NumberRing, A2, C2>> for DoubleRNSRingBase<NumberRing, A1>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnBase>
{
    type Isomorphism = Vec<<ZnBase as CanIsoFromTo<ZnBase>>::Isomorphism>;

    fn has_canonical_iso(&self, from: &SingleRNSRingBase<NumberRing, A2, C2>) -> Option<Self::Isomorphism> {
        if self.base_ring().len() == from.base_ring().len() && self.number_ring() == from.number_ring() {
            (0..self.base_ring().len()).map(|i| self.base_ring().at(i).get_ring().has_canonical_iso(from.base_ring().at(i).get_ring()).ok_or(())).collect::<Result<Vec<_>, ()>>().ok()
        } else {
            None
        }
    }

    fn map_out(&self, from: &SingleRNSRingBase<NumberRing, A2, C2>, el: <Self as RingBase>::Element, iso: &Self::Isomorphism) -> <SingleRNSRingBase<NumberRing, A2, C2> as RingBase>::Element {
        self.map_out_to_singlerns(from, self.undo_fft(el), iso)
    }
}

impl<NumberRing, A1, A2> CanIsoFromTo<DoubleRNSRingBase<NumberRing, A2>> for DoubleRNSRingBase<NumberRing, A1>
    where NumberRing: HENumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
{
    type Isomorphism = Vec<<ZnBase as CanIsoFromTo<ZnBase>>::Isomorphism>;

    fn has_canonical_iso(&self, from: &DoubleRNSRingBase<NumberRing, A2>) -> Option<Self::Isomorphism> {
        if self.base_ring().len() == from.base_ring().len() && self.number_ring() == from.number_ring() {
            (0..self.base_ring().len()).map(|i| self.base_ring().at(i).get_ring().has_canonical_iso(from.base_ring().at(i).get_ring()).ok_or(())).collect::<Result<Vec<_>, ()>>().ok()
        } else {
            None
        }
    }

    fn map_out(&self, from: &DoubleRNSRingBase<NumberRing, A2>, el: Self::Element, iso: &Self::Isomorphism) -> <DoubleRNSRingBase<NumberRing, A2> as RingBase>::Element {
        let mut result = Vec::with_capacity_in(from.element_len(), from.allocator.clone());
        for (i, Zp) in self.base_ring().as_iter().enumerate() {
            for j in 0..self.rank() {
                result.push(Zp.get_ring().map_out(from.base_ring().at(i).get_ring(), Zp.clone_el(&el.el_wrt_mult_basis[i * self.rank() + j]), &iso[i]));
            }
        }
        DoubleRNSEl {
            el_wrt_mult_basis: result,
            number_ring: PhantomData,
            allocator: PhantomData
        }
    }
}

#[cfg(any(test, feature = "generic_tests"))]
pub fn test_with_number_ring<NumberRing: Clone + HECyclotomicNumberRing>(number_ring: NumberRing) {
    use feanor_math::algorithms::eea::signed_lcm;
    use feanor_math::assert_el_eq;
    use feanor_math::primitive_int::*;

    let required_root_of_unity = signed_lcm(
        number_ring.mod_p_required_root_of_unity() as i64, 
        1 << StaticRing::<i64>::RING.abs_log2_ceil(&(number_ring.m() as i64)).unwrap() + 2, 
        StaticRing::<i64>::RING
    );
    let p1 = largest_prime_leq_congruent_to_one(20000, required_root_of_unity).unwrap();
    let p2 = largest_prime_leq_congruent_to_one(p1 - 1, required_root_of_unity).unwrap();
    assert!(p1 != p2);
    let rank = number_ring.rank();
    let base_ring = zn_rns::Zn::new(vec![Zn::new(p1 as u64), Zn::new(p2 as u64)], BigIntRing::RING);
    let ring = DoubleRNSRingBase::new(number_ring.clone(), base_ring.clone());

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

    let single_rns_ring = <SingleRNSRing<NumberRing> as RingStore>::Type::new(number_ring.clone(), base_ring.clone());
    feanor_math::ring::generic_tests::test_hom_axioms(&ring, &single_rns_ring, elements.iter().map(|x| ring.clone_el(x)));

    let dropped_rns_factor_ring = DoubleRNSRingBase::new(number_ring.clone(), zn_rns::Zn::new(vec![Zn::new(p2 as u64)], BigIntRing::RING));
    for a in &elements {
        assert_el_eq!(
            &dropped_rns_factor_ring,
            dropped_rns_factor_ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| dropped_rns_factor_ring.base_ring().from_congruence([*ring.base_ring().get_congruence(&c).at(1)].into_iter()))),
            dropped_rns_factor_ring.get_ring().drop_rns_factor_element(ring.get_ring(), &[0], a)
        );
        assert_el_eq!(
            &dropped_rns_factor_ring,
            dropped_rns_factor_ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| dropped_rns_factor_ring.base_ring().from_congruence([*ring.base_ring().get_congruence(&c).at(1)].into_iter()))),
            dropped_rns_factor_ring.get_ring().do_fft(dropped_rns_factor_ring.get_ring().drop_rns_factor_non_fft_element(ring.get_ring(), &[0], &ring.get_ring().undo_fft(ring.clone_el(a))))
        );
    }
    for a in &elements {
        let dropped_factor_a = dropped_rns_factor_ring.get_ring().drop_rns_factor_element(ring.get_ring(), &[0], a);
        assert_el_eq!(
            &ring,
            ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| ring.base_ring().from_congruence([ring.base_ring().at(0).zero(), *ring.base_ring().get_congruence(&c).at(1)].into_iter()))),
            ring.get_ring().add_rns_factor_element(dropped_rns_factor_ring.get_ring(), &[0], &dropped_factor_a)
        );
        assert_el_eq!(
            &ring,
            ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| ring.base_ring().from_congruence([ring.base_ring().at(0).zero(), *ring.base_ring().get_congruence(&c).at(1)].into_iter()))),
            ring.get_ring().do_fft(ring.get_ring().add_rns_factor_non_fft_element(dropped_rns_factor_ring.get_ring(), &[0], &dropped_rns_factor_ring.get_ring().undo_fft(dropped_factor_a)))
        );
    }

    let dropped_rns_factor_ring = DoubleRNSRingBase::new(number_ring.clone(), zn_rns::Zn::new(vec![Zn::new(p1 as u64)], BigIntRing::RING));
    for a in &elements {
        assert_el_eq!(
            &dropped_rns_factor_ring,
            dropped_rns_factor_ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| dropped_rns_factor_ring.base_ring().from_congruence([*ring.base_ring().get_congruence(&c).at(0)].into_iter()))),
            dropped_rns_factor_ring.get_ring().drop_rns_factor_element(ring.get_ring(), &[1], a)
        );
        assert_el_eq!(
            &dropped_rns_factor_ring,
            dropped_rns_factor_ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| dropped_rns_factor_ring.base_ring().from_congruence([*ring.base_ring().get_congruence(&c).at(0)].into_iter()))),
            dropped_rns_factor_ring.get_ring().do_fft(dropped_rns_factor_ring.get_ring().drop_rns_factor_non_fft_element(ring.get_ring(), &[1], &ring.get_ring().undo_fft(ring.clone_el(a))))
        );
    }
    for a in &elements {
        let dropped_factor_a = dropped_rns_factor_ring.get_ring().drop_rns_factor_element(ring.get_ring(), &[1], a);
        assert_el_eq!(
            &ring,
            ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| ring.base_ring().from_congruence([*ring.base_ring().get_congruence(&c).at(0), ring.base_ring().at(1).zero()].into_iter()))),
            ring.get_ring().add_rns_factor_element(dropped_rns_factor_ring.get_ring(), &[1], &dropped_factor_a)
        );
        assert_el_eq!(
            &ring,
            ring.from_canonical_basis(ring.wrt_canonical_basis(a).iter().map(|c| ring.base_ring().from_congruence([*ring.base_ring().get_congruence(&c).at(0), ring.base_ring().at(1).zero()].into_iter()))),
            ring.get_ring().do_fft(ring.get_ring().add_rns_factor_non_fft_element(dropped_rns_factor_ring.get_ring(), &[1], &dropped_rns_factor_ring.get_ring().undo_fft(dropped_factor_a)))
        );
    }

    feanor_math::serialization::generic_tests::test_serialization(&ring, elements.iter().map(|x| ring.clone_el(x)));
}
