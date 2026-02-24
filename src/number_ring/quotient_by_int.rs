use std::alloc::{Allocator, Global};
use std::marker::PhantomData;

use feanor_math::algorithms::convolution::{ConvolutionAlgorithm, KaratsubaAlgorithm};
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::algorithms::extension_ops::create_multiplication_matrix;
use feanor_math::divisibility::DivisibilityRing;
use feanor_math::algorithms::convolution::STANDARD_CONVOLUTION;
use feanor_math::homomorphism::*;
use feanor_math::algorithms::linsolve::LinSolveRing;
use feanor_math::integer::*;
use feanor_math::iters::{multi_cartesian_product, MultiProduct};
use feanor_math::matrix::OwnedMatrix;
use feanor_math::rings::extension::{FreeAlgebra, FreeAlgebraStore};
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::zn::*;
use feanor_math::ring::*;
use feanor_math::seq::*;
use feanor_math::serialization::{SerializableElementRing, SerializeWithRing, DeserializeWithRing};
use feanor_math::rings::finite::*;
use feanor_math::specialization::{FiniteRingOperation, FiniteRingSpecializable};

use feanor_serde::newtype_struct::*;
use feanor_serde::seq::*;
use serde::{Deserializer, Serialize, Serializer};

use tracing::instrument;

use crate::number_ring::galois::*;
use crate::number_ring::poly_remainder::CyclotomicPolyReducer;
use crate::{number_ring::*, ZZi64};
use crate::prepared_mul::PreparedMultiplicationRing;
use crate::serde::de::DeserializeSeed;
use crate::ZZbig;

///
/// Implementation of `R/tR` for any modulus `t in R` (without restriction on the
/// splitting behaviour of `t` over `R`).
/// 
/// # Implementation and assumptions
/// 
/// Currently, Fheanor only supports cyclotomic number rings, thus this implementation
/// always represents a ring of the form `(Z/qZ)[X]/(Phi_m(X))`. We assume that the
/// generating polynomial of the given number ring is indeed `Phi_m(X)`. In theory it
/// might not be - there can be other generators - but I don't think these other cases
/// are relevant, and the constructor will panic when instantiated with other polynomials. 
/// 
/// We then store ring elements as polynomials modulo `X^m - 1`, i.e. not completely
/// reduced, unless when required (e.g. in [`FreeAlgebra::wrt_canonical_basis()`]).
/// 
pub struct NumberRingQuotientByIntBase<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> 
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase> + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    number_ring: NumberRing,
    galois_group: Subgroup<CyclotomicGaloisGroup>,
    allocator: A,
    reducer: CyclotomicPolyReducer<ZnTy, C>,
}

///
/// [`RingStore`] for [`NumberRingQuotientByIntBase`]
/// 
pub type NumberRingQuotientByInt<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> = RingValue<NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>>;

pub struct NumberRingQuotientByIntEl<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> 
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase> + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    ring: PhantomData<NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>>,
    // if true, this means only the first `phi(m)` entries in `data` are nonzero, i.e.
    // the representative is completely reduced modulo `Phi_m(X)` 
    reduced: bool,
    data: Vec<El<ZnTy>, A>
}

pub struct NumberRingQuotientByIntPreparedMultiplicant<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> 
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase> + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    ring: PhantomData<NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>>,
    data: C::PreparedConvolutionOperand
}

impl<NumberRing, ZnTy> NumberRingQuotientByIntBase<NumberRing, ZnTy>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>
{
    pub fn new(number_ring: NumberRing, base_ring: ZnTy) -> RingValue<Self> {
        Self::create(number_ring, base_ring, Global, STANDARD_CONVOLUTION)
    }
}

impl<NumberRing, ZnTy, A, C> NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    #[instrument(skip_all)]
    pub fn create(number_ring: NumberRing, base_ring: ZnTy, allocator: A, convolution: C) -> RingValue<Self> {
        let poly_ring = DensePolyRing::new(base_ring, "X");
        let ZZX = DensePolyRing::new(ZZbig, "X");
        assert!(ZZX.eq_el(&number_ring.generating_poly(&ZZX), &cyclotomic_polynomial(&ZZX, number_ring.galois_group().m() as usize)));
        let acting_galois_group = number_ring.galois_group().clone().into().full_subgroup();
        let reducer = CyclotomicPolyReducer::new(poly_ring.into().into_base_ring(), number_ring.galois_group().m(), convolution);
        return RingValue::from(Self {
            allocator: allocator,
            galois_group: acting_galois_group,
            number_ring: number_ring,
            reducer: reducer
        });
    }
}

impl<NumberRing, ZnTy, A, C> NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn convolution(&self) -> &C {
        self.reducer.convolution()
    }

    fn m(&self) -> usize {
        self.acting_galois_group().m() as usize
    }
}

impl<NumberRing, ZnTy, A, C> Clone for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type> + Clone
{
    fn clone(&self) -> Self {
        Self {
            allocator: self.allocator.clone(),
            number_ring: self.number_ring.clone(),
            reducer: self.reducer.clone(),
            galois_group: self.galois_group.clone()
        }
    }
}

impl<NumberRing, ZnTy, A, C> NumberRingQuotient for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type NumberRing = NumberRing;

    fn number_ring(&self) -> &Self::NumberRing {
        &self.number_ring
    }

    fn acting_galois_group(&self) -> &Subgroup<CyclotomicGaloisGroup> {
        &self.galois_group
    }

    #[instrument(skip_all)]
    fn apply_galois_action(&self, x: &Self::Element, g: &GaloisGroupEl) -> Self::Element {
        let m = self.m();
        let mut result = Vec::with_capacity_in(m, self.allocator.clone());
        result.resize_with(m, || self.base_ring().zero());
        let Zm = self.acting_galois_group().underlying_ring();
        let mod_m = Zm.can_hom(&ZZi64).unwrap();
        let g_Zm = self.acting_galois_group().as_ring_el(g);
        for i in 0..m {
            result[Zm.smallest_positive_lift(mod_m.mul_ref_map(g_Zm, &(i as i64))) as usize] = self.base_ring().clone_el(&x.data[i]);
        }
        return NumberRingQuotientByIntEl {
            data: result,
            reduced: false,
            ring: PhantomData
        };
    }
}

impl<NumberRing, ZnTy, A, C> PreparedMultiplicationRing for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type PreparedMultiplicant = NumberRingQuotientByIntPreparedMultiplicant<NumberRing, ZnTy, A, C>;

    #[instrument(skip_all)]
    fn prepare_multiplicant(&self, x: &Self::Element) -> Self::PreparedMultiplicant {
        NumberRingQuotientByIntPreparedMultiplicant {
            ring: PhantomData,
            data: self.convolution().prepare_convolution_operand(&x.data, Some(2 * self.m()), self.base_ring())
        }
    }

    #[instrument(skip_all)]
    fn mul_prepared(&self, lhs: &Self::Element, lhs_prep: Option<&Self::PreparedMultiplicant>, rhs: &Self::Element, rhs_prep: Option<&Self::PreparedMultiplicant>) -> Self::Element {
        assert_eq!(self.m(), lhs.data.len());
        assert_eq!(self.m(), rhs.data.len());
        let mut result = Vec::with_capacity_in(2 * self.m(), self.allocator.clone());
        result.resize_with(2 * self.m(), || self.base_ring().zero());
        self.convolution().compute_convolution_prepared(&lhs.data, lhs_prep.map(|x| &x.data), &rhs.data, rhs_prep.map(|x| &x.data), &mut result, self.base_ring());
        let (part1, part2) = result.split_at_mut(self.m());
        for (dst, src) in part1.iter_mut().zip(part2.iter()) {
            self.base_ring().add_assign_ref(dst, src);
        }
        result.truncate(self.m());
        return NumberRingQuotientByIntEl {
            ring: PhantomData,
            reduced: false,
            data: result
        };
    }

    #[instrument(skip_all)]
    fn inner_product_prepared<'a, I>(&self, parts: I) -> Self::Element
        where I: IntoIterator<Item = (&'a Self::Element, Option<&'a Self::PreparedMultiplicant>, &'a Self::Element, Option<&'a Self::PreparedMultiplicant>)>,
            I::IntoIter: ExactSizeIterator,
            Self: 'a
    {
        let mut result = Vec::with_capacity_in(2 * self.m(), self.allocator.clone());
        result.resize_with(2 * self.m(), || self.base_ring().zero());
        self.convolution().compute_convolution_sum(parts.into_iter().map(|(lhs, lhs_prep, rhs, rhs_prep)| {
            assert_eq!(self.m(), lhs.data.len());
            assert_eq!(self.m(), rhs.data.len());
            (&lhs.data, lhs_prep.map(|x| &x.data), &rhs.data, rhs_prep.map(|x| &x.data))
        }), &mut result, self.base_ring());
        self.reducer.remainder(&mut result);
        result.truncate(self.m());
        return NumberRingQuotientByIntEl {
            ring: PhantomData,
            reduced: false,
            data: result
        };
    }
}

impl<NumberRing, ZnTy, A, C> PartialEq for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn eq(&self, other: &Self) -> bool {
        self.number_ring == other.number_ring && self.base_ring().get_ring() == other.base_ring().get_ring()
    }
}

impl<NumberRing, ZnTy, A, C> RingBase for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type Element = NumberRingQuotientByIntEl<NumberRing, ZnTy, A, C>;

    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.m(), self.allocator.clone());
        result.extend(val.data.iter().map(|x| self.base_ring().clone_el(x)));
        return NumberRingQuotientByIntEl {
            data: result,
            reduced: val.reduced,
            ring: PhantomData
        };
    }

    fn add_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        assert_eq!(lhs.data.len(), self.m());
        assert_eq!(rhs.data.len(), self.m());
        lhs.reduced &= rhs.reduced;
        for (i, x) in rhs.data.into_iter().enumerate() {
            self.base_ring().add_assign(&mut lhs.data[i], x)
        }
    }

    fn add_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        assert_eq!(lhs.data.len(), self.m());
        assert_eq!(rhs.data.len(), self.m());
        lhs.reduced &= rhs.reduced;
        for (i, x) in (&rhs.data).into_iter().enumerate() {
            self.base_ring().add_assign_ref(&mut lhs.data[i], x)
        }
    }

    fn sub_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        assert_eq!(lhs.data.len(), self.m());
        assert_eq!(rhs.data.len(), self.m());
        lhs.reduced &= rhs.reduced;
        for (i, x) in (&rhs.data).into_iter().enumerate() {
            self.base_ring().sub_assign_ref(&mut lhs.data[i], x)
        }
    }

    fn negate_inplace(&self, lhs: &mut Self::Element) {
        assert_eq!(lhs.data.len(), self.m());
        for i in 0..self.m() {
            self.base_ring().negate_inplace(&mut lhs.data[i]);
        }
    }

    fn mul_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        *lhs = self.mul_ref(lhs, &rhs);
    }

    fn mul_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        *lhs = self.mul_ref(lhs, rhs);
    }

    #[instrument(skip_all)]
    fn mul_ref(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        assert_eq!(lhs.data.len(), self.m());
        assert_eq!(rhs.data.len(), self.m());
        let mut result = Vec::with_capacity_in(2 * self.m(), self.allocator.clone());
        result.resize_with(2 * self.m(), || self.base_ring().zero());
        self.convolution().compute_convolution_prepared(&lhs.data, None, &rhs.data, None, &mut result, self.base_ring());
        let (part1, part2) = result.split_at_mut(self.m());
        for (dst, src) in part1.iter_mut().zip(part2.iter()) {
            self.base_ring().add_assign_ref(dst, src);
        }
        result.truncate(self.m());
        let result = NumberRingQuotientByIntEl {
            ring: PhantomData,
            reduced: false,
            data: result
        };
        return result;
    }
    
    fn from_int(&self, value: i32) -> Self::Element {
        self.from(self.base_ring().get_ring().from_int(value))
    }

    #[instrument(skip_all)]
    fn eq_el(&self, lhs: &Self::Element, rhs: &Self::Element) -> bool {
        assert_eq!(lhs.data.len(), self.m());
        assert_eq!(rhs.data.len(), self.m());
        let mut difference = self.sub_ref(lhs, rhs);
        if !difference.reduced {
            self.reducer.remainder(&mut difference.data);
        }
        for i in 0..self.rank() {
            if !self.base_ring().is_zero(&difference.data[i]) {
                return false;
            }
        }
        return true;
    }

    fn zero(&self) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.m(), self.allocator.clone());
        result.extend((0..self.m()).map(|_| self.base_ring().zero()));
        return NumberRingQuotientByIntEl {
            data: result,
            reduced: true,
            ring: PhantomData
        };
    }
    
    fn is_commutative(&self) -> bool { true }
    fn is_noetherian(&self) -> bool { true }
    fn is_approximate(&self) -> bool { false }

    fn dbg<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>) -> std::fmt::Result {
        self.dbg_within(value, out, EnvBindingStrength::Weakest)
    }

    fn dbg_within<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>, _env: EnvBindingStrength) -> std::fmt::Result {
        let poly_ring = DensePolyRing::new(self.base_ring(), "X");
        let poly = RingRef::new(self).poly_repr(&poly_ring, value, self.base_ring().identity());
        poly_ring.get_ring().dbg(&poly, out)
    }

    fn characteristic<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        self.base_ring().characteristic(ZZ)
    }
}

impl<NumberRing, ZnTy, A, C> RingExtension for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type BaseRing = ZnTy;

    fn base_ring<'a>(&'a self) -> &'a Self::BaseRing {
        self.reducer.base_ring()
    }

    fn from(&self, x: El<Self::BaseRing>) -> Self::Element {
        let mut result = self.zero();
        result.reduced = true;
        result.data[0] = x;
        return result;
    }

    fn fma_base(&self, lhs: &Self::Element, rhs: &El<Self::BaseRing>, summand: Self::Element) -> Self::Element {
        assert_eq!(lhs.data.len(), self.m());
        assert_eq!(summand.data.len(), self.m());
        
        let mut result = Vec::with_capacity_in(self.rank(), self.allocator.clone());
        result.extend(summand.data.into_iter().enumerate().map(|(i, x)| self.base_ring().fma(&lhs.data[i], rhs, x)));
        return NumberRingQuotientByIntEl {
            data: result,
            reduced: false,
            ring: PhantomData
        };
    }

    fn mul_assign_base(&self, lhs: &mut Self::Element, rhs: &El<Self::BaseRing>) {
        assert_eq!(lhs.data.len(), self.m());
        for x in &mut lhs.data {
            self.base_ring().mul_assign_ref(x, rhs);
        }
    }

    fn mul_assign_base_through_hom<S: ?Sized + RingBase, H: Homomorphism<S, <Self::BaseRing as RingStore>::Type>>(&self, lhs: &mut Self::Element, rhs: &S::Element, hom: H) {
        assert_eq!(lhs.data.len(), self.m());
        for x in &mut lhs.data {
            hom.mul_assign_ref_map(x, rhs);
        }
    }
}

impl<NumberRing, ZnTy, A, C> FreeAlgebra for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type VectorRepresentation<'a> = CloneElFn<Vec<El<ZnTy>, A>, El<ZnTy>, CloneRingEl<&'a ZnTy>>
        where Self: 'a;

    fn from_canonical_basis<V>(&self, vec: V) -> Self::Element
        where V: IntoIterator<Item = El<Self::BaseRing>>
    {
        let mut result = Vec::with_capacity_in(self.m(), self.allocator.clone());
        result.extend(vec);
        assert_eq!(result.len(), self.rank());
        result.resize_with(self.m(), || self.base_ring().zero());
        return NumberRingQuotientByIntEl {
            data: result,
            reduced: true,
            ring: PhantomData
        };
    }

    fn from_canonical_basis_extended<V>(&self, vec: V) -> Self::Element
        where V: IntoIterator<Item = El<Self::BaseRing>>
    {
        let m = self.m();
        let mut result = self.zero();
        result.reduced = false;
        for (i, c) in vec.into_iter().enumerate() {
            self.base_ring().add_assign(&mut result.data[i % m], c);
        }
        return result;
    }

    #[instrument(skip_all)]
    fn wrt_canonical_basis<'a>(&'a self, el: &'a Self::Element) -> Self::VectorRepresentation<'a> {
        let mut el_reduced = self.clone_el(el);
        if !el_reduced.reduced {
            self.reducer.remainder(&mut el_reduced.data);
        }
        el_reduced.data.truncate(self.rank());
        return el_reduced.data.into_clone_ring_els(self.base_ring());
    }

    fn canonical_gen(&self) -> Self::Element {
        let mut result = self.zero();
        result.reduced = true;
        if self.rank() > 1 {
            result.data[1] = self.base_ring().one();
        } else {
            result.data[0] = self.base_ring().one();
        }
        return result;
    }

    fn rank(&self) -> usize {
        self.number_ring.rank()
    }
}

pub struct WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    ring: &'a NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>,
}

impl<'a, NumberRing, ZnTy, A, C> Copy for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{}

impl<'a, NumberRing, ZnTy, A, C> Clone for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, 'b, NumberRing, ZnTy, A, C> FnOnce<(&'b [El<ZnTy>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type Output = El<NumberRingQuotientByInt<NumberRing, ZnTy, A, C>>;

    extern "rust-call" fn call_once(self, args: (&'b [El<ZnTy>],)) -> Self::Output {
        self.call(args)
    }
}

impl<'a, 'b, NumberRing, ZnTy, A, C> FnMut<(&'b [El<ZnTy>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    extern "rust-call" fn call_mut(&mut self, args: (&'b [El<ZnTy>],)) -> Self::Output {
        self.call(args)
    }
}

impl<'a, 'b, NumberRing, ZnTy, A, C> Fn<(&'b [El<ZnTy>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    extern "rust-call" fn call(&self, args: (&'b [El<ZnTy>],)) -> Self::Output {
        self.ring.from_canonical_basis(args.0.iter().map(|x| self.ring.base_ring().clone_el(x)))
    }
}

impl<NumberRing, ZnTy, A, C> FiniteRingSpecializable for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn specialize<O: FiniteRingOperation<Self>>(op: O) -> O::Output {
        op.execute()
    }
}

impl<NumberRing, ZnTy, A, C> FiniteRing for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type ElementsIter<'a> = MultiProduct<<ZnTy::Type as FiniteRing>::ElementsIter<'a>, WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>, CloneRingEl<&'a ZnTy>, Self::Element>
        where Self: 'a;

    fn elements<'a>(&'a self) -> Self::ElementsIter<'a> {
        multi_cartesian_product((0..self.rank()).map(|_| self.base_ring().elements()), WRTCanonicalBasisElementCreator { ring: self }, CloneRingEl(self.base_ring()))
    }

    fn random_element<G: FnMut() -> u64>(&self, mut rng: G) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.m(), self.allocator.clone());
        result.extend((0..self.rank()).map(|_| self.base_ring().random_element(&mut rng)));
        result.resize_with(self.m(), || self.base_ring().zero());
        return NumberRingQuotientByIntEl {
            data: result,
            reduced: true,
            ring: PhantomData
        };
    }

    fn size<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        let characteristic = self.base_ring().size(ZZ)?;
        if ZZ.get_ring().representable_bits().is_none() || ZZ.get_ring().representable_bits().unwrap() >= self.rank() * ZZ.abs_log2_ceil(&characteristic).unwrap() {
            Some(ZZ.pow(characteristic, self.rank()))
        } else {
            None
        }
    }
}

impl<NumberRing, ZnTy, A, C> DivisibilityRing for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn checked_left_div(&self, lhs: &Self::Element, rhs: &Self::Element) -> Option<Self::Element> {
        let mut mul_matrix: OwnedMatrix<_> = create_multiplication_matrix(RingRef::new(self), rhs, Global);
        let data = self.wrt_canonical_basis(&lhs);
        let mut lhs_matrix: OwnedMatrix<_> = OwnedMatrix::from_fn(self.rank(), 1, |i, _| data.at(i));

        let mut solution: OwnedMatrix<_> = OwnedMatrix::zero(self.rank(), 1, self.base_ring());
        let has_sol = self.base_ring().get_ring().solve_right(mul_matrix.data_mut(), lhs_matrix.data_mut(), solution.data_mut(), Global);
        if has_sol.is_solved() {
            return Some(self.from_canonical_basis((0..self.rank()).map(|i| self.base_ring().clone_el(solution.at(i, 0)))));
        } else {
            return None;
        }
    }
}

impl<NumberRing, ZnTy, A, C> SerializableElementRing for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: SerializableElementRing + ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    #[instrument(skip_all)]
    fn serialize<S>(&self, el: &Self::Element, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        let mut el_reduced = self.clone_el(el);
        if !el_reduced.reduced {
            self.reducer.remainder(&mut el_reduced.data);
        }
        SerializableNewtypeStruct::new("RingEl", SerializableSeq::new_with_len(el_reduced.data[..self.rank()].iter().map(|x| SerializeWithRing::new(x, self.base_ring())), self.rank())).serialize(serializer)
    }

    #[instrument(skip_all)]
    fn deserialize<'de, D>(&self, deserializer: D) -> Result<Self::Element, D::Error>
        where D: Deserializer<'de> 
    {
        let mut result = DeserializeSeedNewtypeStruct::new("RingEl", DeserializeSeedSeq::new(
            (0..(self.rank() + 1)).map(|_| DeserializeWithRing::new(self.base_ring())),
            Vec::with_capacity_in(self.m(), self.allocator.clone()),
            |mut current, next| { current.push(next); current }
        )).deserialize(deserializer)?;
        if result.len() != self.rank() {
            return Err(serde::de::Error::invalid_length(result.len(), &format!("expected {} elements", self.rank()).as_str()));
        }
        result.resize_with(self.m(), || self.base_ring().zero());
        return Ok(NumberRingQuotientByIntEl {
            data: result,
            reduced: true,
            ring: PhantomData
        });
    }
}

impl<NumberRing, ZnTy, A, C> CanHomFrom<BigIntRingBase> for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type Homomorphism = <ZnTy::Type as CanHomFrom<BigIntRingBase>>::Homomorphism;

    fn has_canonical_hom(&self, from: &BigIntRingBase) -> Option<Self::Homomorphism> {
        self.base_ring().get_ring().has_canonical_hom(from)
    }

    fn map_in(&self, from: &BigIntRingBase, el: El<BigIntRing>, hom: &Self::Homomorphism) -> Self::Element {
        self.from(self.base_ring().get_ring().map_in(from, el, hom))
    }

    fn mul_assign_map_in(&self, from: &BigIntRingBase, lhs: &mut Self::Element, rhs: <BigIntRingBase as RingBase>::Element, hom: &Self::Homomorphism) {
        self.mul_assign_base(lhs, &self.base_ring().get_ring().map_in(from, rhs, hom));
    }

    fn mul_assign_map_in_ref(&self, from: &BigIntRingBase, lhs: &mut Self::Element, rhs: &<BigIntRingBase as RingBase>::Element, hom: &Self::Homomorphism) {
        self.mul_assign_base(lhs, &self.base_ring().get_ring().map_in_ref(from, rhs, hom));
    }
}

impl<NumberRing, ZnTy1, ZnTy2, A1, A2, C1, C2> CanHomFrom<NumberRingQuotientByIntBase<NumberRing, ZnTy2, A2, C2>> for NumberRingQuotientByIntBase<NumberRing, ZnTy1, A1, C1>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy1: RingStore + Clone,
        ZnTy1::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A1: Allocator + Clone,
        C1: ConvolutionAlgorithm<ZnTy1::Type> + Clone,
        ZnTy2: RingStore + Clone,
        ZnTy2::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnTy2::Type> + Clone,
        ZnTy1::Type: CanHomFrom<ZnTy2::Type>
{
    type Homomorphism = <ZnTy1::Type as CanHomFrom<ZnTy2::Type>>::Homomorphism;

    fn has_canonical_hom(&self, from: &NumberRingQuotientByIntBase<NumberRing, ZnTy2, A2, C2>) -> Option<Self::Homomorphism> {
        if self.number_ring == from.number_ring {
            self.base_ring().get_ring().has_canonical_hom(from.base_ring().get_ring())
        } else {
            None
        }
    }

    fn map_in(&self, from: &NumberRingQuotientByIntBase<NumberRing, ZnTy2, A2, C2>, el: <NumberRingQuotientByIntBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        assert_eq!(el.data.len(), self.m());
        let mut result = Vec::with_capacity_in(self.m(), self.allocator.clone());
        result.extend((0..self.m()).map(|i| self.base_ring().get_ring().map_in(from.base_ring().get_ring(), from.base_ring().clone_el(&el.data[i]), hom)));
        return NumberRingQuotientByIntEl {
            data: result,
            reduced: el.reduced,
            ring: PhantomData
        };
    }
}

impl<NumberRing, ZnTy1, ZnTy2, A1, A2, C1, C2> CanIsoFromTo<NumberRingQuotientByIntBase<NumberRing, ZnTy2, A2, C2>> for NumberRingQuotientByIntBase<NumberRing, ZnTy1, A1, C1>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy1: RingStore + Clone,
        ZnTy1::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A1: Allocator + Clone,
        C1: ConvolutionAlgorithm<ZnTy1::Type> + Clone,
        ZnTy2: RingStore + Clone,
        ZnTy2::Type: ZnRing + CanHomFrom<BigIntRingBase>,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnTy2::Type> + Clone,
        ZnTy1::Type: CanIsoFromTo<ZnTy2::Type>
{
    type Isomorphism = <ZnTy1::Type as CanIsoFromTo<ZnTy2::Type>>::Isomorphism;

    fn has_canonical_iso(&self, from: &NumberRingQuotientByIntBase<NumberRing, ZnTy2, A2, C2>) -> Option<Self::Isomorphism> {
        if self.number_ring == from.number_ring {
            self.base_ring().get_ring().has_canonical_iso(from.base_ring().get_ring())
        } else {
            None
        }
    }

    fn map_out(&self, from: &NumberRingQuotientByIntBase<NumberRing, ZnTy2, A2, C2>, el: Self::Element, iso: &Self::Isomorphism) -> <NumberRingQuotientByIntBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element {
        assert_eq!(el.data.len(), self.m());
        let mut result = Vec::with_capacity_in(self.m(), from.allocator.clone());
        result.extend((0..self.m()).map(|i| self.base_ring().get_ring().map_out(from.base_ring().get_ring(), self.base_ring().clone_el(&el.data[i]), iso)));
        return NumberRingQuotientByIntEl {
            data: result,
            reduced: el.reduced,
            ring: PhantomData
        };
    }
}

#[cfg(test)]
pub fn test_with_number_ring<NumberRing: AbstractNumberRing>(number_ring: NumberRing) {

    let base_ring = zn_64::Zn::new(5);
    let rank = number_ring.rank();
    let ring = NumberRingQuotientByIntBase::new(number_ring, base_ring);

    let elements = vec![
        ring.zero(),
        ring.one(),
        ring.neg_one(),
        ring.int_hom().map(2),
        ring.canonical_gen(),
        ring.pow(ring.canonical_gen(), 2),
        ring.pow(ring.canonical_gen(), rank - 1),
        ring.int_hom().mul_map(ring.canonical_gen(), 2),
        ring.int_hom().mul_map(ring.pow(ring.canonical_gen(), rank - 1), 2)
    ];

    feanor_math::ring::generic_tests::test_ring_axioms(&ring, elements.iter().map(|x| ring.clone_el(x)));
    feanor_math::ring::generic_tests::test_self_iso(&ring, elements.iter().map(|x| ring.clone_el(x)));
    feanor_math::rings::extension::generic_tests::test_free_algebra_axioms(&ring);
    feanor_math::serialization::generic_tests::test_serialization(&ring, elements.iter().map(|x| ring.clone_el(x)));
}
