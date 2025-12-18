use std::alloc::{Allocator, Global};
use std::marker::PhantomData;

use feanor_math::algorithms::convolution::{ConvolutionAlgorithm, KaratsubaAlgorithm};
use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::algorithms::extension_ops::create_multiplication_matrix;
use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::algorithms::poly_gcd::hensel::hensel_lift_factorization;
use feanor_math::computation::DontObserve;
use feanor_math::divisibility::*;
use feanor_math::algorithms::convolution::STANDARD_CONVOLUTION;
use feanor_math::homomorphism::{CanHomFrom, CanIsoFromTo, Homomorphism};
use feanor_math::algorithms::linsolve::LinSolveRing;
use feanor_math::integer::*;
use feanor_math::iters::{multi_cartesian_product, MultiProduct};
use feanor_math::matrix::OwnedMatrix;
use feanor_math::reduce_lift::poly_factor_gcd::IntegersWithLocalZnQuotient;
use feanor_math::rings::extension::{FreeAlgebra, FreeAlgebraStore};
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::poly::PolyRingStore;
use feanor_math::pid::PrincipalIdealRingStore;
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
use crate::number_ring::poly_remainder::BarettPolyReducer;
use crate::number_ring::*;
use crate::prepared_mul::PreparedMultiplicationRing;
use crate::serde::de::DeserializeSeed;
use crate::*;

///
/// Implementation of `R/I` for any ideal `I` of the form `I = (p^e, t(ϑ)).
/// 
/// In this sense, this ring is more general than [`NumberRingQuotientByIntBase`],
/// since (when `t = p^e`) such an ideal `I` can also represent the integer setting
/// `I = (t)`. However, in these settings, it will be significantly less performant.
/// 
/// [`NumberRingQuotientByIntBase`]: crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase
/// 
pub struct NumberRingQuotientByIdealBase<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> 
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    number_ring: NumberRing,
    acting_galois_group: Subgroup<CyclotomicGaloisGroup>,
    generator_powers: Vec<NumberRingQuotientByIdealEl<NumberRing, ZnTy, A, C>>,
    allocator: A,
    reducer: BarettPolyReducer<ZnTy, C>,
}

///
/// [`RingStore`] for [`NumberRingQuotientByIdealBase`]
/// 
pub type NumberRingQuotientByIdeal<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> = RingValue<NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>>;

pub struct NumberRingQuotientByIdealEl<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> 
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    ring: PhantomData<NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>>,
    data: Vec<El<ZnTy>, A>
}

pub struct NumberRingQuotientPreparedMultiplicant<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> 
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    ring: PhantomData<NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>>,
    data: C::PreparedConvolutionOperand
}

impl<NumberRing, ZnTy> NumberRingQuotientByIdealBase<NumberRing, ZnTy>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn
{
    ///
    /// Creates the ring `R/I`, where `R` is the given number ring and `I = (p^e, t(ϑ))`,
    /// where `p^e` is the characteristic of the given polynomial ring (must be a prime power)
    /// and `t(X)` is the given monic polynomial.
    ///  
    pub fn new<const LOG: bool>(number_ring: NumberRing, poly_ring: DensePolyRing<ZnTy>, ideal_generator: El<DensePolyRing<ZnTy>>, acting_galois_group: Subgroup<CyclotomicGaloisGroup>) -> RingValue<Self> {
        Self::create::<LOG>(number_ring, poly_ring, ideal_generator, acting_galois_group, Global, STANDARD_CONVOLUTION)
    }
}

impl<NumberRing, ZnTy, A, C> NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    ///
    /// Creates the ring `R/I`, where `R` is the given number ring and `I = (p^e, t(ϑ))`,
    /// where `p^e` is the characteristic of the given polynomial ring (must be a prime power)
    /// and `t(X)` is the given monic polynomial.
    /// 
    /// # Why must `t` be monic?
    /// 
    /// First of all, it allows us to use straightforward Hensel lifting for the computations,
    /// thus greatly simplifying the implementation. However, it is also necessary in theory,
    /// since otherwise the ring would not be free anymore. 
    /// 
    /// Consider e.g. `(Z/p^2Z)[X]/(X^2, pX)`. This ring is not a free `Z/p^2Z`-module - observe
    /// that it has `p^3` entries, which is not a power of `p^2`.
    ///  
    /// # Algorithm
    /// 
    /// Consider the case `e = 1`, the more general case is handled via Hensel lifting (this
    /// requires that `t` is monic). Our assumption that the given ideal is `I = (p, t(ϑ))`
    /// makes things relatively simple. First, observe that then we have an isomorphism
    /// ```text
    ///   Fp[X]/(gcd_p(t, MiPo(ϑ))) -> R/I,  X -> ϑ
    /// ```
    /// We prove this now. We have `MiPo(ϑ) = f1 ... fr` modulo `p`. Thus, we find
    /// ```text
    ///   I = prod_i (p, fi(ϑ))^ki
    /// ```
    /// Since `p in I`, we see that every `ki in {0, 1}`, and since `p in (p^2, fi(ϑ)fj(ϑ))`,
    /// it follows that `I = (p, t(ϑ)) = (p, t'(ϑ))` for `t(X)' = prod_i fi(X)^ki`. Clearly,
    /// this implies an isomorphism `Fp[X]/(t'(X)) -> R/I`, so it is left to show that
    /// `t' = gcd_p(t, MiPo(ϑ))`. From `(p, t(ϑ)) = (p, t'(ϑ))`, we see that
    /// ```text
    ///   t = p a + b t' + c MiPo(ϑ)    and    t' = p a' + b' t + c' MiPo(ϑ)
    /// ```
    /// Thus `gcd_p(t, MiPo(ϑ)) | t'` and `t' | t` (since `t' | MiPo(ϑ)`) modulo `p`. The claim
    /// follows.
    /// 
    #[instrument(skip_all)]
    pub fn create<const LOG: bool>(number_ring: NumberRing, ZpeX: DensePolyRing<ZnTy>, ideal_generator: El<DensePolyRing<ZnTy>>, acting_galois_group: Subgroup<CyclotomicGaloisGroup>, allocator: A, convolution: C) -> RingValue<Self> {
        let Zpe = ZpeX.base_ring();
        assert!(Zpe.is_one(ZpeX.lc(&ideal_generator).unwrap()));
        let (p, e) = is_prime_power(Zpe.integer_ring(), Zpe.modulus()).unwrap();

        let ZZ = IntegersWithLocalZnQuotient::<ZnTy::Type>::new(Zpe.integer_ring(), p);
        let reduction_context = ZZ.reduction_context(e);

        let ZZX = DensePolyRing::new(RingRef::new(&ZZ), "X");
        let gen_mipo = number_ring.generating_poly(&ZZX);
        let Zpe_to_Fp = reduction_context.base_ring_to_field_iso(0).compose(reduction_context.intermediate_ring_to_field_reduction(0));
        let ZZ_to_Fp = reduction_context.base_ring_to_field_iso(0).compose(reduction_context.main_ring_to_field_reduction(0));
        assert!(Zpe_to_Fp.domain().get_ring() == ZpeX.base_ring().get_ring());
        let FpX = DensePolyRing::new(*Zpe_to_Fp.codomain(), "X");

        let gen_mipo_mod_p = FpX.lifted_hom(&ZZX, &ZZ_to_Fp).map_ref(&gen_mipo);
        let ideal_generator_mod_p = FpX.lifted_hom(&ZpeX, &Zpe_to_Fp).map_ref(&ideal_generator);
        let gcd = log_time::<_, _, LOG, _>("Computing gcd(t, f) mod p", |[]| FpX.normalize(FpX.ideal_gen(&gen_mipo_mod_p, &ideal_generator_mod_p)));
        assert!(FpX.degree(&gcd).unwrap() > 0);

        let other_factor = FpX.checked_div(&gen_mipo_mod_p, &gcd).unwrap();
        let factors = [gcd, other_factor];
        let [lifted_gcd, _] = log_time::<_, _, LOG, _>("Lifting gcd(t, f)", |[]| hensel_lift_factorization(
            &reduction_context.intermediate_ring_to_field_reduction(0),
            &ZpeX,
            &FpX,
            &ZpeX.lifted_hom(&ZZX, reduction_context.main_ring_to_intermediate_ring_reduction(0)).map(gen_mipo),
            &factors[..],
            DontObserve
        )).try_into().ok().unwrap();
        assert!(ZpeX.is_zero(&ZpeX.div_rem_monic(ideal_generator, &lifted_gcd).1));
        let rank = ZpeX.degree(&lifted_gcd).unwrap();
        assert_eq!(rank, acting_galois_group.group_order());

        let mut result = Self {
            acting_galois_group: acting_galois_group,
            allocator: allocator,
            generator_powers: Vec::new(),
            number_ring: number_ring,
            reducer: BarettPolyReducer::new(ZpeX, &lifted_gcd, 2 * rank - 2, convolution)
        };
        log_time::<_, _, LOG, _>("Computing Galois data", |[]| result.init_generator_powers());
        log_time::<_, _, LOG, _>("Checking acting Galois subgroup", |[]| result.check_galois_group());
        return RingValue::from(result);
    }

    #[instrument(skip_all)]
    fn check_galois_group(&self) {
        let Zm = self.acting_galois_group().underlying_ring();
        let ZZ_to_Zm = Zm.can_hom(&ZZi64).unwrap();
        let rank = self.rank();
        let generating_poly = self.reducer.modulus_coefficients();
        assert_eq!(rank + 1, generating_poly.len());
        
        // check that the galois group indeed fixes the ideal
        for g in self.acting_galois_group().enumerate_elements() {
            let mut poly_at_galois_conjugate = self.zero();
            for i in 0..generating_poly.len() {
                let power = Zm.smallest_positive_lift(Zm.mul_ref_snd(ZZ_to_Zm.map(i as i64), self.acting_galois_group().as_ring_el(&g))) as usize;
                poly_at_galois_conjugate = RingRef::new(self).inclusion().fma_map(&self.generator_powers[power], &generating_poly[i], poly_at_galois_conjugate);
            }
            assert!(
                self.is_zero(&poly_at_galois_conjugate),
                "the given Galois group does not fix the given ideal"                
            );
        }
    }

    #[instrument(skip_all)]
    fn init_generator_powers(&mut self) {
        let m = self.acting_galois_group().m() as usize;
        let rank = self.rank();
        let generating_poly = self.reducer.modulus_coefficients();
        assert_eq!(rank + 1, generating_poly.len());

        self.generator_powers.push(self.one());
        for _ in 1..m {
            let last = &self.generator_powers.last().unwrap().data;
            let mut new = Vec::with_capacity_in(self.rank(), self.allocator.clone());
            new.extend([
                self.base_ring().negate(self.base_ring().mul_ref(&last[rank - 1], &generating_poly[0]))
            ].into_iter().chain((1..self.rank()).map(|i| 
                self.base_ring().sub_ref_fst(&last[i - 1], self.base_ring().mul_ref(&last[rank - 1], &generating_poly[i]))
            )));
            self.generator_powers.push(NumberRingQuotientByIdealEl { ring: PhantomData, data: new });
        }
    }
}

impl<NumberRing, ZnTy, A, C> NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn convolution(&self) -> &C {
        self.reducer.convolution()
    }
}

impl<NumberRing, ZnTy, A, C> Clone for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing + Clone,
        ZnTy: RingStore + Clone,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type> + Clone
{
    fn clone(&self) -> Self {
        Self {
            allocator: self.allocator.clone(),
            number_ring: self.number_ring.clone(),
            reducer: self.reducer.clone(),
            acting_galois_group: self.acting_galois_group.clone(),
            generator_powers: self.generator_powers.iter().map(|x| self.clone_el(x)).collect()
        }
    }
}

impl<NumberRing, ZnTy, A, C> NumberRingQuotient for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type NumberRing = NumberRing;

    fn number_ring(&self) -> &Self::NumberRing {
        &self.number_ring
    }

    fn acting_galois_group(&self) -> &Subgroup<CyclotomicGaloisGroup> {
        &self.acting_galois_group
    }

    #[instrument(skip_all)]
    fn apply_galois_action(&self, x: &Self::Element, g: &GaloisGroupEl) -> Self::Element {
        assert!(self.acting_galois_group().dlog(g).is_some());
        let Zm = self.acting_galois_group().underlying_ring();
        let x_wrt_basis = self.wrt_canonical_basis(x);
        let mut result = self.zero();
        let mut current_idx = Zm.zero();
        for c in x_wrt_basis.iter() {
            result = RingRef::new(self).inclusion().fma_map(&self.generator_powers[Zm.smallest_positive_lift(current_idx) as usize], &c, result);
            Zm.add_assign_ref(&mut current_idx, self.acting_galois_group().as_ring_el(g));
        }
        return result;
    }
}

impl<NumberRing, ZnTy, A, C> PreparedMultiplicationRing for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type PreparedMultiplicant = NumberRingQuotientPreparedMultiplicant<NumberRing, ZnTy, A, C>;

    #[instrument(skip_all)]
    fn prepare_multiplicant(&self, x: &Self::Element) -> Self::PreparedMultiplicant {
        NumberRingQuotientPreparedMultiplicant {
            ring: PhantomData,
            data: self.convolution().prepare_convolution_operand(&x.data, Some(2 * self.rank()), self.base_ring())
        }
    }

    #[instrument(skip_all)]
    fn mul_prepared(&self, lhs: &Self::Element, lhs_prep: Option<&Self::PreparedMultiplicant>, rhs: &Self::Element, rhs_prep: Option<&Self::PreparedMultiplicant>) -> Self::Element {
        assert_eq!(self.rank(), lhs.data.len());
        assert_eq!(self.rank(), rhs.data.len());
        let mut result = Vec::with_capacity_in(2 * self.rank(), self.allocator.clone());
        result.resize_with(2 * self.rank(), || self.base_ring().zero());
        self.convolution().compute_convolution_prepared(&lhs.data, lhs_prep.map(|x| &x.data), &rhs.data, rhs_prep.map(|x| &x.data), &mut result, self.base_ring());
        self.reducer.remainder(&mut result);
        result.truncate(self.rank());
        return NumberRingQuotientByIdealEl {
            ring: PhantomData,
            data: result
        };
    }

    #[instrument(skip_all)]
    fn inner_product_prepared<'a, I>(&self, parts: I) -> Self::Element
        where I: IntoIterator<Item = (&'a Self::Element, Option<&'a Self::PreparedMultiplicant>, &'a Self::Element, Option<&'a Self::PreparedMultiplicant>)>,
            I::IntoIter: ExactSizeIterator,
            Self: 'a
    {
        let mut result = Vec::with_capacity_in(2 * self.rank(), self.allocator.clone());
        result.resize_with(2 * self.rank(), || self.base_ring().zero());
        self.convolution().compute_convolution_sum(parts.into_iter().map(|(lhs, lhs_prep, rhs, rhs_prep)| {
            assert_eq!(self.rank(), lhs.data.len());
            assert_eq!(self.rank(), rhs.data.len());
            (&lhs.data, lhs_prep.map(|x| &x.data), &rhs.data, rhs_prep.map(|x| &x.data))
        }), &mut result, self.base_ring());
        self.reducer.remainder(&mut result);
        result.truncate(self.rank());
        return NumberRingQuotientByIdealEl {
            ring: PhantomData,
            data: result
        };
    }
}

impl<NumberRing, ZnTy, A, C> PartialEq for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn eq(&self, other: &Self) -> bool {
        self.number_ring == other.number_ring && self.base_ring().get_ring() == other.base_ring().get_ring()
    }
}

impl<NumberRing, ZnTy, A, C> RingBase for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type Element = NumberRingQuotientByIdealEl<NumberRing, ZnTy, A, C>;

    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.rank(), self.allocator.clone());
        result.extend(val.data.iter().map(|x| self.base_ring().clone_el(x)));
        return NumberRingQuotientByIdealEl {
            data: result,
            ring: PhantomData
        };
    }

    fn add_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        assert_eq!(lhs.data.len(), self.rank());
        assert_eq!(rhs.data.len(), self.rank());
        for (i, x) in rhs.data.into_iter().enumerate() {
            self.base_ring().add_assign(&mut lhs.data[i], x)
        }
    }

    fn add_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        assert_eq!(lhs.data.len(), self.rank());
        assert_eq!(rhs.data.len(), self.rank());
        for (i, x) in (&rhs.data).into_iter().enumerate() {
            self.base_ring().add_assign_ref(&mut lhs.data[i], x)
        }
    }

    fn sub_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        assert_eq!(lhs.data.len(), self.rank());
        assert_eq!(rhs.data.len(), self.rank());
        for (i, x) in (&rhs.data).into_iter().enumerate() {
            self.base_ring().sub_assign_ref(&mut lhs.data[i], x)
        }
    }

    fn negate_inplace(&self, lhs: &mut Self::Element) {
        assert_eq!(lhs.data.len(), self.rank());
        for i in 0..self.rank() {
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
        assert_eq!(lhs.data.len(), self.rank());
        assert_eq!(rhs.data.len(), self.rank());
        let mut result = Vec::with_capacity_in(2 * self.rank(), self.allocator.clone());
        result.resize_with(2 * self.rank(), || self.base_ring().zero());
        self.convolution().compute_convolution_prepared(&lhs.data, None, &rhs.data, None, &mut result, self.base_ring());
        self.reducer.remainder(&mut result);
        result.truncate(self.rank());
        return NumberRingQuotientByIdealEl {
            ring: PhantomData,
            data: result
        };
    }
    
    fn from_int(&self, value: i32) -> Self::Element {
        self.from(self.base_ring().get_ring().from_int(value))
    }

    fn eq_el(&self, lhs: &Self::Element, rhs: &Self::Element) -> bool {
        assert_eq!(lhs.data.len(), self.rank());
        assert_eq!(rhs.data.len(), self.rank());
        for i in 0..self.rank() {
            if !self.base_ring().eq_el(&lhs.data[i], &rhs.data[i]) {
                return false;
            }
        }
        return true;
    }

    fn zero(&self) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.rank(), self.allocator.clone());
        result.extend((0..self.rank()).map(|_| self.base_ring().zero()));
        return NumberRingQuotientByIdealEl {
            data: result,
            ring: PhantomData
        };
    }

    fn is_zero(&self, value: &Self::Element) -> bool {
        assert_eq!(value.data.len(), self.rank());
        value.data.iter().all(|x| self.base_ring().is_zero(x))
    }

    fn is_one(&self, value: &Self::Element) -> bool {
        assert_eq!(value.data.len(), self.rank());
        self.base_ring().is_one(&value.data[0]) && value.data[1..].iter().all(|x| self.base_ring().is_zero(x))
    }

    fn is_neg_one(&self, value: &Self::Element) -> bool {
        assert_eq!(value.data.len(), self.rank());
        self.base_ring().is_neg_one(&value.data[0]) && value.data[1..].iter().all(|x| self.base_ring().is_zero(x))
    }
    
    fn is_commutative(&self) -> bool { true }
    fn is_noetherian(&self) -> bool { true }
    fn is_approximate(&self) -> bool { false }

    fn dbg<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>) -> std::fmt::Result {
        self.dbg_within(value, out, EnvBindingStrength::Weakest)
    }

    fn dbg_within<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>, _env: EnvBindingStrength) -> std::fmt::Result {
        let poly_ring = DensePolyRing::new(self.base_ring(), "X");
        poly_ring.get_ring().dbg(&RingRef::new(self).poly_repr(&poly_ring, value, self.base_ring().identity()), out)
    }

    fn characteristic<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        self.base_ring().characteristic(ZZ)
    }
}

impl<NumberRing, ZnTy, A, C> RingExtension for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type BaseRing = ZnTy;

    fn base_ring<'a>(&'a self) -> &'a Self::BaseRing {
        self.reducer.base_ring()
    }

    fn from(&self, x: El<Self::BaseRing>) -> Self::Element {
        let mut result = self.zero();
        result.data[0] = x;
        return result;
    }

    fn fma_base(&self, lhs: &Self::Element, rhs: &El<Self::BaseRing>, summand: Self::Element) -> Self::Element {
        assert_eq!(self.rank(), lhs.data.len());
        assert_eq!(self.rank(), summand.data.len());
        
        let mut result = Vec::with_capacity_in(self.rank(), self.allocator.clone());
        result.extend(summand.data.into_iter().enumerate().map(|(i, x)| self.base_ring().fma(&lhs.data[i], rhs, x)));
        return NumberRingQuotientByIdealEl {
            data: result,
            ring: PhantomData
        };
    }

    fn mul_assign_base(&self, lhs: &mut Self::Element, rhs: &El<Self::BaseRing>) {
        assert_eq!(self.rank(), lhs.data.len());
        for x in &mut lhs.data {
            self.base_ring().mul_assign_ref(x, rhs);
        }
    }

    fn mul_assign_base_through_hom<S: ?Sized + RingBase, H: Homomorphism<S, <Self::BaseRing as RingStore>::Type>>(&self, lhs: &mut Self::Element, rhs: &S::Element, hom: H) {
        assert_eq!(self.rank(), lhs.data.len());
        for x in &mut lhs.data {
            hom.mul_assign_ref_map(x, rhs);
        }
    }
}

impl<NumberRing, ZnTy, A, C> FreeAlgebra for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type VectorRepresentation<'a> = CloneElFn<&'a [El<ZnTy>], El<ZnTy>, CloneRingEl<&'a ZnTy>>
        where Self: 'a;

    fn from_canonical_basis<V>(&self, vec: V) -> Self::Element
        where V: IntoIterator<Item = El<Self::BaseRing>>
    {
        let mut result = Vec::with_capacity_in(self.rank(), self.allocator.clone());
        result.extend(vec);
        assert_eq!(result.len(), self.rank());
        return NumberRingQuotientByIdealEl {
            data: result,
            ring: PhantomData
        };
    }

    fn from_canonical_basis_extended<V>(&self, vec: V) -> Self::Element
        where V: IntoIterator<Item = El<Self::BaseRing>>
    {
        let m = self.acting_galois_group().m() as usize;
        let mut result = self.zero();
        for (i, c) in vec.into_iter().enumerate() {
            result = RingRef::new(self).inclusion().fma_map(&self.generator_powers[i % m], &c, result);
        }
        return result;
    }

    fn wrt_canonical_basis<'a>(&'a self, el: &'a Self::Element) -> Self::VectorRepresentation<'a> {
        (&el.data[..]).clone_ring_els(self.base_ring())
    }

    fn canonical_gen(&self) -> Self::Element {
        let mut result = self.zero();
        if result.data.len() > 1 {
            result.data[1] = self.base_ring().one();
        } else {
            result.data[0] = self.base_ring().negate(self.base_ring().clone_el(&self.reducer.modulus_coefficients()[0]));
        }
        return result;
    }

    fn rank(&self) -> usize {
        self.reducer.modulus_deg()
    }
}

pub struct WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    ring: &'a NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>,
}

impl<'a, NumberRing, ZnTy, A, C> Copy for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{}

impl<'a, NumberRing, ZnTy, A, C> Clone for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, 'b, NumberRing, ZnTy, A, C> FnOnce<(&'b [El<ZnTy>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type Output = El<NumberRingQuotientByIdeal<NumberRing, ZnTy, A, C>>;

    extern "rust-call" fn call_once(self, args: (&'b [El<ZnTy>],)) -> Self::Output {
        self.call(args)
    }
}

impl<'a, 'b, NumberRing, ZnTy, A, C> FnMut<(&'b [El<ZnTy>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    extern "rust-call" fn call_mut(&mut self, args: (&'b [El<ZnTy>],)) -> Self::Output {
        self.call(args)
    }
}

impl<'a, 'b, NumberRing, ZnTy, A, C> Fn<(&'b [El<ZnTy>],)> for WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    extern "rust-call" fn call(&self, args: (&'b [El<ZnTy>],)) -> Self::Output {
        self.ring.from_canonical_basis(args.0.iter().map(|x| self.ring.base_ring().clone_el(x)))
    }
}

impl<NumberRing, ZnTy, A, C> FiniteRingSpecializable for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn specialize<O: FiniteRingOperation<Self>>(op: O) -> O::Output {
        op.execute()
    }
}

impl<NumberRing, ZnTy, A, C> FiniteRing for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type ElementsIter<'a> = MultiProduct<<ZnTy::Type as FiniteRing>::ElementsIter<'a>, WRTCanonicalBasisElementCreator<'a, NumberRing, ZnTy, A, C>, CloneRingEl<&'a ZnTy>, Self::Element>
        where Self: 'a;

    fn elements<'a>(&'a self) -> Self::ElementsIter<'a> {
        multi_cartesian_product((0..self.rank()).map(|_| self.base_ring().elements()), WRTCanonicalBasisElementCreator { ring: self }, CloneRingEl(self.base_ring()))
    }

    fn random_element<G: FnMut() -> u64>(&self, mut rng: G) -> Self::Element {
        let mut result = Vec::with_capacity_in(self.rank(), self.allocator.clone());
        result.extend((0..self.rank()).map(|_| self.base_ring().random_element(&mut rng)));
        return NumberRingQuotientByIdealEl {
            data: result,
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

impl<NumberRing, ZnTy, A, C> DivisibilityRing for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
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

impl<NumberRing, ZnTy, A, C> SerializableElementRing for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn serialize<S>(&self, el: &Self::Element, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        SerializableNewtypeStruct::new("RingEl", SerializableSeq::new_with_len(el.data.iter().map(|x| SerializeWithRing::new(x, self.base_ring())), el.data.len())).serialize(serializer)
    }

    fn deserialize<'de, D>(&self, deserializer: D) -> Result<Self::Element, D::Error>
        where D: Deserializer<'de> 
    {
        let result = DeserializeSeedNewtypeStruct::new("RingEl", DeserializeSeedSeq::new(
            (0..(self.rank() + 1)).map(|_| DeserializeWithRing::new(self.base_ring())),
            Vec::with_capacity_in(self.rank(), self.allocator.clone()),
            |mut current, next| { current.push(next); current }
        )).deserialize(deserializer)?;
        if result.len() != self.rank() {
            return Err(serde::de::Error::invalid_length(result.len(), &format!("expected {} elements", self.rank()).as_str()));
        }
        return Ok(NumberRingQuotientByIdealEl {
            data: result,
            ring: PhantomData
        });
    }
}

impl<NumberRing, ZnTy, A, C> CanHomFrom<BigIntRingBase> for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
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

impl<NumberRing, ZnTy1, ZnTy2, A1, A2, C1, C2> CanHomFrom<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>> for NumberRingQuotientByIdealBase<NumberRing, ZnTy1, A1, C1>
    where NumberRing: AbstractNumberRing,
        ZnTy1: RingStore,
        ZnTy1::Type: NiceZn,
        A1: Allocator + Clone,
        C1: ConvolutionAlgorithm<ZnTy1::Type>,
        ZnTy2: RingStore,
        ZnTy2::Type: NiceZn,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnTy2::Type>,
        ZnTy1::Type: CanHomFrom<ZnTy2::Type>
{
    type Homomorphism = <ZnTy1::Type as CanHomFrom<ZnTy2::Type>>::Homomorphism;

    fn has_canonical_hom(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>) -> Option<Self::Homomorphism> {
        if self.number_ring == from.number_ring {
            self.base_ring().get_ring().has_canonical_hom(from.base_ring().get_ring())
        } else {
            None
        }
    }

    fn map_in(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>, el: <NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        assert_eq!(el.data.len(), self.rank());
        let mut result = Vec::with_capacity_in(self.rank(), self.allocator.clone());
        result.extend((0..self.rank()).map(|i| self.base_ring().get_ring().map_in(from.base_ring().get_ring(), from.base_ring().clone_el(&el.data[i]), hom)));
        return NumberRingQuotientByIdealEl {
            data: result,
            ring: PhantomData
        };
    }
}

impl<NumberRing, ZnTy1, ZnTy2, A1, A2, C1, C2> CanIsoFromTo<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>> for NumberRingQuotientByIdealBase<NumberRing, ZnTy1, A1, C1>
    where NumberRing: AbstractNumberRing,
        ZnTy1: RingStore,
        ZnTy1::Type: NiceZn,
        A1: Allocator + Clone,
        C1: ConvolutionAlgorithm<ZnTy1::Type>,
        ZnTy2: RingStore,
        ZnTy2::Type: NiceZn,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnTy2::Type>,
        ZnTy1::Type: CanIsoFromTo<ZnTy2::Type>
{
    type Isomorphism = <ZnTy1::Type as CanIsoFromTo<ZnTy2::Type>>::Isomorphism;

    fn has_canonical_iso(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>) -> Option<Self::Isomorphism> {
        if self.number_ring == from.number_ring {
            self.base_ring().get_ring().has_canonical_iso(from.base_ring().get_ring())
        } else {
            None
        }
    }

    fn map_out(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>, el: Self::Element, iso: &Self::Isomorphism) -> <NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element {
        assert_eq!(el.data.len(), self.rank());
        let mut result = Vec::with_capacity_in(self.rank(), from.allocator.clone());
        result.extend((0..self.rank()).map(|i| self.base_ring().get_ring().map_out(from.base_ring().get_ring(), self.base_ring().clone_el(&el.data[i]), iso)));
        return NumberRingQuotientByIdealEl {
            data: result,
            ring: PhantomData
        };
    }
}

#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::group::*;

#[test]
fn test_quotient_by_ideal() {
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(8);
    let base_ring = zn_big::Zn::new(ZZbig, int_cast(17, ZZbig, ZZi64)).as_field().ok().unwrap();
    let poly_ring = DensePolyRing::new(base_ring.as_field().ok().unwrap(), "X");
    let [t] = poly_ring.with_wrapped_indeterminate(|X| [X - 2]);
    let acting_galois_group = number_ring.galois_group().clone().into().subgroup([]);
    let ring = NumberRingQuotientByIdealBase::new::<true>(number_ring, poly_ring, t, acting_galois_group,);
    assert_eq!(1, ring.rank());
    let galois_group = ring.get_ring().acting_galois_group().parent();
    assert_eq!(17, ring.elements().count());
    feanor_math::ring::generic_tests::test_ring_axioms(&ring, ring.elements());
    assert_el_eq!(&ring, ring.one(), ring.get_ring().apply_galois_action(&ring.one(), &galois_group.identity()));

    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(8);
    let galois_group = number_ring.galois_group();
    let base_ring = zn_big::Zn::new(ZZbig, int_cast(17, ZZbig, ZZi64)).as_field().ok().unwrap();
    let poly_ring = DensePolyRing::new(base_ring.as_field().ok().unwrap(), "X");
    let [t] = poly_ring.with_wrapped_indeterminate(|X| [X.pow_ref(2) + 4]);
    let acting_galois_group = galois_group.get_group().clone().subgroup([galois_group.from_representative(5)]);
    let ring = NumberRingQuotientByIdealBase::new::<true>(number_ring, poly_ring, t, acting_galois_group);
    assert_eq!(2, ring.rank());
    let galois_group = ring.get_ring().acting_galois_group();
    assert_el_eq!(ZZbig, int_cast(2, ZZbig, ZZi64), ring.get_ring().acting_galois_group().subgroup_order());
    assert_el_eq!(&ring, ring.negate(ring.canonical_gen()), ring.get_ring().apply_galois_action(&ring.canonical_gen(), &galois_group.from_representative(5)));
}