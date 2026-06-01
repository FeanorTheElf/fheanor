use std::alloc::Allocator;
use std::alloc::Global;

use feanor_math::algorithms::convolution::ConvolutionAlgorithm;
use feanor_math::algorithms::convolution::KaratsubaAlgorithm;
use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::algorithms::eea::*;
use feanor_math::algorithms::resultant::ComputeResultantRing;
use feanor_math::delegate::DelegateRing;
use feanor_math::delegate::DelegateRingImplFiniteRing;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::field::FieldStore;
use feanor_math::homomorphism::CanHomFrom;
use feanor_math::homomorphism::CanIsoFromTo;
use feanor_math::rings::extension::*;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::rings::zn::*;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::pid::PrincipalIdealRingStore;
use feanor_math::ring::*;
use feanor_math::rings::poly::*;
use feanor_math::rings::poly::dense_poly::*;
use feanor_math::seq::VectorFn;
use feanor_math::rings::rational::RationalField;
use feanor_math::integer::*;
use tracing::instrument;

use crate::number_ring::galois::*;
use crate::number_ring::quotient_by_ideal::*;
use crate::number_ring::*;
use crate::NiceZn;
use crate::{log_time, ZZbig, ZZi64};

pub struct CLPXPlaintextRingBase<NumberRing, ZnTy, A, C>
    where NumberRing: NumberRingDescriptor,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    ZZX: DensePolyRing<BigIntRing>,
    base: NumberRingQuotientByIdeal<NumberRing, ZnTy, A, C>,
    t: El<DensePolyRing<BigIntRing>>,
    /// The (algebraic) norm `N(t)` of `t`, which is equivalent to `Res(t(X), Phi_m(X))`
    normt: El<BigIntRing>,
    /// the value `N(t) t^-1`, which is an element of `Z[𝝵]`
    normt_t_inv: El<DensePolyRing<BigIntRing>>,
    gen_poly: El<DensePolyRing<BigIntRing>>
}

pub type CLPXPlaintextRing<NumberRing, ZnTy, A = Global, C = KaratsubaAlgorithm> = RingValue<CLPXPlaintextRingBase<NumberRing, ZnTy, A, C>>;

impl<NumberRing, ZnTy, A, C> CLPXPlaintextRingBase<NumberRing, ZnTy, A, C>
    where NumberRing: NumberRingDescriptor,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    #[instrument(skip_all)]
    pub fn create<const LOG: bool>(
        number_ring: NumberRing, 
        base_ring: ZnTy, 
        poly_ring: DensePolyRing<BigIntRing>, 
        t: El<DensePolyRing<BigIntRing>>, 
        acting_galois_group: Subgroup<CyclotomicGaloisGroup>, 
        allocator: A, 
        convolution: C
    ) -> RingValue<Self> {
        assert!(
            poly_ring.base_ring().is_one(poly_ring.lc(&t).unwrap()),
            "currently only the case that t(X) is monic is supported"
        );
        let QQX = DensePolyRing::new(RationalField::new(ZZbig), "X");
        let QQ = QQX.base_ring();

        let gen_poly = number_ring.generating_poly(&poly_ring);

        // we compute `N(t) = Res(t(X), Phi_m(X))`; this is large, so use big integers
        let norm = log_time::<_, _, LOG, _>("Compute Resultant", |[]| 
            ZZbig.abs(<_ as ComputeResultantRing>::resultant(&poly_ring, poly_ring.clone_el(&gen_poly), poly_ring.clone_el(&t)))
        );
        let rest = if let Some(rest) = ZZbig.checked_div(&norm, &ZZbig.pow(base_ring.characteristic(ZZbig).unwrap(), int_cast(acting_galois_group.subgroup_order(), ZZi64, ZZbig) as usize)) {
            rest
        } else {
            panic!("the given ideal has norm {}, which is not divisible by {}^{}", ZZbig.format(&norm), ZZbig.format(&base_ring.characteristic(ZZbig).unwrap()), int_cast(acting_galois_group.subgroup_order(), ZZi64, ZZbig))
        };
        if !ZZbig.is_one(&signed_gcd(rest, base_ring.characteristic(ZZbig).unwrap(), ZZbig)) {
            panic!("the given ideal has norm {}, which is divisible by more than {} (= size of acting Galois group) powers of {}; note that the Galois group must have rank equal to the rank of the quotient ring", 
                ZZbig.format(&norm), 
                int_cast(acting_galois_group.subgroup_order(), ZZi64, ZZbig), 
                ZZbig.format(&base_ring.characteristic(ZZbig).unwrap())
            )
        }

        // compute the inverse of `t(X)` modulo `Phi_m(X)`, which is required for encoding
        let ZZX_to_QQX = QQX.lifted_hom(&poly_ring, QQ.inclusion());
        let (mut s, _, d) = log_time::<_, _, LOG, _>("Compute Inverse", |[]| 
            QQX.extended_ideal_gen(&ZZX_to_QQX.map_ref(&t), &ZZX_to_QQX.map_ref(&gen_poly))
        );
        assert_eq!(0, QQX.degree(&d).unwrap());
        QQX.inclusion().mul_assign_map(&mut s, QQ.div(&QQ.inclusion().map_ref(&norm), QQX.coefficient_at(&d, 0)));
        let normt_t_inv = poly_ring.from_terms(QQX.terms(&s).map(|(c, i)| (
            ZZbig.checked_div(QQ.num(c), QQ.den(c)).unwrap(),
            i
        )));

        let base_ringX = DensePolyRing::new(base_ring, "X");
        let hom = base_ringX.base_ring().can_hom(&ZZbig).unwrap();
        let ideal_generator = base_ringX.lifted_hom(&poly_ring, &hom).map_ref(&t);
        let base = NumberRingQuotientByIdealBase::create::<LOG>(number_ring, base_ringX, ideal_generator, acting_galois_group, allocator, convolution);
        return RingValue::from(Self {
            base: base,
            normt: norm,
            normt_t_inv: normt_t_inv,
            t: t,
            ZZX: poly_ring,
            gen_poly: gen_poly
        });
    }

    pub fn t(&self) -> &El<DensePolyRing<BigIntRing>> {
        &self.t
    }

    pub fn normt_t_inv(&self) -> &El<DensePolyRing<BigIntRing>> {
        &self.normt_t_inv
    }

    pub fn normt(&self) -> &El<BigIntRing> {
        &self.normt
    }

    pub fn ZZX(&self) -> &DensePolyRing<BigIntRing> {
        &self.ZZX
    }

    ///
    /// Reduces the given element modulo `I`.
    /// 
    #[instrument(skip_all)]
    pub fn reduce_mod_t(&self, el: &El<DensePolyRing<BigIntRing>>) -> <Self as RingBase>::Element {
        if self.ZZX.is_zero(&el) {
            return self.zero();
        }
        let hom = self.base_ring().can_hom(&ZZbig).unwrap();
        self.from_canonical_basis_extended((0..=self.ZZX.degree(el).unwrap()).map(|i| hom.map_ref(self.ZZX.coefficient_at(el, i))))
    }

    ///
    /// Finds a small element in the number ring that reduces to the given
    /// element modulo `I`.
    /// 
    #[instrument(skip_all)]
    pub fn small_lift(&self, el: &<Self as RingBase>::Element) -> El<DensePolyRing<BigIntRing>> {
        let el_lift = self.ZZX.from_terms(self.wrt_canonical_basis(el).iter().enumerate().map(|(i, c)| (int_cast(self.base_ring().smallest_lift(c), ZZbig, self.base_ring().integer_ring()), i)));
        let (_, normt_el_over_t) = self.ZZX.div_rem_monic(self.ZZX.mul_ref(&el_lift, &self.normt_t_inv), &self.gen_poly);
        let (_, closest_multiple_of_t) = self.ZZX.div_rem_monic(
            self.ZZX.mul_ref_snd(self.ZZX.from_terms(self.ZZX.terms(&normt_el_over_t).map(|(c, i)| (ZZbig.rounded_div(ZZbig.clone_el(c), &self.normt), i))), &self.t),
            &self.gen_poly
        );
        return self.ZZX.sub(el_lift, closest_multiple_of_t);
    }

    ///
    /// Computes `round(Q lift(x) / t) mod Q`, where `Q` is the characteristic
    /// of the given ring.
    /// 
    #[instrument(skip_all)]
    pub fn encode<S>(&self, target: S, el: &<Self as RingBase>::Element) -> El<S>
        where S: RingStore, 
            S::Type: NumberRingQuotient<NumberRing = NumberRing>,
            <<S::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing + CanHomFrom<BigIntRingBase>
    {
        assert!(target.number_ring() == self.number_ring());
        let el_lift = self.ZZX.from_terms(self.wrt_canonical_basis(el).iter().enumerate().map(|(i, c)| (int_cast(self.base_ring().smallest_lift(c), ZZbig, self.base_ring().integer_ring()), i)));
        let (_, normt_el_over_t) = self.ZZX.div_rem_monic(self.ZZX.mul_ref(&el_lift, &self.normt_t_inv), &self.gen_poly);
        let hom = target.base_ring().can_hom(&ZZbig).unwrap();
        let Q = int_cast(target.base_ring().integer_ring().clone_el(target.base_ring().modulus()), ZZbig, target.base_ring().integer_ring());
        return target.from_canonical_basis((0..target.rank()).map(|i| hom.map(ZZbig.rounded_div(ZZbig.mul_ref(&Q, self.ZZX.coefficient_at(&normt_el_over_t, i)), &self.normt))));
    }

    ///
    /// Computes `round(t lift(x) / Q) mod t`, where `Q` is the characteristic
    /// of the given ring.
    /// 
    #[instrument(skip_all)]
    pub fn decode<S>(&self, from: S, el: &El<S>) -> <Self as RingBase>::Element
        where S: RingStore, 
            S::Type: NumberRingQuotient<NumberRing = NumberRing>,
            <<S::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing
    {
        assert!(from.number_ring() == self.number_ring());
        if from.is_zero(el) {
            return self.zero();
        }
        let el_lift = self.ZZX.from_terms(from.wrt_canonical_basis(el).iter().enumerate().map(|(i, c)| (int_cast(from.base_ring().smallest_lift(c), ZZbig, from.base_ring().integer_ring()), i)));
        let (_, el_t) = self.ZZX.div_rem_monic(self.ZZX.mul_ref(&el_lift, &self.t), &self.gen_poly);
        let hom = self.base_ring().can_hom(&ZZbig).unwrap();
        let Q = int_cast(from.base_ring().integer_ring().clone_el(from.base_ring().modulus()), ZZbig, from.base_ring().integer_ring());
        return self.from_canonical_basis_extended((0..=self.ZZX.degree(&el_t).unwrap()).map(|i| hom.map(ZZbig.rounded_div(ZZbig.clone_el(self.ZZX.coefficient_at(&el_t, i)), &Q))));
    }
}

impl<NumberRing, ZnTy, A, C> PartialEq for CLPXPlaintextRingBase<NumberRing, ZnTy, A, C>
    where NumberRing: NumberRingDescriptor,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn eq(&self, other: &Self) -> bool {
        self.base.get_ring() == other.base.get_ring()
    }
}

impl<NumberRing, ZnTy, A, C> DelegateRing for CLPXPlaintextRingBase<NumberRing, ZnTy, A, C>
    where NumberRing: NumberRingDescriptor,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type Base = NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>;
    type Element = El<NumberRingQuotientByIdeal<NumberRing, ZnTy, A, C>>;

    fn get_delegate(&self) -> &Self::Base {
        self.base.get_ring()
    }

    fn delegate(&self, el: Self::Element) -> <Self::Base as RingBase>::Element { el }
    fn delegate_mut<'a>(&self, el: &'a mut Self::Element) -> &'a mut <Self::Base as RingBase>::Element { el }
    fn delegate_ref<'a>(&self, el: &'a Self::Element) -> &'a <Self::Base as RingBase>::Element { el }
    fn rev_delegate(&self, el: <Self::Base as RingBase>::Element) -> Self::Element { el }
}

impl<NumberRing, ZnTy, A, C> DelegateRingImplFiniteRing for CLPXPlaintextRingBase<NumberRing, ZnTy, A, C>
    where NumberRing: NumberRingDescriptor,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{}

impl<NumberRing, ZnTy, A, C> NumberRingQuotient for CLPXPlaintextRingBase<NumberRing, ZnTy, A, C>
    where NumberRing: NumberRingDescriptor,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type NumberRing = NumberRing;

    fn acting_galois_group(&self) -> &Subgroup<CyclotomicGaloisGroup> {
        self.base.acting_galois_group()
    }

    fn apply_galois_action(&self, x: &Self::Element, g: &GaloisGroupEl) -> Self::Element {
        self.base.apply_galois_action(x, g)
    }

    fn number_ring(&self) -> &Self::NumberRing {
        self.base.number_ring()
    }

    fn apply_galois_action_many(&self, x: &Self::Element, gs: &[GaloisGroupEl]) -> Vec<Self::Element> {
        self.base.apply_galois_action_many(x, gs)
    }
}

impl<NumberRing, ZnTy1, ZnTy2, A1, A2, C1, C2> CanHomFrom<CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>> for CLPXPlaintextRingBase<NumberRing, ZnTy1, A1, C1>
    where NumberRing: NumberRingDescriptor,
        ZnTy1: RingStore,
        ZnTy1::Type: NiceZn + CanHomFrom<ZnTy2::Type>,
        ZnTy2: RingStore,
        ZnTy2::Type: NiceZn,
        A1: Allocator + Clone,
        C1: ConvolutionAlgorithm<ZnTy1::Type>,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnTy2::Type>,
{
    type Homomorphism = <NumberRingQuotientByIdealBase<NumberRing, ZnTy1, A1, C1> as CanHomFrom<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>>>::Homomorphism;

    fn has_canonical_hom(&self, from: &CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>) -> Option<Self::Homomorphism> {
        self.base.get_ring().has_canonical_hom(from.base.get_ring())
    }

    fn map_in(&self, from: &CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>, el: <CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.base.get_ring().map_in(from.base.get_ring(), el, hom)
    }

    fn map_in_ref(&self, from: &CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>, el: &<CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.base.get_ring().map_in_ref(from.base.get_ring(), el, hom)
    }

    fn mul_assign_map_in(&self, from: &CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>, lhs: &mut Self::Element, rhs: <CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) {
        self.base.get_ring().mul_assign_map_in(from.base.get_ring(), lhs, rhs, hom)
    }

    fn mul_assign_map_in_ref(&self, from: &CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>, lhs: &mut Self::Element, rhs: &<CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) {
        self.base.get_ring().mul_assign_map_in_ref(from.base.get_ring(), lhs, rhs, hom)
    }

    fn fma_map_in(&self, from: &CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>, lhs: &Self::Element, rhs: &<CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, summand: Self::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.base.get_ring().fma_map_in(from.base.get_ring(), lhs, rhs, summand, hom)
    }
}


impl<NumberRing, ZnTy1, ZnTy2, A1, A2, C1, C2> CanIsoFromTo<CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>> for CLPXPlaintextRingBase<NumberRing, ZnTy1, A1, C1>
    where NumberRing: NumberRingDescriptor,
        ZnTy1: RingStore,
        ZnTy1::Type: NiceZn + CanIsoFromTo<ZnTy2::Type>,
        ZnTy2: RingStore,
        ZnTy2::Type: NiceZn,
        A1: Allocator + Clone,
        C1: ConvolutionAlgorithm<ZnTy1::Type>,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnTy2::Type>,
{
    type Isomorphism = <NumberRingQuotientByIdealBase<NumberRing, ZnTy1, A1, C1> as CanIsoFromTo<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>>>::Isomorphism;

    fn has_canonical_iso(&self, from: &CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>) -> Option<Self::Isomorphism> {
        self.base.get_ring().has_canonical_iso(from.base.get_ring())
    }

    fn map_out(&self, from: &CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2>, el: Self::Element, iso: &Self::Isomorphism) -> <CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element {
        self.base.get_ring().map_out(from.base.get_ring(), el, iso)
    }
}

impl<NumberRing, ZnTy1, ZnTy2, A1, A2, C1, C2> CanHomFrom<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>> for CLPXPlaintextRingBase<NumberRing, ZnTy1, A1, C1>
    where NumberRing: NumberRingDescriptor,
        ZnTy1: RingStore,
        ZnTy1::Type: NiceZn + CanHomFrom<ZnTy2::Type>,
        ZnTy2: RingStore,
        ZnTy2::Type: NiceZn,
        A1: Allocator + Clone,
        C1: ConvolutionAlgorithm<ZnTy1::Type>,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnTy2::Type>,
{
    type Homomorphism = <NumberRingQuotientByIdealBase<NumberRing, ZnTy1, A1, C1> as CanHomFrom<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>>>::Homomorphism;

    fn has_canonical_hom(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>) -> Option<Self::Homomorphism> {
        self.base.get_ring().has_canonical_hom(from)
    }

    fn map_in(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>, el: <NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.base.get_ring().map_in(from, el, hom)
    }

    fn map_in_ref(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>, el: &<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.base.get_ring().map_in_ref(from, el, hom)
    }

    fn mul_assign_map_in(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>, lhs: &mut Self::Element, rhs: <NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) {
        self.base.get_ring().mul_assign_map_in(from, lhs, rhs, hom)
    }

    fn mul_assign_map_in_ref(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>, lhs: &mut Self::Element, rhs: &<CLPXPlaintextRingBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, hom: &Self::Homomorphism) {
        self.base.get_ring().mul_assign_map_in_ref(from, lhs, rhs, hom)
    }

    fn fma_map_in(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>, lhs: &Self::Element, rhs: &<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element, summand: Self::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.base.get_ring().fma_map_in(from, lhs, rhs, summand, hom)
    }
}

impl<NumberRing, ZnTy1, ZnTy2, A1, A2, C1, C2> CanIsoFromTo<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>> for CLPXPlaintextRingBase<NumberRing, ZnTy1, A1, C1>
    where NumberRing: NumberRingDescriptor,
        ZnTy1: RingStore,
        ZnTy1::Type: NiceZn + CanIsoFromTo<ZnTy2::Type>,
        ZnTy2: RingStore,
        ZnTy2::Type: NiceZn,
        A1: Allocator + Clone,
        C1: ConvolutionAlgorithm<ZnTy1::Type>,
        A2: Allocator + Clone,
        C2: ConvolutionAlgorithm<ZnTy2::Type>,
{
    type Isomorphism = <NumberRingQuotientByIdealBase<NumberRing, ZnTy1, A1, C1> as CanIsoFromTo<NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>>>::Isomorphism;

    fn has_canonical_iso(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>) -> Option<Self::Isomorphism> {
        self.base.get_ring().has_canonical_iso(from)
    }

    fn map_out(&self, from: &NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2>, el: Self::Element, iso: &Self::Isomorphism) -> <NumberRingQuotientByIdealBase<NumberRing, ZnTy2, A2, C2> as RingBase>::Element {
        self.base.get_ring().map_out(from, el, iso)
    }
}

#[cfg(test)]
use feanor_math::algorithms::convolution::STANDARD_CONVOLUTION;
#[cfg(test)]
use feanor_math::group::AbelianGroupStore;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::number_ring::general_cyclotomic::OddSquarefreeCyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::galois::CyclotomicGaloisGroupOps;
#[cfg(test)]
use std::array::from_fn;
#[cfg(test)]
use crate::ciphertext_ring::double_rns_ring::DoubleRNSRingBase;

#[cfg(test)]
fn test_rns_base() -> zn_rns::Zn<zn_64::Zn, BigIntRing> {
    zn_rns::Zn::create_from_primes(vec![5598412801, 5665259521, 5698682881, 5715394561, 5732106241, 5771100161, 5821235201, 5899223041, 5921505281, 5966069761, 6032916481, 6155468801], ZZbig)
}

#[cfg(test)]
fn test_ring1() -> (CLPXPlaintextRing<Pow2CyclotomicNumberRing, zn_64::Zn>, Vec<El<CLPXPlaintextRing<Pow2CyclotomicNumberRing, zn_64::Zn>>>) {
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X - 2]);
    let number_ring = Pow2CyclotomicNumberRing::new(32);
    let acting_galois_group = number_ring.galois_group().get_group().clone().subgroup([]);
    let result = CLPXPlaintextRingBase::create::<true>(number_ring, zn_64::Zn::new(65537), ZZX, t, acting_galois_group, Global, STANDARD_CONVOLUTION);
    let elements = (0..31).map(|i| result.int_hom().map(1 << i)).collect();
    return (result, elements);
}

#[cfg(test)]
fn test_ring2() -> (CLPXPlaintextRing<Pow2CyclotomicNumberRing, zn_64::Zn>, Vec<El<CLPXPlaintextRing<Pow2CyclotomicNumberRing, zn_64::Zn>>>) {
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    let number_ring = Pow2CyclotomicNumberRing::new(64);
    let acting_galois_group = number_ring.galois_group().get_group().clone().subgroup([]);
    let result = CLPXPlaintextRingBase::create::<true>(number_ring, zn_64::Zn::new(6700417), ZZX, t, acting_galois_group, Global, STANDARD_CONVOLUTION);
    let elements = (0..31).map(|i| result.int_hom().map(1 << i)).collect();
    return (result, elements);
}

#[cfg(test)]
fn test_ring3() -> (CLPXPlaintextRing<Pow2CyclotomicNumberRing, zn_64::Zn>, Vec<El<CLPXPlaintextRing<Pow2CyclotomicNumberRing, zn_64::Zn>>>) {
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(4) - 2]);
    let number_ring = Pow2CyclotomicNumberRing::new(64);
    let acting_galois_group = number_ring.galois_group().get_group().clone().subgroup([number_ring.galois_group().from_representative(17)]);
    let result = CLPXPlaintextRingBase::create::<true>(number_ring, zn_64::Zn::new(257), ZZX, t, acting_galois_group, Global, STANDARD_CONVOLUTION);
    let elements = (0..31).map(|i| result.int_hom().map(1 << i))
        .chain((0..31).map(|i| result.mul(result.canonical_gen(), result.int_hom().map(1 << i)))).collect();
    return (result, elements);
}

#[cfg(test)]
fn test_ring4() -> (CLPXPlaintextRing<OddSquarefreeCyclotomicNumberRing, zn_64::Zn>, Vec<El<CLPXPlaintextRing<OddSquarefreeCyclotomicNumberRing, zn_64::Zn>>>) {
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(5) - 2]);
    let number_ring = OddSquarefreeCyclotomicNumberRing::new(85);
    let acting_galois_group = number_ring.galois_group().get_group().clone().subgroup([number_ring.galois_group().from_representative(18)]);
    let result = CLPXPlaintextRingBase::create::<true>(number_ring, zn_64::Zn::new(131071), ZZX, t, acting_galois_group, Global, STANDARD_CONVOLUTION);
    let elements = (0..15).flat_map(|i| from_fn::<_, 4, _>(|j| result.mul(result.pow(result.canonical_gen(), j), result.int_hom().map(1 << i))).into_iter()).collect();
    return (result, elements);
}

#[test]
fn test_clpx_plaintext_ring_create() {
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let (ring, _) = test_ring1();
    assert_eq!(1, ring.rank());
    assert_el_eq!(&ring, ring.int_hom().map(2), ring.canonical_gen());

    let (ring, _) = test_ring2();
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    assert_eq!(1, ring.rank());
    assert_el_eq!(&ring, ring.zero(), ZZX.evaluate(&t, &ring.canonical_gen(), ring.inclusion().compose(ring.base_ring().can_hom(&ZZbig).unwrap())));

    let (ring, _) = test_ring3();
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(4) - 2]);
    assert_eq!(4, ring.rank());
    assert_el_eq!(&ring, ring.zero(), ZZX.evaluate(&t, &ring.canonical_gen(), ring.inclusion().compose(ring.base_ring().can_hom(&ZZbig).unwrap())));

    let (ring, _) = test_ring4();
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(5) - 2]);
    assert_eq!(4, ring.rank());
    assert_el_eq!(&ring, ring.zero(), ZZX.evaluate(&t, &ring.canonical_gen(), ring.inclusion().compose(ring.base_ring().can_hom(&ZZbig).unwrap())));
}

#[test]
fn test_clpx_plaintext_ring_small_lift() {
    let ZZX = DensePolyRing::new(ZZbig, "X");

    let (ring, elements) = test_ring1();
    for a in &elements {
        let a_lift = ring.get_ring().small_lift(a);
        assert!(ring.get_ring().ZZX().degree(&a_lift).unwrap_or(0) < ring.number_ring().rank());
        assert_el_eq!(&ring, a, ring.get_ring().reduce_mod_t(&a_lift));
        assert!(ZZX.terms(&ring.get_ring().small_lift(a)).all(|(c, _)| int_cast(ZZbig.clone_el(c), ZZi64, ZZbig).abs() <= 1));
    }

    let (ring, elements) = test_ring2();
    for a in &elements {
        let a_lift = ring.get_ring().small_lift(a);
        assert!(ring.get_ring().ZZX().degree(&a_lift).unwrap_or(0) < ring.number_ring().rank());
        assert_el_eq!(&ring, a, ring.get_ring().reduce_mod_t(&a_lift));
        assert!(ZZX.terms(&ring.get_ring().small_lift(a)).all(|(c, _)| int_cast(ZZbig.clone_el(c), ZZi64, ZZbig).abs() <= 1));
    }

    let (ring, elements) = test_ring3();
    for a in &elements {
        let a_lift = ring.get_ring().small_lift(a);
        assert!(ring.get_ring().ZZX().degree(&a_lift).unwrap_or(0) < ring.number_ring().rank());
        assert_el_eq!(&ring, a, ring.get_ring().reduce_mod_t(&a_lift));
        assert!(ZZX.terms(&ring.get_ring().small_lift(a)).all(|(c, _)| int_cast(ZZbig.clone_el(c), ZZi64, ZZbig).abs() <= 1));
    }

    let (ring, elements) = test_ring4();
    for a in &elements {
        let a_lift = ring.get_ring().small_lift(a);
        assert!(ring.get_ring().ZZX().degree(&a_lift).unwrap_or(0) < ring.number_ring().rank());
        assert_el_eq!(&ring, a, ring.get_ring().reduce_mod_t(&a_lift));
        assert!(ZZX.terms(&ring.get_ring().small_lift(a)).all(|(c, _)| int_cast(ZZbig.clone_el(c), ZZi64, ZZbig).abs() <= 1));
    }
}

#[test]
fn test_clpx_plaintext_ring_encode_decode() {
    let ZQ = test_rns_base();

    let (ring, elements) = test_ring1();
    let RQ = DoubleRNSRingBase::new(ring.number_ring().clone(), ZQ.clone());
    for a in &elements {
        assert_el_eq!(&ring, a, ring.get_ring().decode(&RQ, &ring.get_ring().encode(&RQ, a)));
    }

    let (ring, elements) = test_ring2();
    let RQ = DoubleRNSRingBase::new(ring.number_ring().clone(), ZQ.clone());
    for a in &elements {
        assert_el_eq!(&ring, a, ring.get_ring().decode(&RQ, &ring.get_ring().encode(&RQ, a)));
    }

    let (ring, elements) = test_ring3();
    let RQ = DoubleRNSRingBase::new(ring.number_ring().clone(), ZQ.clone());
    for a in &elements {
        assert_el_eq!(&ring, a, ring.get_ring().decode(&RQ, &ring.get_ring().encode(&RQ, a)));
    }

    let (ring, elements) = test_ring4();
    let RQ = DoubleRNSRingBase::new(ring.number_ring().clone(), ZQ.clone());
    for a in &elements {
        assert_el_eq!(&ring, a, ring.get_ring().decode(&RQ, &ring.get_ring().encode(&RQ, a)));
    }
}
