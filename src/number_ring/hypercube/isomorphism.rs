use std::alloc::*;
use std::sync::Arc;

use feanor_math::algorithms::convolution::fft::{FFTConvolution, FFTConvolutionZn};
use feanor_math::algorithms::convolution::rns::{RNSConvolution, RNSConvolutionZn};
use feanor_math::algorithms::convolution::STANDARD_CONVOLUTION;
use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::algorithms::poly_gcd::hensel::hensel_lift_factorization;
use feanor_math::algorithms::unity_root::get_prim_root_of_unity;
use feanor_math::computation::*;
use feanor_math::reduce_lift::poly_factor_gcd::IntegersWithLocalZnQuotient;
use feanor_math::rings::field::{AsField, AsFieldBase};
use feanor_math::pid::PrincipalIdealRingStore;
use feanor_math::divisibility::*;
use feanor_math::homomorphism::*;
use feanor_math::integer::*;
use feanor_math::primitive_int::*;
use feanor_math::rings::extension::extension_impl::*;
use feanor_math::rings::extension::galois_field::GaloisField;
use feanor_math::rings::extension::*;
use feanor_math::rings::local::{AsLocalPIR, AsLocalPIRBase};
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::poly::PolyRingStore;
use feanor_math::group::*;
use feanor_math::delegate::{WrapHom, UnwrapHom};
use feanor_math::ring::*;
use feanor_math::rings::zn::*;
use feanor_math::seq::sparse::SparseMapVector;
use feanor_math::seq::*;
use feanor_math::assert_el_eq;
use feanor_math::serialization::SerializableElementRing;
use tracing::instrument;

use crate::cache::{create_cached, SerializeDeserializeWith, StoreAs};
use crate::number_ring::galois::*;
#[cfg(test)]
use crate::number_ring::quotient_by_ideal::NumberRingQuotientByIdeal;
use crate::number_ring::*;
use crate::*;
use crate::ntt::dyn_convolution::*;
use crate::number_ring::hypercube::interpolate::FastPolyInterpolation;
use crate::number_ring::hypercube::structure::*;

pub use crate::number_ring::hypercube::serialization::{DeserializeSeedHypercubeIsomorphismWithoutRing, SerializableHypercubeIsomorphismWithoutRing};

#[instrument(skip_all)]
pub(super) fn create_convolution<R>(d: usize, log2_input_size: usize) -> DynConvolutionAlgorithmConvolution<R, Arc<dyn DynConvolutionAlgorithm<R>>>
    where R: ?Sized + ZnRing + CanHomFrom<BigIntRingBase> + CanHomFrom<StaticRingBase<i64>>
{
    let fft_convolution = FFTConvolution::new();
    let max_log2_len = ZZi64.abs_log2_ceil(&(d as i64)).unwrap() + 1;
    if d <= 30 {
        DynConvolutionAlgorithmConvolution::new(Arc::new(STANDARD_CONVOLUTION))
    } else if fft_convolution.has_sufficient_precision(max_log2_len, log2_input_size) {
        DynConvolutionAlgorithmConvolution::new(Arc::new(FFTConvolutionZn::from(fft_convolution)))
    } else {
        DynConvolutionAlgorithmConvolution::new(Arc::new(RNSConvolutionZn::from(RNSConvolution::new(max_log2_len))))
    }
}

#[instrument(skip_all)]
fn hensel_lift_root_of_unity<R1, R2>(S: R1, Fp: R2, root_of_unity: El<R2>, m: usize) -> El<R1>
    where R1: RingStore,
        R2: RingStore,
        R1::Type: FreeAlgebra + DivisibilityRing,
        R2::Type: FreeAlgebra,
        <<R1::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing + CanHomFrom<StaticRingBase<i64>>,
        <<R2::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing
{
    let (p, e) = is_prime_power(S.base_ring().integer_ring(), S.base_ring().modulus()).unwrap();
    assert_el_eq!(Fp.base_ring().integer_ring(), Fp.base_ring().modulus(), int_cast(p, Fp.base_ring().integer_ring(), S.base_ring().integer_ring()));

    let red_map = ZnReductionMap::new(S.base_ring(), Fp.base_ring()).unwrap();
    let mut result = S.from_canonical_basis(Fp.wrt_canonical_basis(&root_of_unity).into_iter().map(|x| red_map.smallest_lift(x)));

    // perform hensel lifting
    for _ in 0..e {
        let delta = S.checked_div(
            &S.sub(S.pow(S.clone_el(&result), m), S.one()),
            &S.inclusion().mul_map(S.pow(S.clone_el(&result), m - 1), S.base_ring().coerce(&ZZi64, m as i64)) 
        ).unwrap();
        S.sub_assign(&mut result, delta);
    }
    assert!(S.is_one(&S.pow(S.clone_el(&result), m)));
    return result;
}


type FpPolyRing<R> = DensePolyRing<
    AsField<RingValue<BaseRing<R>>>, 
    Global, 
    DynConvolutionAlgorithmConvolution<AsFieldBase<RingValue<BaseRing<R>>>, Arc<dyn DynConvolutionAlgorithm<AsFieldBase<RingValue<BaseRing<R>>>>>>
>;
type ZpePolyRing<R> = DensePolyRing<
    AsLocalPIR<RingValue<BaseRing<R>>>, 
    Global, 
    DynConvolutionAlgorithmConvolution<AsLocalPIRBase<RingValue<BaseRing<R>>>, Arc<dyn DynConvolutionAlgorithm<AsLocalPIRBase<RingValue<BaseRing<R>>>>>>
>;
type TmpSlotRingOf<'a, R> = AsLocalPIR<FreeAlgebraImpl<
    AsLocalPIR<RingRef<'a, BaseRing<R>>>,
    SparseMapVector<AsLocalPIR<RingRef<'a, BaseRing<R>>>>, 
    Global, 
    DynConvolutionAlgorithmConvolution<AsLocalPIRBase<RingRef<'a, BaseRing<R>>>, Arc<dyn DynConvolutionAlgorithm<AsLocalPIRBase<RingRef<'a, BaseRing<R>>>>>>
>>;

pub type SlotRingOver<R> = AsLocalPIR<FreeAlgebraImpl<R, Vec<El<R>>, Global, DynConvolutionAlgorithmConvolution<<R as RingStore>::Type, Arc<dyn DynConvolutionAlgorithm<<R as RingStore>::Type>>>>>;

///
/// Type of the slot ring used to represent the decomposition into
/// slots of the given ring `R`.
/// 
pub type SlotRingOf<R> = SlotRingOver<RingValue<BaseRing<R>>>;

///
/// Shortcut to access the base ring of a ring extension `R`.
/// 
pub type BaseRing<R> = <<<R as RingStore>::Type as RingExtension>::BaseRing as RingStore>::Type;

///
/// Shortcut to access the base ring of a ring extension `R` and
/// wrap it in a [`AsLocalPIRBase`].
/// 
pub type DecoratedBaseRingBase<R> = AsLocalPIRBase<RingValue<BaseRing<R>>>;

///
/// Represents the isomorphism `Fp[X]/(Phi_m(X)) -> F_(p^d)^domain(h)` for a
/// [`HypercubeStructure`] `h`, defined by
/// ```text
///   Fp[X]/(Phi_m(X))  ->  F_(p^d)^domain(h)
///          a(X)       ->  ( a(𝝵^(h(i)^-1)) )_(i in domain(h))
/// ```
/// where `𝝵` is an `m`-th primitive root of unity in `F_(p^d)`.
/// 
/// In fact, the more general case of `(Z/p^eZ)[X]/(Phi_m(X))` is supported.
///  
/// # Serialization
/// 
/// There are two ways of serializing/deserializing a [`HypercubeIsomorphism`]
///  - you can serialize the isomorphism including the implementation of `Fp[X]/(Phi_m(X))`
///    (if the latter is serializable) using the implementation of [`serde::Serialize`] and
///    [`serde::Deserialize`]
///  - alternatively, you can serialize the isomorphism without the ring implementation
///    using [`SerializableHypercubeIsomorphismWithoutRing`] and 
///    [`DeserializeSeedHypercubeIsomorphismWithoutRing`]; 
///    this of course requires that the ring is provided at deserialization time
/// 
pub struct HypercubeIsomorphism<R>
    where R: RingStore,
        R::Type: NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    ring: R,
    e: usize,
    slot_rings: Vec<SlotRingOf<R>>,
    slot_to_ring_interpolation: FastPolyInterpolation<ZpePolyRing<R>>,
    hypercube_structure: HypercubeStructure,
    /// the `(i, j)`-th entry stores the image of `𝝵^j` under the isomorphism
    /// from `F_(p^d)` to the `i`-th local slot ring (which is of course isomorphic
    /// to `F_(p^d)`, but represented as quotient by `slot_ring_moduli[i]`).
    slot_generator_powers: Vec<Vec<El<ZpePolyRing<R>>>>,
}

impl<R> HypercubeIsomorphism<R>
    where R: RingStore,
        R::Type: NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    ///
    /// Most general way to create a new [`HypercubeIsomorphism`].
    /// 
    /// The parameters are as follows:
    ///  - `ring` is the ring `Fp[X]/(Phi_m(X))` that is the domain of the isomorphism
    ///  - `hypercube_structure` is the [`HypercubeStructure`] that induces the isomorphism
    ///  - `slot_ring_moduli` is a list of all factors of `Phi_m(X) mod p`, ordered such
    ///    as to be compatible with the ordering of the slots, as given by [`HypercubeStructure`].
    /// 
    #[instrument(skip_all)]
    pub fn create<const LOG: bool>(ring: R, hypercube_structure: HypercubeStructure, ZpeX: ZpePolyRing<R>, slot_ring_moduli: Vec<El<ZpePolyRing<R>>>) -> Self {
        assert!(ring.acting_galois_group().get_group() == hypercube_structure.galois_group().get_group());
        let frobenius = hypercube_structure.frobenius(1);
        let d = hypercube_structure.d();
       
        // for quotients of cyclotomic number rings, the frobenius associated to a prime ideal
        // is always a nontrivial element of `<p> <= (Z/mZ)*`, where the characteristic of the
        // quotient is a power of `p`
        let (p, e) = is_prime_power(&ZZbig, &ring.characteristic(&ZZbig).unwrap()).unwrap();
        assert!(hypercube_structure.galois_group().eq_el(&frobenius, &hypercube_structure.galois_group().from_ring_el(hypercube_structure.galois_group().underlying_ring().coerce(&ZZbig, ZZbig.clone_el(&p)))));

        let ring_ref = &ring;
        let convolution = create_convolution(d, ring_ref.base_ring().integer_ring().abs_log2_ceil(ring_ref.base_ring().modulus()).unwrap());
        let slot_rings: Vec<SlotRingOf<R>> = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Computing slot rings", |[]| slot_ring_moduli.iter().map(|f| {
            let unwrap = UnwrapHom::from_delegate_ring(ZpeX.base_ring().get_ring());
            let modulus = (0..d).map(|i| ring_ref.base_ring().negate(unwrap.map_ref(ZpeX.coefficient_at(f, i)))).collect::<Vec<_>>();
            let slot_ring = FreeAlgebraImpl::new_with_convolution(RingValue::from(ring_ref.base_ring().get_ring().clone()), d, modulus, "𝝵", Global, convolution.clone());
            let max_ideal_gen = slot_ring.inclusion().map(slot_ring.base_ring().coerce(&ZZbig, ZZbig.clone_el(&p)));
            return SlotRingOf::<R>::from(AsLocalPIRBase::promise_is_local_pir(slot_ring, max_ideal_gen, Some(e)));
        }).collect::<Vec<_>>());

        let interpolation = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Computing interpolation data", |[]|
            FastPolyInterpolation::new(ZpeX, slot_ring_moduli)
        );

        let slot_generator_powers = Self::compute_slot_generator_powers(interpolation.poly_ring(), &hypercube_structure, &slot_rings);

        return Self {
            slot_generator_powers: slot_generator_powers,
            hypercube_structure: hypercube_structure,
            ring: ring,
            e: e,
            slot_to_ring_interpolation: interpolation,
            slot_rings: slot_rings,
        };
    }

    pub fn change_modulus<RNew>(&self, new_ring: RNew) -> HypercubeIsomorphism<RNew>
        where RNew: RingStore,
            RNew::Type: NumberRingQuotient,
            BaseRing<RNew>: NiceZn
    {
        let (p, e) = is_prime_power(&ZZbig, &new_ring.characteristic(&ZZbig).unwrap()).unwrap();
        let d = self.hypercube().d();
        let red_map = ZnReductionMap::new(self.ring().base_ring(), new_ring.base_ring()).unwrap();
        let poly_ring = DensePolyRing::new(new_ring.base_ring(), "X");
        let slot_rings = self.slot_rings.iter().map(|slot_ring| {
            let gen_poly = slot_ring.generating_poly(&poly_ring, &red_map);
            let new_slot_ring = FreeAlgebraImpl::new_with_convolution(
                RingValue::from(new_ring.base_ring().get_ring().clone()),
                d,
                (0..d).map(|i| new_ring.base_ring().negate(new_ring.base_ring().clone_el(poly_ring.coefficient_at(&gen_poly, i)))).collect::<Vec<_>>(),
                "𝝵",
                Global,
                create_convolution(d, new_ring.base_ring().integer_ring().abs_log2_ceil(new_ring.base_ring().modulus()).unwrap())
            );
            let max_ideal_gen = new_slot_ring.inclusion().map(new_slot_ring.base_ring().coerce(&ZZbig, ZZbig.clone_el(&p)));
            return AsLocalPIR::from(AsLocalPIRBase::promise_is_local_pir(new_slot_ring, max_ideal_gen, Some(e)));
        }).collect::<Vec<_>>();

        let Zpe: RingValue<DecoratedBaseRingBase<RNew>> = AsLocalPIR::from_zn(RingValue::from(new_ring.base_ring().get_ring().clone())).unwrap();
        let convolution = create_convolution(new_ring.rank(), Zpe.integer_ring().abs_log2_ceil(Zpe.modulus()).unwrap());
        let base_poly_ring = DensePolyRing::new_with_convolution(Zpe, "X", Global, convolution);

        let interpolation = self.slot_to_ring_interpolation.change_modulus(base_poly_ring);
        let slot_generator_powers = HypercubeIsomorphism::<RNew>::compute_slot_generator_powers(interpolation.poly_ring(), self.hypercube(), &slot_rings);

        return HypercubeIsomorphism {
            slot_generator_powers: slot_generator_powers,
            slot_to_ring_interpolation: interpolation,
            e: e,
            hypercube_structure: self.hypercube().clone(),
            ring: new_ring,
            slot_rings: slot_rings,
        };
    }

    pub fn hypercube(&self) -> &HypercubeStructure {
        &self.hypercube_structure
    }

    pub fn ring(&self) -> &R {
        &self.ring
    }

    pub fn slot_ring_at<'a>(&'a self, i: usize) -> &'a SlotRingOf<R>
        where R: 'a
    {
        &self.slot_rings[i]
    }

    pub fn slot_ring<'a>(&'a self) -> &'a SlotRingOf<R>
        where R: 'a
    {
        self.slot_ring_at(0)
    }

    pub fn p(&self) -> &GaloisGroupEl {
        self.hypercube().p()
    }

    pub fn e(&self) -> usize {
        self.e
    }

    pub fn d(&self) -> usize {
        self.hypercube_structure.d()
    }

    pub fn galois_group(&self) -> &Subgroup<CyclotomicGaloisGroup> {
        self.hypercube_structure.galois_group()
    }

    pub fn slot_count(&self) -> usize {
        self.hypercube_structure.element_count()
    }
    
    #[instrument(skip_all)]
    pub fn get_slot_value(&self, el: &El<R>, slot_index: &GaloisGroupEl) -> El<SlotRingOf<R>> {
        let el = self.ring().apply_galois_action(el, &self.galois_group().inv(slot_index));
        let poly_ring = DensePolyRing::new(self.ring.base_ring(), "X");
        let el_as_poly = self.ring().poly_repr(&poly_ring, &el, self.ring.base_ring().identity());
        let poly_modulus = self.slot_ring().generating_poly(&poly_ring, self.ring.base_ring().identity());
        let (_, rem) = poly_ring.div_rem_monic(el_as_poly, &poly_modulus);
        self.slot_ring().from_canonical_basis((0..self.d()).map(|i| poly_ring.base_ring().clone_el(poly_ring.coefficient_at(&rem, i))))
    }

    pub fn get_slot_values<'a>(&'a self, el: &'a El<R>) -> impl ExactSizeIterator<Item = El<SlotRingOf<R>>> + use<'a, R> {
        self.hypercube_structure.element_iter().map(move |g| self.get_slot_value(el, &g))
    }

    #[instrument(skip_all)]
    fn compute_slot_generator_powers(poly_ring: &ZpePolyRing<R>, hypercube_structure: &HypercubeStructure, slot_rings: &[SlotRingOf<R>]) -> Vec<Vec<El<ZpePolyRing<R>>>> {
        let wrap = WrapHom::to_delegate_ring(poly_ring.base_ring().get_ring());
        hypercube_structure.element_iter().zip(slot_rings.iter()).map(|(g, S)| {
            let image_zeta = S.pow(S.canonical_gen(), hypercube_structure.galois_group().representative(&g) as usize);
            (0..hypercube_structure.d()).scan(S.one(), |current, _| {
                let result = S.poly_repr(poly_ring, current, &wrap);
                S.mul_assign_ref(current, &image_zeta);
                return Some(result);
            }).collect()
        }).collect()
    }

    #[instrument(skip_all)]
    fn slot_ring_el_to_coset_X_repr<I>(&self, values: I) -> Vec<El<DensePolyRing<RingValue<DecoratedBaseRingBase<R>>>>>
        where I: IntoIterator<Item = El<SlotRingOf<R>>>
    {
        let poly_ring = self.slot_to_ring_interpolation.poly_ring();
        let mut values_it = values.into_iter();
        let wrap = WrapHom::to_delegate_ring(poly_ring.base_ring().get_ring());
        let result = values_it.by_ref().enumerate().map(|(i, a)| {
            let a_wrt_basis = self.slot_ring().wrt_canonical_basis(&a);
            let mut result = poly_ring.zero();
            let mut check = poly_ring.zero();
            for (c, zeta_pow) in a_wrt_basis.iter().zip(self.slot_generator_powers[i].iter()) {
                poly_ring.add_assign(&mut check, poly_ring.inclusion().mul_ref_map(&zeta_pow, &wrap.map_ref(&c)));
                result = poly_ring.inclusion().fma_map(zeta_pow, &wrap.map(c), result);
            }
            return result;
        }).collect::<Vec<_>>();
        assert!(values_it.next().is_none(), "iterator should only have {} elements", self.slot_count());
        return result;
    }

    #[instrument(skip_all)]
    pub fn from_slot_values<'a, I>(&self, values: I) -> El<R>
        where I: IntoIterator<Item = El<SlotRingOf<R>>>
    {
        let poly_ring = self.slot_to_ring_interpolation.poly_ring();
        let remainders = self.slot_ring_el_to_coset_X_repr(values);
        debug_assert!(remainders.iter().all(|r| poly_ring.degree(r).unwrap_or(0) < self.d()));

        let unreduced_result = self.slot_to_ring_interpolation.interpolate_unreduced(remainders);
        let hom = UnwrapHom::from_delegate_ring(poly_ring.base_ring().get_ring());
        if let Some(deg) = poly_ring.degree(&unreduced_result) {
            let result = self.ring().from_canonical_basis_extended((0..(deg + 1)).map(|i| hom.map_ref(poly_ring.coefficient_at(&unreduced_result, i))));
            result
        } else {
            self.ring().zero()
        }
    }

    ///
    /// Tries to load a [`HypercubeIsomorphism`] from the corresponding file
    /// in the given directory. If the file does not exist, a new
    /// [`HypercubeIsomorphism`] is created and stored in the file.
    /// 
    pub fn new<const LOG: bool>(ring: &R, hypercube_structure: &HypercubeStructure, cache_dir: Option<&str>) -> Self
        where R: Clone,
            BaseRing<R>: SerializableElementRing
    {
        let (p, e) = is_prime_power(&ZZbig, &ring.characteristic(&ZZbig).unwrap()).unwrap();
        let o = hypercube_structure.galois_group().subgroup_order();
        let m = ring.number_ring().galois_group().m();
        let d = hypercube_structure.d();
        let result = create_cached::<_, R, _, LOG>(
            &ring,
            || {
                let (ZpeX, slot_ring_moduli) = if d * d < m as usize {
                    if LOG {
                        println!("[HypercubeIsomorphism] Using algorithm optimized for small slot rings");
                    }
                    let (S, root) = Self::compute_tmp_slot_ring_and_root::<LOG>(ring, hypercube_structure);
                    Self::compute_slot_ring_moduli_small_slot_ring::<LOG>(ring, hypercube_structure, S, root)
                } else {
                    if LOG {
                        println!("[HypercubeIsomorphism] Using algorithm optimized for large slot rings");
                    }
                    let (FpX, factor) = Self::compute_factor_of_generating_poly_mod_p::<LOG>(ring, hypercube_structure);
                    Self::compute_slot_ring_moduli_large_slot_ring::<LOG>(ring, hypercube_structure, &FpX, &factor)
                };
                Self::create::<LOG>(ring.clone(), hypercube_structure.clone(), ZpeX, slot_ring_moduli)
            },
            &filename_keys![hypercube, m: m, o: o, p: p, e: e],
            cache_dir,
            if cache_dir.is_none() { StoreAs::None } else { StoreAs::AlwaysJson }
        );
        assert!(result.hypercube_structure == *hypercube_structure, "hypercube structure mismatch");

        return result;
    }

    pub fn new_with_poly_factor<P, const LOG: bool>(ring: &R, poly_ring: P, factor: &El<P>, hypercube_structure: &HypercubeStructure, cache_dir: Option<&str>) -> Self
        where P: RingStore + Copy,
            P::Type: PolyRing,
            <P::Type as RingExtension>::BaseRing: RingStore<Type = BaseRing<R>>,
            R: Clone
    {
        assert!(ring.base_ring().get_ring() == poly_ring.base_ring().get_ring());
        assert_eq!(hypercube_structure.d(), poly_ring.degree(factor).unwrap());let (p, e) = is_prime_power(&ZZbig, &ring.characteristic(&ZZbig).unwrap()).unwrap();

        let o = hypercube_structure.galois_group().subgroup_order();
        let m = ring.number_ring().galois_group().m();
        let d = hypercube_structure.d();
        let result = create_cached::<_, R, _, LOG>(
            ring,
            || {
                let (ZpeX, slot_ring_moduli) = if d * d < m as usize {
                    if LOG {
                        println!("[HypercubeIsomorphism] Using algorithm optimized for small slot rings");
                    }
                    let (S, root_of_unity) = Self::convert_tmp_slot_ring_and_root(ring, poly_ring, factor);
                    Self::compute_slot_ring_moduli_small_slot_ring::<LOG>(ring, hypercube_structure, S, root_of_unity)
                } else {
                    if LOG {
                        println!("[HypercubeIsomorphism] Using algorithm optimized for large slot rings");
                    }
                    let (FpX, factor) = Self::convert_factor_of_generating_poly_mod_p(ring, poly_ring, factor);
                    Self::compute_slot_ring_moduli_large_slot_ring::<LOG>(ring, hypercube_structure, &FpX, &factor)
                };
                Self::create::<LOG>(ring.clone(), hypercube_structure.clone(), ZpeX, slot_ring_moduli)
            },
            &filename_keys![hypercube, m: m, o: o, p: p, e: e],
            cache_dir,
            if cache_dir.is_none() { StoreAs::None } else { StoreAs::AlwaysJson }
        );
        assert!(result.hypercube_structure == *hypercube_structure, "hypercube structure mismatch");
        assert_el_eq!(&poly_ring, factor, result.slot_ring().generating_poly(&poly_ring, poly_ring.base_ring().identity()));

        return result;
    }

    #[instrument(skip_all)]
    fn convert_factor_of_generating_poly_mod_p<P>(ring: &R, poly_ring: P, factor: &El<P>) -> (FpPolyRing<R>, El<FpPolyRing<R>>)
        where P: RingStore,
            P::Type: PolyRing,
            <P::Type as RingExtension>::BaseRing: RingStore<Type = BaseRing<R>>,
            R: Clone
    {
        let (p, _) = is_prime_power(&ZZbig, &ring.characteristic(&ZZbig).unwrap()).unwrap();
        let Fp = RingValue::from(<<<R::Type as RingExtension>::BaseRing as RingStore>::Type as FromModulusCreateableZnRing>::from_modulus::<_, !>(|ZZ| 
            Ok(int_cast(ZZbig.clone_el(&p), RingRef::new(ZZ), ZZbig))
        ).unwrap_or_else(no_error)).as_field().ok().unwrap();
        let convolution = create_convolution(ring.rank(), Fp.integer_ring().abs_log2_ceil(Fp.modulus()).unwrap());
        let FpX = DensePolyRing::new_with_convolution(Fp, "X", Global, convolution);
        let hom = ZnReductionMap::new(poly_ring.base_ring(), FpX.base_ring()).unwrap();
        let factor = FpX.lifted_hom(&poly_ring, &hom).map_ref(factor);
        assert!(FpX.divides(&ring.generating_poly(&FpX, &hom), &factor), "invalid factor");
        return (FpX, factor);
    }

    ///
    /// Computes an irrreducible factor of the generating polynomial of the given ring,
    /// over the prime field.
    /// 
    /// Currently, we assume that this root is an `m`-th root of unity. This makes sense,
    /// since the Galois group currently is a subgroup of `(Z/mZ)*`, thus the ring always
    /// has a generator which is a root of unity.
    /// 
    #[instrument(skip_all)]
    fn compute_factor_of_generating_poly_mod_p<const LOG: bool>(ring: &R, hypercube_structure: &HypercubeStructure) -> (FpPolyRing<R>, El<FpPolyRing<R>>) {
        let m = ring.acting_galois_group().m() as usize;
        assert!(ring.is_one(&ring.pow(ring.canonical_gen(), m)), "HypercubeIsomorphism currently assumes that the generator of the ring is an m-th root of unity");

        let d = hypercube_structure.d();
        let (p, _) = is_prime_power(ring.base_ring().integer_ring(), &ring.base_ring().modulus()).unwrap();
        let p = int_cast(p, ZZbig, ring.base_ring().integer_ring());
        let Fp = RingValue::from(<<<R::Type as RingExtension>::BaseRing as RingStore>::Type as FromModulusCreateableZnRing>::from_modulus::<_, !>(|ZZ| 
            Ok(int_cast(ZZbig.clone_el(&p), RingRef::new(ZZ), ZZbig))
        ).unwrap_or_else(no_error)).as_field().ok().unwrap();
        let convolution = create_convolution(ring.rank(), Fp.integer_ring().abs_log2_ceil(Fp.modulus()).unwrap());
        let FpX = DensePolyRing::new_with_convolution(Fp, "X", Global, convolution);
        let Fp = FpX.base_ring();
        let Fq = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Creating Galois field", |[]|
            GaloisField::new_with_convolution(Fp, d, Global, create_convolution(d, Fp.integer_ring().abs_log2_ceil(Fp.modulus()).unwrap()))
        );
        let FqX = DensePolyRing::new(&Fq, "X");
        
        let root_of_unity = get_prim_root_of_unity(&Fq, m).unwrap();
        let gen_poly = ring.generating_poly(&FpX, ZnReductionMap::new(ring.base_ring(), FpX.base_ring()).unwrap());
        let root = (0..m).scan(Fq.one(), |state, _| {
            let result = Fq.clone_el(state);
            Fq.mul_assign_ref(state, &root_of_unity);
            Some(result)
        }).filter(|x| Fq.is_zero(&FpX.evaluate(&gen_poly, x, Fq.inclusion()))).next().unwrap();

        let mut result = FqX.prod((0..d).scan(
            root, 
            |current_root, _| {
                let result = FqX.sub(FqX.indeterminate(), FqX.inclusion().map_ref(current_root));
                *current_root = Fq.pow_gen(Fq.clone_el(current_root), &p, ZZbig);
                return Some(result);
            }
        ));
        let normalization_factor = FqX.base_ring().invert(FqX.lc(&result).unwrap()).unwrap();
        FqX.inclusion().mul_assign_map(&mut result, normalization_factor);

        let result = FpX.from_terms(FqX.terms(&result).map(|(c, i)| {
            let c_wrt_basis = Fq.wrt_canonical_basis(c);
            debug_assert!(c_wrt_basis.iter().skip(1).all(|c| Fp.is_zero(&c)));
            (c_wrt_basis.at(0), i)
        }));
        return (FpX, result);
    }

    #[instrument(skip_all)]
    fn convert_tmp_slot_ring_and_root<'a, P>(ring: &'a R, poly_ring: P, factor: &El<P>) -> (TmpSlotRingOf<'a, R>, El<TmpSlotRingOf<'a, R>>)
        where P: RingStore,
            P::Type: PolyRing,
            <P::Type as RingExtension>::BaseRing: RingStore<Type = BaseRing<R>>,
            R: Clone
    {
        assert!(poly_ring.base_ring().is_one(poly_ring.lc(factor).unwrap()));
        let (p, e) = is_prime_power(ring.base_ring().integer_ring(), &ring.base_ring().modulus()).unwrap();
        let Zpe = AsLocalPIR::<RingRef<_>>::from_zn(RingRef::new(ring.base_ring().get_ring())).unwrap();
        let d = poly_ring.degree(factor).unwrap();
        let mut modulus = SparseMapVector::new(d, Zpe.clone());
        let hom = WrapHom::to_delegate_ring(Zpe.get_ring());
        for (c, i) in poly_ring.terms(factor) {
            if i != d {
                *modulus.at_mut(i) = Zpe.negate(hom.map_ref(c));
            }
        }
        modulus.at_mut(0);
        let convolution = create_convolution(d, Zpe.integer_ring().abs_log2_ceil(Zpe.modulus()).unwrap());
        let S = FreeAlgebraImpl::new_with_convolution(Zpe, d, modulus, "θ", Global, convolution);
        let ideal_gen = S.inclusion().map(S.base_ring().coerce(S.base_ring().integer_ring(), p));
        let S = RingValue::from(AsLocalPIRBase::promise_is_local_pir(S, ideal_gen, Some(e)));
        let root_of_unity = S.canonical_gen();
        assert!(S.is_zero(&poly_ring.evaluate(&ring.generating_poly(&poly_ring, poly_ring.base_ring().identity()), &root_of_unity, S.inclusion().compose(WrapHom::to_delegate_ring(S.base_ring().get_ring())))), "invalid factor");
        return (S, root_of_unity);
    }

    ///
    /// Creates a temporary representation of the slot ring, and computes
    /// a root of the generating polynomial of `ring` as element of the
    /// slot ring.
    /// 
    /// Currently, we assume that this root is an `m`-th root of unity. This makes sense,
    /// since the Galois group currently is a subgroup of `(Z/mZ)*`, thus the ring always
    /// has a generator which is a root of unity.
    /// 
    #[instrument(skip_all)]
    fn compute_tmp_slot_ring_and_root<'a, const LOG: bool>(ring: &'a R, hypercube_structure: &HypercubeStructure) -> (TmpSlotRingOf<'a, R>, El<TmpSlotRingOf<'a, R>>) {
        
        let m = ring.acting_galois_group().m() as usize;
        assert!(ring.is_one(&ring.pow(ring.canonical_gen(), m)), "HypercubeIsomorphism currently assumes that the generator of the ring is an m-th root of unity");

        let d = hypercube_structure.d();
        let (p, _) = is_prime_power(&ZZbig, &ring.characteristic(&ZZbig).unwrap()).unwrap();
        let Fp = RingValue::from(<<<R::Type as RingExtension>::BaseRing as RingStore>::Type as FromModulusCreateableZnRing>::from_modulus::<_, !>(|ZZ| 
            Ok(int_cast(ZZbig.clone_el(&p), RingRef::new(ZZ), ZZbig))
        ).unwrap_or_else(no_error)).as_field().ok().unwrap();
        let convolution = create_convolution(d, Fp.integer_ring().abs_log2_ceil(Fp.modulus()).unwrap());
        let Fq = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Creating Galois field", |[]|
            GaloisField::new_with_convolution(Fp, d, Global, convolution)
        );
        let convolution = create_convolution(d, ring.base_ring().integer_ring().abs_log2_ceil(ring.base_ring().modulus()).unwrap());
        let S = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Creating temporary slot ring", |[]| {
            let base_ring: AsLocalPIR<RingRef<BaseRing<R>>> = AsLocalPIR::<RingRef<_>>::from_zn(RingRef::new(ring.base_ring().get_ring())).unwrap();
            Fq.get_ring().galois_ring_with(base_ring, Global, convolution)
        });

        let root_of_unity = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Computing root of unity", |[]| 
            hensel_lift_root_of_unity(&S, &Fq, get_prim_root_of_unity(&Fq, m).unwrap(), m)
        );

        debug_assert!(S.is_one(&S.pow(S.clone_el(&root_of_unity), m)));
        let ZpeX = DensePolyRing::new(S.base_ring(), "X");
        let gen_poly = ring.generating_poly(&ZpeX, ZnReductionMap::new(ring.base_ring(), ZpeX.base_ring()).unwrap());
        let root = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Searching for root of generating polynomial", |[]| (0..m).scan(S.one(), |state, _| {
            let result = S.clone_el(state);
            S.mul_assign_ref(state, &root_of_unity);
            Some(result)
        }).filter(|x| S.is_zero(&ZpeX.evaluate(&gen_poly, x, S.inclusion()))).next().unwrap());

        return (S, root);
    }

    ///
    /// Computes the complete factorization of the generating polynomial of
    /// the given ring over its base ring, in an order that matches the galois
    /// elements as enumerated by `hypercube_structure`.
    /// 
    #[instrument(skip_all)]
    fn compute_slot_ring_moduli_small_slot_ring<'a, const LOG: bool>(ring: &R, hypercube_structure: &HypercubeStructure, S: TmpSlotRingOf<'a, R>, root: El<TmpSlotRingOf<'a, R>>) -> (ZpePolyRing<R>, Vec<El<ZpePolyRing<R>>>) {
        
        let m = ring.acting_galois_group().m() as usize;
        assert!(ring.is_one(&ring.pow(ring.canonical_gen(), m)), "HypercubeIsomorphism currently assumes that the generator of the ring is an m-th root of unity");

        // in this case, we use an "internal" approach, i.e. work only within
        // the slot ring; since the slot ring is small, this is fast;
        // The main idea is that we already know how the slot ring should look like,
        // namely it is `GR(p, e, d)`. Once we find a root of unity in the slot
        // ring, we can compute its minimal polynomial and find a factor of `Phi_m`, 
        // without ever even computing `Phi_m`. Note however that this requires
        // a lot of operations within the slot ring, and if that is large, this
        // will be more expensive than an explicit factorization of `Phi_m`.

        let d = hypercube_structure.d();
        let (p, _) = is_prime_power(&ZZbig, &ring.characteristic(&ZZbig).unwrap()).unwrap();

        let Zpe: RingValue<DecoratedBaseRingBase<R>> = AsLocalPIR::from_zn(RingValue::from(ring.base_ring().get_ring().clone())).unwrap();
        let convolution = create_convolution(ring.rank(), ring.base_ring().integer_ring().abs_log2_ceil(ring.base_ring().modulus()).unwrap());
        let ZpeX = DensePolyRing::new_with_convolution(Zpe, "X", Global, convolution);
        let galois_group = ring.acting_galois_group();
        let slot_ring_moduli = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Computing factorization of cyclotomic polynomial", |[]| {
            let SX = DensePolyRing::new(&S, "X");
            let mut slot_ring_moduli = Vec::new();
            for g in hypercube_structure.element_iter() {
                let mut result = SX.prod((0..d).scan(
                    S.pow(S.clone_el(&root), galois_group.representative(&galois_group.inv(&g)) as usize), 
                    |current_root, _| {
                        let result = SX.sub(SX.indeterminate(), SX.inclusion().map_ref(current_root));
                        *current_root = S.pow_gen(S.clone_el(current_root), &p, ZZbig);
                        return Some(result);
                    }
                ));
                let normalization_factor = SX.base_ring().invert(SX.lc(&result).unwrap()).unwrap();
                SX.inclusion().mul_assign_map(&mut result, normalization_factor);
    
                let rewrap = WrapHom::to_delegate_ring(ZpeX.base_ring().get_ring()).compose(UnwrapHom::from_delegate_ring(S.base_ring().get_ring()));
                slot_ring_moduli.push(ZpeX.from_terms(SX.terms(&result).map(|(c, i)| {
                    let c_wrt_basis = S.wrt_canonical_basis(c);
                    debug_assert!(c_wrt_basis.iter().skip(1).all(|c| S.base_ring().is_zero(&c)));
                    return (rewrap.map(c_wrt_basis.at(0)), i);
                })));
            }
            return slot_ring_moduli;
        });
        drop(S);

        return (ZpeX, slot_ring_moduli);
    }

    ///
    /// Computes the complete factorization of the generating polynomial of
    /// the given ring over its base ring, in an order that matches the galois
    /// elements as enumerated by `hypercube_structure`.
    /// 
    #[instrument(skip_all)]
    fn compute_slot_ring_moduli_large_slot_ring<const LOG: bool>(ring: &R, hypercube_structure: &HypercubeStructure, FpX: &FpPolyRing<R>, factor: &El<FpPolyRing<R>>) -> (ZpePolyRing<R>, Vec<El<ZpePolyRing<R>>>) {

        // in case that the slot ring is large, it can actually be faster to compute in the
        // original ring, since that can use the structure of the cyclotomic polynomial for
        // a more efficient implementation. Hence, we only compute a single factor of the 
        // cyclotomic polynomial using computations in the slot ring, and then compute the
        // other factors as the suitable Galois conjugates of the first factor, which can
        // be done using arithmetic in the full ring.

        let (p, e) = is_prime_power(ring.base_ring().integer_ring(), ring.base_ring().modulus()).unwrap();

        let Zpe: RingValue<DecoratedBaseRingBase<R>> = AsLocalPIR::from_zn(RingValue::from(ring.base_ring().get_ring().clone())).unwrap();
        let convolution = create_convolution(ring.rank(), Zpe.integer_ring().abs_log2_ceil(Zpe.modulus()).unwrap());
        let ZpeX = DensePolyRing::new_with_convolution(Zpe, "X", Global, convolution);
        let Zpe = ZpeX.base_ring();

        let convolution = create_convolution(2 * ring.rank(), Zpe.integer_ring().abs_log2_ceil(Zpe.modulus()).unwrap());
        let ZpeX_undecorated = DensePolyRing::new_with_convolution(ring.base_ring(), "X", Global, convolution);
        let ZZX = DensePolyRing::new(ZZi64, "X");
        let gen_poly = ring.number_ring().generating_poly(&ZZX);
        let gen_poly_mod_pe = ZpeX_undecorated.lifted_hom(&ZZX, ZpeX_undecorated.base_ring().can_hom(ring.base_ring()).unwrap().compose(ring.base_ring().can_hom(&ZZX.base_ring()).unwrap())).map_ref(&gen_poly);
        let gen_poly_mod_p = FpX.lifted_hom(&ZZX, FpX.base_ring().can_hom(ZZX.base_ring()).unwrap()).map(gen_poly);
        
        let slot_ring_moduli = log_time::<_, _, LOG, _>("[HypercubeIsomorphism] Computing complete factorization of cyclotomic polynomial", |[]| {
            let mut result = Vec::new();
            let Zm = ring.number_ring().galois_group().underlying_ring();
            for g in hypercube_structure.element_iter() {
                let factor_conjugate = FpX.from_terms(
                    FpX.terms(&factor).map(|(c, i)| (
                        FpX.base_ring().clone_el(c),
                        Zm.smallest_positive_lift(Zm.mul(*ring.number_ring().galois_group().as_ring_el(&g), Zm.coerce(&ZZi64, i as i64))) as usize
                    ))
                );

                let ZZ = IntegersWithLocalZnQuotient::<BaseRing<R>>::new(Zpe.integer_ring(), Zpe.integer_ring().clone_el(&p));
                let reduction_context = ZZ.reduction_context(e);
                let reduction_map = reduction_context.intermediate_ring_to_field_reduction(0);
                let factor = FpX.normalize(FpX.ideal_gen(&factor_conjugate, &gen_poly_mod_p));
                let other_factor = FpX.checked_div(&gen_poly_mod_p, &factor).unwrap();
                let [lifted_factor, _] = hensel_lift_factorization(&reduction_map, &ZpeX_undecorated, &FpX, &gen_poly_mod_pe, &[factor, other_factor][..], DontObserve).try_into().ok().unwrap();

                result.push(ZpeX.lifted_hom(&ZpeX_undecorated, WrapHom::to_delegate_ring(Zpe.get_ring())).map(lifted_factor));
            }
            return result;
        });

        return (ZpeX, slot_ring_moduli);
    }
    
}

impl<R> SerializeDeserializeWith<R> for HypercubeIsomorphism<R>
    where R: RingStore + Clone,
        R::Type: NumberRingQuotient,
        BaseRing<R>: SerializableElementRing,
        BaseRing<R>: NiceZn
{
    type SerializeWithData<'a> = SerializableHypercubeIsomorphismWithoutRing<'a, R> where Self: 'a, R: 'a;
    type DeserializeWithData<'a> = DeserializeSeedHypercubeIsomorphismWithoutRing<R> where Self: 'a, R: 'a;

    fn serialize_with<'a>(&'a self, ring: &'a R) -> Self::SerializeWithData<'a> {
        assert!(self.ring.get_ring() == ring.get_ring());
        SerializableHypercubeIsomorphismWithoutRing::new(self)
    }

    fn deserialize_with<'a>(ring: &'a R) -> Self::DeserializeWithData<'a> {
        DeserializeSeedHypercubeIsomorphismWithoutRing::new(ring.clone())
    }
}

#[cfg(test)]
use feanor_math::rings::finite::*;
#[cfg(test)]
use crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use serde::de::DeserializeSeed;
#[cfg(test)]
use serde::Serialize;
#[cfg(test)]
use crate::number_ring::quotient_by_int::{NumberRingQuotientByInt, NumberRingQuotientByIntBase};
#[cfg(test)]
use crate::number_ring::quotient_by_ideal::NumberRingQuotientByIdealBase;

#[cfg(test)]
fn test_ring1() -> (NumberRingQuotientByInt<Pow2CyclotomicNumberRing, zn_64::Zn>, HypercubeStructure) {
    let galois_group = CyclotomicGaloisGroupBase::new(32);
    let p = galois_group.from_representative(7);
    let gs = vec![galois_group.from_representative(5)];
    let hypercube_structure = HypercubeStructure::new(galois_group.into().full_subgroup(), p, 4, vec![4], gs);
    let ring = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(32), zn_64::Zn::new(7));
    return (ring, hypercube_structure);
}

#[cfg(test)]
fn test_ring2() -> (NumberRingQuotientByInt<Pow2CyclotomicNumberRing, zn_64::Zn>, HypercubeStructure) {
    let galois_group = CyclotomicGaloisGroupBase::new(32);
    let gs = vec![galois_group.from_representative(5), galois_group.from_representative(-1)];
    let p = galois_group.from_representative(17);
    let hypercube_structure = HypercubeStructure::new(galois_group.into().full_subgroup(), p, 2, vec![4, 2], gs);
    let ring = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(32), zn_64::Zn::new(17));
    return (ring, hypercube_structure);
}

#[cfg(test)]
fn test_ring3() -> (NumberRingQuotientByInt<CompositeCyclotomicNumberRing, zn_64::Zn>, HypercubeStructure) {
    let galois_group = CyclotomicGaloisGroupBase::new(11 * 13);
    let p = galois_group.from_representative(3);
    let gs = vec![galois_group.from_representative(79), galois_group.from_representative(67)];
    let hypercube_structure = HypercubeStructure::new(
        galois_group.into().full_subgroup(),
        p,
        15,
        vec![2, 4],
        gs
    );
    let ring = NumberRingQuotientByIntBase::new(CompositeCyclotomicNumberRing::new(11, 13), zn_64::Zn::new(3));
    return (ring, hypercube_structure);
}

#[cfg(test)]
fn test_ring4() -> (NumberRingQuotientByIdeal<Pow2CyclotomicNumberRing, zn_64::Zn>, HypercubeStructure) {
    let galois_group = CyclotomicGaloisGroupBase::new(64);
    let acting_galois_group = galois_group.get_group().clone().subgroup([galois_group.from_representative(17)]);
    let p = galois_group.from_representative(257);
    let gs = vec![galois_group.from_representative(17)];
    let hypercube_structure = HypercubeStructure::new(acting_galois_group.clone(), p, 1, vec![4], gs);
    let FpX = DensePolyRing::new(zn_64::Zn::new(257), "X");
    let [t] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(4) - 2]);
    let ring = NumberRingQuotientByIdealBase::new::<false>(Pow2CyclotomicNumberRing::new(64), FpX, t, acting_galois_group);
    return (ring, hypercube_structure);
}

#[test]
fn test_hypercube_isomorphism_from_to_slot_vector() {

    fn test_from_to_slot_vector<R>((ring, hypercube): (R, HypercubeStructure))
        where R: RingStore,
            R::Type: NumberRingQuotient,
            BaseRing<R>: NiceZn,
            DecoratedBaseRingBase<R>: CanIsoFromTo<BaseRing<R>>
    {
        let mut rng = oorandom::Rand64::new(1);
        let isomorphism = HypercubeIsomorphism::new::<true>(&&ring, &hypercube, None);

        for _ in 0..10 {
            let slot_ring = isomorphism.slot_ring();
            let expected = (0..isomorphism.slot_count()).map(|_| slot_ring.random_element(|| rng.rand_u64())).collect::<Vec<_>>();
            let element = isomorphism.from_slot_values(expected.iter().map(|a| slot_ring.clone_el(a)));
            let actual = isomorphism.get_slot_values(&element).collect::<Vec<_>>();
            for (expected, actual) in expected.iter().zip(actual) {
                assert_el_eq!(slot_ring, expected, actual);
            }
        }
    }

    test_from_to_slot_vector(test_ring1());
    test_from_to_slot_vector(test_ring2());
    test_from_to_slot_vector(test_ring3());
    test_from_to_slot_vector(test_ring4());
}

#[test]
fn test_hypercube_isomorphism_is_isomorphic() {

    fn test_is_isomorphic<R>((ring, hypercube): (R, HypercubeStructure))
        where R: RingStore,
            R::Type: NumberRingQuotient,
            BaseRing<R>: NiceZn,
            DecoratedBaseRingBase<R>: CanIsoFromTo<BaseRing<R>>
    {
        let mut rng = oorandom::Rand64::new(1);
        let isomorphism = HypercubeIsomorphism::new::<true>(&&ring, &hypercube, None);
        for _ in 0..10 {
            let slot_ring = isomorphism.slot_ring();
            let lhs = (0..isomorphism.slot_count()).map(|_| slot_ring.random_element(|| rng.rand_u64())).collect::<Vec<_>>();
            let rhs = (0..isomorphism.slot_count()).map(|_| slot_ring.random_element(|| rng.rand_u64())).collect::<Vec<_>>();
            let expected = (0..isomorphism.slot_count()).map(|i| slot_ring.mul_ref(&lhs[i], &rhs[i])).collect::<Vec<_>>();
            let element = isomorphism.ring().mul(
                isomorphism.from_slot_values(lhs.iter().map(|a| slot_ring.clone_el(a))),
                isomorphism.from_slot_values(rhs.iter().map(|a| slot_ring.clone_el(a)))
            );
            let actual = isomorphism.get_slot_values(&element);
            for (expected, actual) in expected.iter().zip(actual) {
                assert_el_eq!(slot_ring, expected, actual);
            }
        }
    }

    test_is_isomorphic(test_ring1());
    test_is_isomorphic(test_ring2());
    test_is_isomorphic(test_ring3());
    test_is_isomorphic(test_ring4());
}

#[test]
fn test_hypercube_isomorphism_rotation() {

    fn test_rotation<R>((ring, hypercube): (R, HypercubeStructure))
        where R: RingStore,
            R::Type: NumberRingQuotient,
            BaseRing<R>: NiceZn,
            DecoratedBaseRingBase<R>: CanIsoFromTo<BaseRing<R>>
    {
        let mut rng = oorandom::Rand64::new(1);
        let isomorphism = HypercubeIsomorphism::new::<true>(&&ring, &hypercube, None);
        let ring = isomorphism.ring();
        let hypercube = isomorphism.hypercube();
        for _ in 0..10 {
            let slot_ring = isomorphism.slot_ring();
            let a = slot_ring.random_element(|| rng.rand_u64());

            let mut input = (0..isomorphism.slot_count()).map(|_| slot_ring.zero()).collect::<Vec<_>>();
            input[0] = slot_ring.clone_el(&a);
            let input = isomorphism.from_slot_values(input.into_iter());

            let mut expected = (0..isomorphism.slot_count()).map(|_| slot_ring.zero()).collect::<Vec<_>>();
            expected[(hypercube.dim_length(0) - 1) * hypercube.element_count() / hypercube.dim_length(0)] = slot_ring.clone_el(&a);

            let actual = ring.apply_galois_action(
                &input,
                &hypercube.galois_group().pow(hypercube.dim_generator(0), &int_cast(hypercube.dim_length(0) as i64 - 1, ZZbig, ZZi64))
            );

            let actual = isomorphism.get_slot_values(&actual);
            for (expected, actual) in expected.iter().zip(actual) {
                assert_el_eq!(slot_ring, expected, actual);
            }
        }
    }

    test_rotation(test_ring1());
    test_rotation(test_ring2());
    test_rotation(test_ring3());
    test_rotation(test_ring4());
}

#[test]
fn test_serialization() {

    fn test_with_test_ring<R>((ring, hypercube_structure): (R, HypercubeStructure))
        where R: RingStore,
            R::Type: NumberRingQuotient,
            BaseRing<R>: NiceZn + SerializableElementRing + CanIsoFromTo<zn_64::ZnBase>
    {
        let hypercube = HypercubeIsomorphism::new::<false>(&&ring, &hypercube_structure, None);
        let serializer = serde_assert::Serializer::builder().is_human_readable(true).build();
        let tokens = SerializableHypercubeIsomorphismWithoutRing::new(&hypercube).serialize(&serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(true).build();
        let deserialized_hypercube = DeserializeSeedHypercubeIsomorphismWithoutRing::new(&ring).deserialize(&mut deserializer).unwrap();
        assert!(hypercube.slot_ring().get_ring() == deserialized_hypercube.slot_ring().get_ring());
        assert_el_eq!(hypercube.ring(), 
            hypercube.from_slot_values((0..hypercube.slot_count()).map(|i| hypercube.slot_ring().int_hom().map(i as i32))), 
            deserialized_hypercube.from_slot_values((0..deserialized_hypercube.slot_count()).map(|i| deserialized_hypercube.slot_ring().int_hom().map(i as i32)))
        );

        let serializer = serde_assert::Serializer::builder().is_human_readable(false).build();
        let tokens = SerializableHypercubeIsomorphismWithoutRing::new(&hypercube).serialize(&serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(false).build();
        let deserialized_hypercube = DeserializeSeedHypercubeIsomorphismWithoutRing::new(&ring).deserialize(&mut deserializer).unwrap();
        assert!(hypercube.slot_ring().get_ring() == deserialized_hypercube.slot_ring().get_ring());
        assert_el_eq!(hypercube.ring(), 
            hypercube.from_slot_values((0..hypercube.slot_count()).map(|i| hypercube.slot_ring().int_hom().map(i as i32))), 
            deserialized_hypercube.from_slot_values((0..deserialized_hypercube.slot_count()).map(|i| deserialized_hypercube.slot_ring().int_hom().map(i as i32)))
        );
    }

    test_with_test_ring(test_ring1());
    test_with_test_ring(test_ring2());
    test_with_test_ring(test_ring3());
    test_with_test_ring(test_ring4());
}