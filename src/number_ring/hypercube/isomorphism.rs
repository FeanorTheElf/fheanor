use std::alloc::{Allocator, Global};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::sync::Arc;

use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::algorithms::convolution::fft::{FFTConvolution, FFTConvolutionZn};
use feanor_math::algorithms::convolution::rns::{RNSConvolution, RNSConvolutionZn};
use feanor_math::algorithms::convolution::{ConvolutionAlgorithm, STANDARD_CONVOLUTION};
use feanor_math::algorithms::eea::signed_gcd;
use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::algorithms::poly_gcd::hensel::hensel_lift_factorization;
use feanor_math::reduce_lift::poly_factor_gcd::PolyGCDLocallyIntermediateReductionMap;
use feanor_math::computation::DontObserve;
use feanor_math::field::Field;
use feanor_math::rings::poly::sparse_poly::SparsePolyRing;
use feanor_math::algorithms::linsolve::LinSolveRing;
use feanor_math::pid::PrincipalIdealRingStore;
use feanor_math::divisibility::{DivisibilityRing, DivisibilityRingStore};
use feanor_math::rings::field::AsFieldBase;
use feanor_math::homomorphism::*;
use feanor_math::integer::*;
use feanor_math::local::PrincipalLocalRing;
use feanor_math::primitive_int::{StaticRing, StaticRingBase};
use feanor_math::rings::extension::extension_impl::*;
use feanor_math::rings::extension::galois_field::GaloisField;
use feanor_math::rings::extension::{FreeAlgebra, FreeAlgebraStore};
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::local::{AsLocalPIR, AsLocalPIRBase};
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::poly::PolyRingStore;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::delegate::DelegateRing;
use feanor_math::ring::*;
use feanor_math::rings::zn::*;
use feanor_math::seq::*;
use feanor_math::serialization::SerializableElementRing;
use serde::de::DeserializeSeed;
use serde::Serialize;
use tracing::instrument;

use crate::cyclotomic::*;
use crate::{log_time, ZZi64};
use crate::ntt::dyn_convolution::*;
use crate::number_ring::hypercube::interpolate::FastPolyInterpolation;
use crate::number_ring::quotient::*;
use crate::number_ring::hypercube::structure::*;

pub use crate::number_ring::hypercube::serialization::{DeserializeSeedHypercubeIsomorphismWithoutRing, SerializableHypercubeIsomorphismWithoutRing};

#[instrument(skip_all)]
fn hensel_lift_factor<R1, R2, A1, A2, C1, C2>(from_ring: &DensePolyRing<R1, A1, C1>, to_ring: &DensePolyRing<R2, A2, C2>, f: &El<DensePolyRing<R1, A1, C1>>, g: El<DensePolyRing<R2, A2, C2>>) -> El<DensePolyRing<R1, A1, C1>>
    where R1: RingStore,
        R1::Type: ZnRing,
        R2: RingStore,
        R2::Type: ZnRing + Field + CanIsoFromTo<AsFieldBase<Zn>>,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C1: ConvolutionAlgorithm<R1::Type>,
        C2: ConvolutionAlgorithm<R2::Type>,
{
    let ZZ = StaticRing::<i64>::RING;
    let p = int_cast(to_ring.base_ring().integer_ring().clone_el(to_ring.base_ring().modulus()), ZZ, to_ring.base_ring().integer_ring());
    let (from_p, e) = is_prime_power(ZZ, &int_cast(from_ring.base_ring().integer_ring().clone_el(from_ring.base_ring().modulus()), ZZ, from_ring.base_ring().integer_ring())).unwrap();
    assert_eq!(p, from_p);

    let Zpe = zn_big::Zn::new(BigIntRing::RING, BigIntRing::RING.pow(int_cast(p, BigIntRing::RING, ZZ), e));
    let Zp = zn_big::Zn::new(BigIntRing::RING, int_cast(p, BigIntRing::RING, ZZ));
    let Fp = Zn::new(p as u64).as_field().ok().unwrap();
    let red_map = PolyGCDLocallyIntermediateReductionMap::new(ZZ.get_ring(), &p, &Zpe, e, &Zp, 1, 0);
    let ZpeX = DensePolyRing::new(&Zpe, "X");
    let FpX = DensePolyRing::new(&Fp, "X");
    let to_ZpeX = ZpeX.lifted_hom(from_ring, ZnReductionMap::new(from_ring.base_ring(), ZpeX.base_ring()).unwrap());
    let from_ZpeX = from_ring.lifted_hom(&ZpeX, ZnReductionMap::new(ZpeX.base_ring(), from_ring.base_ring()).unwrap());
    let to_FpX = FpX.lifted_hom(to_ring, to_ring.base_ring().can_iso(FpX.base_ring()).unwrap());

    let f_mod_p = FpX.lifted_hom(&ZpeX, Fp.can_hom(&Zp).unwrap().compose(&red_map)).compose(&to_ZpeX).map_ref(f);
    let f_over_g = FpX.checked_div(&f_mod_p, &to_FpX.map_ref(&g)).unwrap();
    let lifted = hensel_lift_factorization(&red_map, &ZpeX, &FpX, &to_ZpeX.map_ref(f), &[to_FpX.map(g), f_over_g][..], DontObserve);
    return from_ZpeX.map(lifted.into_iter().next().unwrap());
}

#[instrument(skip_all)]
fn get_prim_root_of_unity<R>(ring: R, m: usize) -> El<R>
    where R: RingStore,
        R::Type: FiniteRing + FreeAlgebra + DivisibilityRing,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: PrincipalLocalRing + ZnRing + CanHomFrom<StaticRingBase<i64>>
{
    let (p, e) = is_prime_power(&ZZi64, &ring.characteristic(&ZZi64).unwrap()).unwrap();
    let galois_field = GaloisField::new_with(
        Zn::new(p as u64).as_field().ok().unwrap(), 
        ring.rank(), 
        Global, 
        create_convolution(ring.rank(), ring.base_ring().integer_ring().abs_log2_ceil(ring.base_ring().modulus()).unwrap())
    );

    let rou = feanor_math::algorithms::unity_root::get_prim_root_of_unity(&galois_field, m).unwrap();

    let red_map = ZnReductionMap::new(ring.base_ring(), galois_field.base_ring()).unwrap();
    let mut result = ring.from_canonical_basis(galois_field.wrt_canonical_basis(&rou).into_iter().map(|x| red_map.smallest_lift(x)));

    // perform hensel lifting
    for _ in 0..e {
        let delta = ring.checked_div(
            &ring.sub(ring.pow(ring.clone_el(&result), m), ring.one()),
            &ring.inclusion().mul_map(ring.pow(ring.clone_el(&result), m - 1), ring.base_ring().coerce(&ZZi64, m as i64)) 
        ).unwrap();
        ring.sub_assign(&mut result, delta);
    }
    assert!(ring.is_one(&ring.pow(ring.clone_el(&result), m)));
    return result;
}

fn create_convolution<R>(d: usize, log2_input_size: usize) -> DynConvolutionAlgorithmConvolution<R, Arc<dyn Send + Sync + DynConvolutionAlgorithm<R>>>
    where R: ?Sized + ZnRing + CanHomFrom<BigIntRingBase> + CanHomFrom<StaticRingBase<i64>>
{
    let fft_convolution = FFTConvolution::new_with(Global);
    let max_log2_len = ZZi64.abs_log2_ceil(&(d as i64)).unwrap() + 1;
    if d <= 30 {
        DynConvolutionAlgorithmConvolution::new(Arc::new(STANDARD_CONVOLUTION))
    } else if fft_convolution.has_sufficient_precision(max_log2_len, log2_input_size) {
        DynConvolutionAlgorithmConvolution::new(Arc::new(FFTConvolutionZn::from(fft_convolution)))
    } else {
        DynConvolutionAlgorithmConvolution::new(Arc::new(RNSConvolutionZn::from(RNSConvolution::new(max_log2_len))))
    }
}

pub type SlotRingOver<R> = AsLocalPIR<FreeAlgebraImpl<R, Vec<El<R>>, Global, DynConvolutionAlgorithmConvolution<<R as RingStore>::Type, Arc<dyn Send + Sync + DynConvolutionAlgorithm<<R as RingStore>::Type>>>>>;
pub type SlotRingOf<R> = SlotRingOver<RingValue<BaseRing<R>>>;

pub type DefaultHypercube<'a, NumberRing, A = Global> = HypercubeIsomorphism<&'a NumberRingQuotient<NumberRing, Zn, A>>;

pub type BaseRing<R> = <<<R as RingStore>::Type as RingExtension>::BaseRing as RingStore>::Type;
pub type DecoratedBaseRing<R> = AsLocalPIR<RingValue<BaseRing<R>>>;

///
/// Represents the isomorphism
/// ```text
///   Fp[X]/(Phi_n(X)) -> F_(p^d)^((Z/nZ)*/<p>)
/// ```
/// where `d` is the order of `p` in `(Z/nZ)*`.
/// The group `(Z/nZ)*/<p>` is represented by a [`HypercubeStructure`].
/// 
/// In fact, the more general case of `(Z/p^eZ)[X]/(Phi_n(X))` is supported.
/// 
/// # Serialization
/// 
/// There are two ways of serializing/deserializing a [`HypercubeIsomorphism`]
///  - you can serialize the isomorphism including the implementation of `Fp[X]/(Phi_n(X))`
///    (if the latter is serializable) using the implementation of [`serde::Serialize`] and
///    [`serde::Deserialize`]
///  - alternatively, you can serialize the isomorphism without the ring implementation
///    using [`SerializableHypercubeIsomorphismWithoutRing`] and 
///    [`DeserializeSeedHypercubeIsomorphismWithoutRing`]; 
///    this of course requires that the ring is provided at deserialization time
/// 
pub struct HypercubeIsomorphism<R>
    where R: RingStore,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    ring: R,
    e: usize,
    slot_rings: Vec<SlotRingOf<R>>,
    slot_to_ring_interpolation: FastPolyInterpolation<DensePolyRing<DecoratedBaseRing<R>, Global>>,
    hypercube_structure: HypercubeStructure,
}

impl<R> HypercubeIsomorphism<R>
    where R: RingStore,
        R::Type: CyclotomicRing,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    pub fn new_cache_file<const LOG: bool>(ring: R, hypercube_structure: HypercubeStructure, dir: &str) -> Self
        where BaseRing<R>: SerializableElementRing
    {
        let (p, e) = is_prime_power(&ZZi64, &ring.characteristic(&ZZi64).unwrap()).unwrap();
        let filename = format!("{}/hypercube_n{}_p{}_e{}.json", dir, ring.n(), p, e);
        if let Ok(file) = File::open(filename.as_str()) {
            if LOG {
                println!("Reading from file {}", filename);
            }
            let reader = serde_json::de::IoRead::new(BufReader::new(file));
            let mut deserializer = serde_json::Deserializer::new(reader);
            let deserialized = DeserializeSeedHypercubeIsomorphismWithoutRing::new(ring).deserialize(&mut deserializer).unwrap();
            assert!(deserialized.hypercube() == &hypercube_structure);
            return deserialized;
        }
        let result = Self::new::<LOG>(ring, hypercube_structure);
        let file = File::create(filename.as_str()).unwrap();
        let writer = BufWriter::new(file);
        let mut serializer = serde_json::Serializer::new(writer);
        SerializableHypercubeIsomorphismWithoutRing::new(&result).serialize(&mut serializer).unwrap();
        return result;
    }

    pub fn new<const LOG: bool>(ring: R, hypercube_structure: HypercubeStructure) -> Self {      
        let d = hypercube_structure.d();  
        if d * d < hypercube_structure.n() {
            return Self::new_small_slot_ring::<LOG>(ring, hypercube_structure);
        } else {
            return Self::new_large_slot_ring::<LOG>(ring, hypercube_structure);
        }
    }

    ///
    /// Creates a new [`HypercubeIsomorphism`], using algorithms that are
    /// optimized for few large slots.
    /// 
    #[instrument(skip_all)]
    fn new_large_slot_ring<const LOG: bool>(ring: R, hypercube_structure: HypercubeStructure) -> Self {
        let n = ring.n() as usize;
        let d = hypercube_structure.d();
        let (p, _) = is_prime_power(&ZZi64, &ring.characteristic(&ZZi64).unwrap()).unwrap();
        assert!(signed_gcd(n as i64, p, ZZi64) == 1, "currently the ramified case is not implemented");
        let galois_group = hypercube_structure.galois_group();
        assert_eq!(n, galois_group.n());
        assert!(galois_group.eq_el(hypercube_structure.p(), galois_group.from_representative(p)));

        let decorated_base_ring: DecoratedBaseRing<R> = AsLocalPIR::from_zn(RingValue::from(ring.base_ring().get_ring().clone())).unwrap();
        let ZpeX = DensePolyRing::new_with(decorated_base_ring, "X", Global, STANDARD_CONVOLUTION);
        let FpX = DensePolyRing::new_with(Zn::new(p as u64).as_field().ok().unwrap(), "X", Global, create_convolution(n as usize, ZZi64.abs_log2_ceil(&p).unwrap()));
        let ZZX = SparsePolyRing::new(ZZi64, "X");
        let Phi_n = cyclotomic_polynomial(&ZZX, n);
        let Phi_n_mod_pe = ZpeX.lifted_hom(&ZZX, ZpeX.base_ring().can_hom(ZZX.base_ring()).unwrap()).map_ref(&Phi_n);
        let Phi_n_mod_p = FpX.lifted_hom(&ZZX, FpX.base_ring().can_hom(ZZX.base_ring()).unwrap()).map(Phi_n);

        let tmp_slot_ring = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_small_slot_ring] Creating temporary slot ring", |[]| {
            let base_ring = Zn::new(p as u64).as_field().ok().unwrap();
            GaloisField::new_with(
                base_ring, 
                d, 
                Global, 
                create_convolution(d, ZZi64.abs_log2_ceil(&p).unwrap())
            ).get_ring().galois_ring_with(
                AsLocalPIR::from_zn(RingRef::new(ring.base_ring().get_ring())).unwrap(), 
                Global, 
                create_convolution(d, ring.base_ring().integer_ring().abs_log2_ceil(ring.base_ring().modulus()).unwrap())
            )
        });

        let root_of_unity = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_small_slot_ring] Computing root of unity", |[]| 
            get_prim_root_of_unity(&tmp_slot_ring, n)
        );

        let slot_ring_modulus = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_small_slot_ring] Computing single factor of cyclotomic polynomial", |[]| {
            let SX = DensePolyRing::new(&tmp_slot_ring, "X");
            let mut result = SX.prod((0..d).scan(
                root_of_unity, 
                |current_root_of_unity, _| {
                    let result = SX.sub(SX.indeterminate(), SX.inclusion().map_ref(current_root_of_unity));
                    *current_root_of_unity = tmp_slot_ring.pow(tmp_slot_ring.clone_el(current_root_of_unity), p as usize);
                    return Some(result);
                }
            ));
            let normalization_factor = SX.base_ring().invert(SX.lc(&result).unwrap()).unwrap();
            SX.inclusion().mul_assign_map(&mut result, normalization_factor);
    
            let red_map = ZnReductionMap::new(SX.base_ring().base_ring(), FpX.base_ring()).unwrap();
            return FpX.from_terms(SX.terms(&result).map(|(c, i)| {
                let c_wrt_basis = tmp_slot_ring.wrt_canonical_basis(c);
                debug_assert!(c_wrt_basis.iter().skip(1).all(|c| tmp_slot_ring.base_ring().is_zero(&c)));
                return (red_map.map(c_wrt_basis.at(0)), i);
            }));
        });
        drop(tmp_slot_ring);
        
        let slot_ring_moduli = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_large_slot_ring] Computing complete factorization of cyclotomic polynomial", |[]| {
            let mut result = Vec::new();
            for g in hypercube_structure.element_iter() {
                let slot_ring_modulus_mod_p = FpX.from_terms(
                    FpX.terms(&slot_ring_modulus).map(|(c, i)| (
                        *c,
                        (galois_group.representative(g) * i as usize) % n
                    ))
                );
                result.push(hensel_lift_factor(&ZpeX, &FpX, &Phi_n_mod_pe, FpX.normalize(FpX.ideal_gen(&slot_ring_modulus_mod_p, &Phi_n_mod_p))));
            }
            return result;
        });

        return Self::create::<LOG>(ring, hypercube_structure, ZpeX, slot_ring_moduli);
    }

    ///
    /// Creates a new [`HypercubeIsomorphism`], using algorithms that are
    /// optimized for many small slots.
    /// 
    #[instrument(skip_all)]
    fn new_small_slot_ring<const LOG: bool>(ring: R, hypercube_structure: HypercubeStructure) -> Self {
        let n = ring.n() as usize;
        let d = hypercube_structure.d();
        let (p, _) = is_prime_power(&ZZi64, &ring.characteristic(&ZZi64).unwrap()).unwrap();
        let galois_group = hypercube_structure.galois_group();
        assert_eq!(n, galois_group.n());
        assert!(galois_group.eq_el(hypercube_structure.p(), galois_group.from_representative(p)));

        // in this case, we use an "internal" approach, i.e. work only within
        // the slot ring; since the slot ring is small, this is fast;
        // The main idea is that we already know how the slot ring should look like,
        // namely it is `GR(p, e, d)`. Once we find a root of unity in the slot
        // ring, we can compute its minimal polynomial and find a factor of `Phi_n`, 
        // without ever even computing `Phi_n`. Note however that this requires
        // a lot of operations within the slot ring, and if that is large, this
        // will be more expensive than an explicit factorization of `Phi_n`.

        let tmp_slot_ring = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_small_slot_ring] Creating temporary slot ring", |[]| {
            let base_ring = Zn::new(p as u64).as_field().ok().unwrap();
            GaloisField::new_with(
                base_ring, 
                d, 
                Global, 
                create_convolution(d, ZZi64.abs_log2_ceil(&p).unwrap())
            ).get_ring().galois_ring_with(
                AsLocalPIR::from_zn(RingRef::new(ring.base_ring().get_ring())).unwrap(), 
                Global, 
                create_convolution(d, ring.base_ring().integer_ring().abs_log2_ceil(ring.base_ring().modulus()).unwrap())
            )
        });

        let root_of_unity = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_small_slot_ring] Computing root of unity", |[]| 
            get_prim_root_of_unity(&tmp_slot_ring, n)
        );

        let decorated_base_ring: DecoratedBaseRing<R> = AsLocalPIR::from_zn(RingValue::from(ring.base_ring().get_ring().clone())).unwrap();
        let ZpeX = DensePolyRing::new_with(decorated_base_ring, "X", Global, STANDARD_CONVOLUTION);
        let slot_ring_moduli = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_small_slot_ring] Computing factorization of cyclotomic polynomial", |[]| {
            let SX = DensePolyRing::new(&tmp_slot_ring, "X");
            let mut slot_ring_moduli = Vec::new();
            for g in hypercube_structure.element_iter() {
                let mut result = SX.prod((0..d).scan(
                    tmp_slot_ring.pow(tmp_slot_ring.clone_el(&root_of_unity), galois_group.representative(galois_group.invert(g))), 
                    |current_root_of_unity, _| {
                        let result = SX.sub(SX.indeterminate(), SX.inclusion().map_ref(current_root_of_unity));
                        *current_root_of_unity = tmp_slot_ring.pow(tmp_slot_ring.clone_el(current_root_of_unity), p as usize);
                        return Some(result);
                    }
                ));
                let normalization_factor = SX.base_ring().invert(SX.lc(&result).unwrap()).unwrap();
                SX.inclusion().mul_assign_map(&mut result, normalization_factor);
    
                slot_ring_moduli.push(ZpeX.from_terms(SX.terms(&result).map(|(c, i)| {
                    let c_wrt_basis = tmp_slot_ring.wrt_canonical_basis(c);
                    debug_assert!(c_wrt_basis.iter().skip(1).all(|c| tmp_slot_ring.base_ring().is_zero(&c)));
                    return (ZpeX.base_ring().get_ring().rev_delegate(tmp_slot_ring.base_ring().get_ring().delegate(c_wrt_basis.at(0))), i);
                })));
            }
            return slot_ring_moduli;
        });
        drop(tmp_slot_ring);

        return Self::create::<LOG>(ring, hypercube_structure, ZpeX, slot_ring_moduli);
    }

    #[instrument(skip_all)]
    pub fn create<const LOG: bool>(ring: R, hypercube_structure: HypercubeStructure, ZpeX: DensePolyRing<AsLocalPIR<RingValue<BaseRing<R>>>>, slot_ring_moduli: Vec<El<DensePolyRing<AsLocalPIR<RingValue<BaseRing<R>>>>>>) -> Self {
        assert_eq!(ring.n(), hypercube_structure.n());
        let (p, e) = is_prime_power(&ZZi64, &ring.characteristic(&ZZi64).unwrap()).unwrap();
        assert!(hypercube_structure.galois_group().eq_el(hypercube_structure.galois_group().from_representative(p), hypercube_structure.frobenius(1)));
        let d = hypercube_structure.d();

        let slot_rings = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_small_slot_ring] Computing slot rings", |[]| slot_ring_moduli.iter().map(|f| {
            let modulus = (0..d).map(|i| ZpeX.base_ring().get_ring().delegate(ZpeX.base_ring().negate(ZpeX.base_ring().clone_el(ZpeX.coefficient_at(f, i))))).collect::<Vec<_>>();
            let slot_ring = FreeAlgebraImpl::new_with(
                RingValue::from(ring.base_ring().get_ring().clone()),
                d,
                modulus,
                "𝝵",
                Global,
                create_convolution(d, ring.base_ring().integer_ring().abs_log2_ceil(ring.base_ring().modulus()).unwrap())
            );
            let max_ideal_gen = slot_ring.inclusion().map(slot_ring.base_ring().coerce(&ZZi64, p));
            return AsLocalPIR::from(AsLocalPIRBase::promise_is_local_pir(slot_ring, max_ideal_gen, Some(e)));
        }).collect::<Vec<_>>());

        let interpolation = log_time::<_, _, LOG, _>("[HypercubeIsomorphism::new_small_slot_ring] Computing interpolation data", |[]|
            FastPolyInterpolation::new(ZpeX, slot_ring_moduli)
        );

        return Self {
            hypercube_structure: hypercube_structure,
            ring: ring,
            e: e,
            slot_to_ring_interpolation: interpolation,
            slot_rings: slot_rings
        };
    }

    pub fn change_modulus<RNew>(&self, new_ring: RNew) -> HypercubeIsomorphism<RNew>
        where RNew: RingStore,
            RNew::Type: CyclotomicRing,
            BaseRing<RNew>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing,
            AsFieldBase<DecoratedBaseRing<RNew>>: CanIsoFromTo<<DecoratedBaseRing<RNew> as RingStore>::Type> + SelfIso
    {
        let (p, e) = is_prime_power(&ZZi64, &new_ring.characteristic(&ZZi64).unwrap()).unwrap();
        let d = self.hypercube().d();
        let red_map = ZnReductionMap::new(self.ring().base_ring(), new_ring.base_ring()).unwrap();
        let poly_ring = DensePolyRing::new(new_ring.base_ring(), "X");
        let slot_rings = self.slot_rings.iter().map(|slot_ring| {
            let gen_poly = slot_ring.generating_poly(&poly_ring, &red_map);
            let new_slot_ring = FreeAlgebraImpl::new_with(
                RingValue::from(new_ring.base_ring().get_ring().clone()),
                d,
                (0..d).map(|i| new_ring.base_ring().negate(new_ring.base_ring().clone_el(poly_ring.coefficient_at(&gen_poly, i)))).collect::<Vec<_>>(),
                "𝝵",
                Global,
                create_convolution(d, ZZi64.abs_log2_ceil(&p).unwrap())
            );
            let max_ideal_gen = new_slot_ring.inclusion().map(new_slot_ring.base_ring().coerce(&ZZi64, p));
            return AsLocalPIR::from(AsLocalPIRBase::promise_is_local_pir(new_slot_ring, max_ideal_gen, Some(e)));
        }).collect::<Vec<_>>();

        let decorated_base_ring: DecoratedBaseRing<RNew> = AsLocalPIR::from_zn(RingValue::from(new_ring.base_ring().get_ring().clone())).unwrap();
        let base_poly_ring = DensePolyRing::new_with(decorated_base_ring, "X", Global, STANDARD_CONVOLUTION);
        return HypercubeIsomorphism {
            slot_to_ring_interpolation: self.slot_to_ring_interpolation.change_modulus(base_poly_ring),
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

    pub fn p(&self) -> i64 {
        self.galois_group().representative(self.hypercube_structure.p()) as i64
    }

    pub fn e(&self) -> usize {
        self.e
    }

    pub fn d(&self) -> usize {
        self.hypercube_structure.d()
    }

    pub fn galois_group(&self) -> &CyclotomicGaloisGroup {
        self.hypercube_structure.galois_group()
    }

    pub fn slot_count(&self) -> usize {
        self.hypercube_structure.element_count()
    }
    
    #[instrument(skip_all)]
    pub fn get_slot_value(&self, el: &El<R>, slot_index: CyclotomicGaloisGroupEl) -> El<SlotRingOf<R>> {
        let el = self.ring().apply_galois_action(el, self.galois_group().invert(slot_index));
        let poly_ring = DensePolyRing::new(self.ring.base_ring(), "X");
        let el_as_poly = self.ring().poly_repr(&poly_ring, &el, self.ring.base_ring().identity());
        let poly_modulus = self.slot_ring().generating_poly(&poly_ring, self.ring.base_ring().identity());
        let (_, rem) = poly_ring.div_rem_monic(el_as_poly, &poly_modulus);
        self.slot_ring().from_canonical_basis((0..self.d()).map(|i| poly_ring.base_ring().clone_el(poly_ring.coefficient_at(&rem, i))))
    }

    #[instrument(skip_all)]
    pub fn get_slot_values<'a>(&'a self, el: &'a El<R>) -> impl ExactSizeIterator<Item = El<SlotRingOf<R>>> + use<'a, R> {
        self.hypercube_structure.element_iter().map(move |g| self.get_slot_value(el, g))
    }

    #[instrument(skip_all)]
    pub fn from_slot_values<'a, I>(&self, values: I) -> El<R>
        where I: IntoIterator<Item = El<SlotRingOf<R>>>
    {
        let poly_ring = self.slot_to_ring_interpolation.poly_ring();
        let first_slot_ring: &SlotRingOf<R> = self.slot_ring();
        let mut values_it = values.into_iter();
        let wrap = LambdaHom::new(first_slot_ring.base_ring(), poly_ring.base_ring(), |from, to, x| to.get_ring().rev_delegate(from.clone_el(x)));
        let unwrap = LambdaHom::new(poly_ring.base_ring(), first_slot_ring.base_ring(), |from, _to, x| from.get_ring().delegate(from.clone_el(x)));

        let remainders = values_it.by_ref().zip(self.hypercube_structure.element_iter()).enumerate().map(|(i, (a, g))| {
            let f = first_slot_ring.poly_repr(&poly_ring, &a, &wrap);
            let local_slot_ring = self.slot_ring_at(i);
            let image_zeta = local_slot_ring.pow(local_slot_ring.canonical_gen(), self.galois_group().representative(g));
            return local_slot_ring.poly_repr(&poly_ring, &poly_ring.evaluate(&f, &image_zeta, local_slot_ring.inclusion().compose(&unwrap)), &wrap);
        }).collect::<Vec<_>>();
        assert!(values_it.next().is_none(), "iterator should only have {} elements", self.slot_count());
        debug_assert!(remainders.iter().all(|r| poly_ring.degree(r).unwrap_or(0) < self.d()));

        let unreduced_result = self.slot_to_ring_interpolation.interpolate_unreduced(remainders);
        let unreduced_result = (0..=poly_ring.degree(&unreduced_result).unwrap_or(0)).map(|i| poly_ring.base_ring().clone_el(poly_ring.coefficient_at(&unreduced_result, i))).collect::<Vec<_>>();

        let canonical_gen_pow_rank = self.ring().mul(self.ring().canonical_gen(), self.ring().from_canonical_basis((1..self.ring().rank()).map(|_| self.ring().base_ring().zero()).chain([self.ring().base_ring().one()].into_iter())));
        let mut current = self.ring().one();
        return <_ as RingStore>::sum(&self.ring, unreduced_result.chunks(self.ring.rank()).map(|chunk| self.ring.from_canonical_basis(
            chunk.iter().map(|a| poly_ring.base_ring().clone_el(a)).chain((0..(self.ring.rank() - chunk.len())).map(|_| poly_ring.base_ring().zero()))
                .map(|x| unwrap.map(x))
        )).map(|x| {
            let result = self.ring().mul_ref_snd(x, &current);
            self.ring().mul_assign_ref(&mut current, &canonical_gen_pow_rank);
            return result;
        }));
    }
}

#[cfg(test)]
use feanor_math::rings::finite::*;
#[cfg(test)]
use crate::number_ring::odd_cyclotomic::CompositeCyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use std::rc::Rc;
#[cfg(test)]
use std::ptr::Alignment;

#[cfg(test)]
fn test_ring1() -> (NumberRingQuotient<Pow2CyclotomicNumberRing, Zn>, HypercubeStructure) {
    let galois_group = CyclotomicGaloisGroup::new(32);
    let hypercube_structure = HypercubeStructure::new(
        galois_group,
        galois_group.from_representative(7),
        4,
        vec![4],
        vec![galois_group.from_representative(5)]
    );
    let ring = NumberRingQuotientBase::new(Pow2CyclotomicNumberRing::new(32), Zn::new(7));
    return (ring, hypercube_structure);
}

#[cfg(test)]
fn test_ring2() -> (NumberRingQuotient<Pow2CyclotomicNumberRing, Zn>, HypercubeStructure) {
    let galois_group = CyclotomicGaloisGroup::new(32);
    let hypercube_structure = HypercubeStructure::new(
        galois_group,
        galois_group.from_representative(17),
        2,
        vec![4, 2],
        vec![galois_group.from_representative(5), galois_group.from_representative(-1)]
    );
    let ring = NumberRingQuotientBase::new(Pow2CyclotomicNumberRing::new(32), Zn::new(17));
    return (ring, hypercube_structure);
}

#[cfg(test)]
fn test_ring3() -> (NumberRingQuotient<CompositeCyclotomicNumberRing, Zn>, HypercubeStructure) {
    let galois_group = CyclotomicGaloisGroup::new(11 * 13);
    let hypercube_structure = HypercubeStructure::new(
        galois_group,
        galois_group.from_representative(3),
        15,
        vec![2, 4],
        vec![galois_group.from_representative(79), galois_group.from_representative(67)]
    );
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(11, 13), Zn::new(3));
    return (ring, hypercube_structure);
}

#[test]
fn test_hypercube_isomorphism_from_to_slot_vector() {
    let mut rng = oorandom::Rand64::new(1);

    let (ring, hypercube) = test_ring1();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
    assert_eq!(4, isomorphism.slot_count());
    for _ in 0..10 {
        let slot_ring = isomorphism.slot_ring();
        let expected = (0..isomorphism.slot_count()).map(|_| slot_ring.random_element(|| rng.rand_u64())).collect::<Vec<_>>();
        let element = isomorphism.from_slot_values(expected.iter().map(|a| slot_ring.clone_el(a)));
        let actual = isomorphism.get_slot_values(&element);
        for (expected, actual) in expected.iter().zip(actual) {
            assert_el_eq!(slot_ring, expected, actual);
        }
    }

    let (ring, hypercube) = test_ring2();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
    assert_eq!(8, isomorphism.slot_count());
    for _ in 0..10 {
        let slot_ring = isomorphism.slot_ring();
        let expected = (0..isomorphism.slot_count()).map(|_| slot_ring.random_element(|| rng.rand_u64())).collect::<Vec<_>>();
        let element = isomorphism.from_slot_values(expected.iter().map(|a| slot_ring.clone_el(a)));
        let actual = isomorphism.get_slot_values(&element);
        for (expected, actual) in expected.iter().zip(actual) {
            assert_el_eq!(slot_ring, expected, actual);
        }
    }

    let (ring, hypercube) = test_ring3();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
    assert_eq!(8, isomorphism.slot_count());
    for _ in 0..10 {
        let slot_ring = isomorphism.slot_ring();
        let expected = (0..isomorphism.slot_count()).map(|_| slot_ring.random_element(|| rng.rand_u64())).collect::<Vec<_>>();
        let element = isomorphism.from_slot_values(expected.iter().map(|a| slot_ring.clone_el(a)));
        let actual = isomorphism.get_slot_values(&element);
        for (expected, actual) in expected.iter().zip(actual) {
            assert_el_eq!(slot_ring, expected, actual);
        }
    }
}

#[test]
fn test_hypercube_isomorphism_is_isomorphic() {
    let mut rng = oorandom::Rand64::new(1);

    let (ring, hypercube) = test_ring1();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
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

    let (ring, hypercube) = test_ring2();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
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

    let (ring, hypercube) = test_ring3();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
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

#[test]
fn test_hypercube_isomorphism_rotation() {
    let mut rng = oorandom::Rand64::new(1);

    let (ring, hypercube) = test_ring1();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
    let ring = isomorphism.ring();
    let hypercube = isomorphism.hypercube();
    for _ in 0..10 {
        let slot_ring = isomorphism.slot_ring();
        let a = slot_ring.random_element(|| rng.rand_u64());

        let mut input = (0..isomorphism.slot_count()).map(|_| slot_ring.zero()).collect::<Vec<_>>();
        input[0] = slot_ring.clone_el(&a);

        let mut expected = (0..isomorphism.slot_count()).map(|_| slot_ring.zero()).collect::<Vec<_>>();
        expected[hypercube.m(0) - 1] = slot_ring.clone_el(&a);

        let actual = ring.apply_galois_action(
            &isomorphism.from_slot_values(input.into_iter()),
            hypercube.galois_group().pow(hypercube.g(0), hypercube.m(0) as i64 - 1)
        );
        let actual = isomorphism.get_slot_values(&actual);
        for (expected, actual) in expected.iter().zip(actual) {
            assert_el_eq!(slot_ring, expected, actual);
        }
    }

    let (ring, hypercube) = test_ring2();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
    let ring = isomorphism.ring();
    let hypercube = isomorphism.hypercube();
    for _ in 0..10 {
        let slot_ring = isomorphism.slot_ring();
        let a = slot_ring.random_element(|| rng.rand_u64());
        
        let mut input = (0..isomorphism.slot_count()).map(|_| slot_ring.zero()).collect::<Vec<_>>();
        input[0] = slot_ring.clone_el(&a);

        let mut expected = (0..isomorphism.slot_count()).map(|_| slot_ring.zero()).collect::<Vec<_>>();
        expected[(hypercube.m(0) - 1) * hypercube.m(1)] = slot_ring.clone_el(&a);

        let actual = ring.apply_galois_action(
            &isomorphism.from_slot_values(input.into_iter()),
            hypercube.galois_group().pow(hypercube.g(0), hypercube.m(0) as i64 - 1)
        );
        let actual = isomorphism.get_slot_values(&actual).collect::<Vec<_>>();
        for (expected, actual) in expected.iter().zip(actual.iter()) {
            assert_el_eq!(slot_ring, expected, actual);
        }
    }

    let (ring, hypercube) = test_ring3();
    let isomorphism = HypercubeIsomorphism::new::<true>(ring, hypercube);
    let ring = isomorphism.ring();
    let hypercube = isomorphism.hypercube();
    for _ in 0..10 {
        let slot_ring = isomorphism.slot_ring();
        let a = slot_ring.random_element(|| rng.rand_u64());
        
        let mut input = (0..isomorphism.slot_count()).map(|_| slot_ring.zero()).collect::<Vec<_>>();
        input[0] = slot_ring.clone_el(&a);

        let mut expected = (0..isomorphism.slot_count()).map(|_| slot_ring.zero()).collect::<Vec<_>>();
        expected[(hypercube.m(0) - 1) * hypercube.m(1)] = slot_ring.clone_el(&a);

        let actual = ring.apply_galois_action(
            &isomorphism.from_slot_values(input.into_iter()),
            hypercube.galois_group().pow(hypercube.g(0), hypercube.m(0) as i64 - 1)
        );
        let actual = isomorphism.get_slot_values(&actual);
        for (expected, actual) in expected.iter().zip(actual) {
            assert_el_eq!(slot_ring, expected, actual);
        }
    }
}

#[test]
#[ignore]
fn time_from_slot_values_large() {
    use tracing_subscriber::prelude::*;
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    tracing_subscriber::registry().with(chrome_layer).init();

    let mut rng = oorandom::Rand64::new(1);

    let allocator = feanor_mempool::AllocRc(Rc::new(feanor_mempool::dynsize::DynLayoutMempool::<Global>::new(Alignment::of::<u64>())));
    let ring = RingValue::from(NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(337, 127), Zn::new(65536)).into().with_allocator(allocator));
    let galois_group = CyclotomicGaloisGroup::new(337 * 127);
    let hypercube = HypercubeStructure::new(
        galois_group,
        galois_group.from_representative(2),
        21,
        vec![16, 126],
        vec![galois_group.from_representative(37085), galois_group.from_representative(25276)]
    );
    let H = HypercubeIsomorphism::new::<true>(ring, hypercube);
    let slot_ring = H.slot_ring();

    let value = log_time::<_, _, true, _>("from_slot_values", |[]| {
        H.from_slot_values((0..H.slot_count()).map(|_| slot_ring.random_element(|| rng.rand_u64())))
    });
    std::hint::black_box(value);
}

#[test]
fn test_serialization() {

    fn test_with_test_ring<R>((ring, hypercube_structure): (R, HypercubeStructure))
        where R: RingStore,
            R::Type: CyclotomicRing,
            BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
            AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
    {
        let hypercube = HypercubeIsomorphism::new::<false>(&ring, hypercube_structure);
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
}