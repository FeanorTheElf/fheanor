use std::marker::PhantomData;
use std::alloc::Global;

use feanor_math::algorithms::linsolve::LinSolveRing;
use feanor_math::homomorphism::*;
use feanor_math::algorithms::convolution::STANDARD_CONVOLUTION;
use feanor_math::integer::BigIntRingBase;
use feanor_math::primitive_int::StaticRingBase;
use feanor_math::ring::*;
use feanor_math::rings::field::AsFieldBase;
use feanor_math::rings::local::AsLocalPIR;
use feanor_math::rings::poly::PolyRing;
use feanor_math::rings::zn::{FromModulusCreateableZnRing, ZnReductionMap, ZnRing};
use feanor_math::seq::{VectorFn, VectorView};
use feanor_math::serialization::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::poly::dense_poly::*;
use serde::de::DeserializeSeed;
use serde::{Deserialize, Serialize};

use crate::{cyclotomic::*, ZZi64};
use crate::impl_deserialize_seed_for_dependent_struct;
use crate::serialization_helper::DeserializeSeedDependentTuple;

use super::isomorphism::{BaseRing, DecoratedBaseRing, HypercubeIsomorphism};
use super::structure::{HypercubeStructure, HypercubeTypeData};

#[derive(Serialize)]
#[serde(rename = "HypercubeStructureData")]
struct SerializableHypercubeStructureData<'a, G: Serialize> {
    p: SerializableCyclotomicGaloisGroupEl<'a>,
    d: usize,
    ls: &'a [usize],
    gs: G,
    choice: &'a HypercubeTypeData
}

impl Serialize for HypercubeStructure {

    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        SerializableNewtype::new("HypercubeStructure", (&self.galois_group, SerializableHypercubeStructureData {
            choice: &self.choice,
            d: self.d,
            p: SerializableCyclotomicGaloisGroupEl::new(&self.galois_group, self.p),
            ls: &self.ls,
            gs: SerializableSeq::new(self.gs.as_fn().map_fn(|g| SerializableCyclotomicGaloisGroupEl::new(&self.galois_group, *g)))
        })).serialize(serializer)
    }
}

struct DeserializeSeedHypercubeStructureData {
    galois_group: CyclotomicGaloisGroup
}

fn derive_single_galois_group_deserializer<'a>(deserializer: &'a DeserializeSeedHypercubeStructureData) -> DeserializeSeedCyclotomicGaloisGroupEl<'a> {
    DeserializeSeedCyclotomicGaloisGroupEl::new(&deserializer.galois_group)
}

fn derive_multiple_galois_group_deserializer<'de, 'a>(deserializer: &'a DeserializeSeedHypercubeStructureData) -> impl use<'a, 'de> + DeserializeSeed<'de, Value = Vec<CyclotomicGaloisGroupEl>> {
    DeserializeSeedSeq::new(
        std::iter::repeat(DeserializeSeedCyclotomicGaloisGroupEl::new(&deserializer.galois_group)),
        Vec::new(),
        |mut current, next| { current.push(next); current }
    )
}

impl_deserialize_seed_for_dependent_struct!{
    pub struct HypercubeStructureData<'de> using DeserializeSeedHypercubeStructureData {
        p: CyclotomicGaloisGroupEl: derive_single_galois_group_deserializer,
        d: usize: |_| PhantomData,
        ls: Vec<usize>: |_| PhantomData,
        gs: Vec<CyclotomicGaloisGroupEl>: derive_multiple_galois_group_deserializer,
        choice: HypercubeTypeData: |_| PhantomData
    }
}

impl<'de> Deserialize<'de> for HypercubeStructure {

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de>
    {
        let mut deserialized_galois_group = None;
        DeserializeSeedNewtype::new("HypercubeStructure", DeserializeSeedDependentTuple::new(
            PhantomData::<CyclotomicGaloisGroup>,
            |galois_group| {
                deserialized_galois_group = Some(galois_group);
                DeserializeSeedHypercubeStructureData { galois_group }
            }
        )).deserialize(deserializer).map(|data| {
            let mut result = HypercubeStructure::new(deserialized_galois_group.take().unwrap(), data.p, data.d, data.ls, data.gs);
            result.choice = data.choice;
            return result;
        })
    }
}

#[derive(Serialize)]
#[serde(rename = "HypercubeIsomorphismData", bound = "")]
struct SerializableHypercubeIsomorphismData<'a, R>
    where R: RingStore,
        R::Type: PolyRing + SerializableElementRing
{
    p: i64,
    e: usize,
    m: usize,
    hypercube_structure: &'a HypercubeStructure,
    slot_ring_moduli: Vec<SerializeOwnedWithRing<R>>
}

///
/// Wrapper around a reference to a [`HypercubeIsomorphism`] that
/// can be used for serialization, without including the ring.
/// 
/// This can be deserialized using [`DeserializeSeedHypercubeIsomorphismWithoutRing`]
/// if the ring is provided during deserialization time.
/// 
pub struct SerializableHypercubeIsomorphismWithoutRing<'a, R>
    where R: RingStore,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    hypercube_isomorphism: &'a HypercubeIsomorphism<R>
}

impl<'a, R> SerializableHypercubeIsomorphismWithoutRing<'a, R>
    where R: RingStore,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    pub fn new(hypercube_isomorphism: &'a HypercubeIsomorphism<R>) -> Self {
        Self { hypercube_isomorphism }
    }
}

impl<'a, R> Serialize for SerializableHypercubeIsomorphismWithoutRing<'a, R>
    where R: RingStore,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        let decorated_base_ring: DecoratedBaseRing<R> = AsLocalPIR::from_zn(RingValue::from(self.hypercube_isomorphism.ring().base_ring().get_ring().clone())).unwrap();
        let ZpeX = DensePolyRing::new_with(decorated_base_ring, "X", Global, STANDARD_CONVOLUTION);
        let hom = ZnReductionMap::new(self.hypercube_isomorphism.slot_ring().base_ring(), ZpeX.base_ring()).unwrap();
        SerializableHypercubeIsomorphismData {
            p: self.hypercube_isomorphism.p(),
            e: self.hypercube_isomorphism.e(),
            m: self.hypercube_isomorphism.hypercube().m(),
            hypercube_structure: self.hypercube_isomorphism.hypercube(),
            slot_ring_moduli: (0..self.hypercube_isomorphism.slot_count()).map(|i| 
                SerializeOwnedWithRing::new(self.hypercube_isomorphism.slot_ring_at(i).generating_poly(&ZpeX, &hom), &ZpeX)
            ).collect()
        }.serialize(serializer)
    }
}
struct DeserializeSeedHypercubeIsomorphismData<R>
    where R: RingStore,
        R::Type: PolyRing + SerializableElementRing
{
    poly_ring: R
}

fn derive_multiple_poly_deserializer<'de, 'a, R>(deserializer: &'a DeserializeSeedHypercubeIsomorphismData<R>) -> impl use <'a, 'de, R> + DeserializeSeed<'de, Value = Vec<El<R>>>
    where R: RingStore,
        R::Type: PolyRing + SerializableElementRing
{
    DeserializeSeedSeq::new(
        std::iter::repeat(DeserializeWithRing::new(&deserializer.poly_ring)),
        Vec::new(),
        |mut current, next| { current.push(next); current }
    )
}

impl_deserialize_seed_for_dependent_struct!{
    <{'de, R}> pub struct HypercubeIsomorphismData<{'de, R}> using DeserializeSeedHypercubeIsomorphismData<R> {
        p: i64: |_| PhantomData,
        e: usize: |_| PhantomData,
        m: usize: |_| PhantomData,
        hypercube_structure: HypercubeStructure: |_| PhantomData,
        slot_ring_moduli: Vec<El<R>>: derive_multiple_poly_deserializer
    } where R: RingStore, R::Type: PolyRing + SerializableElementRing
}

///
/// A [`DeserializeSeed`] to deserialize a [`HypercubeIsomorphism`]
/// that has been serialized without the ring. Hence, for deserialization,
/// it is necessary that the ring is provided again. Therefore, we must
/// use a [`DeserializeSeed`] wrapping the ring, i.e. this struct.
/// 
pub struct DeserializeSeedHypercubeIsomorphismWithoutRing<R>
    where R: RingStore,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    ring: R
}

impl<R> DeserializeSeedHypercubeIsomorphismWithoutRing<R>
    where R: RingStore,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    pub fn new(ring: R) -> Self {
        Self { ring }
    }
}

impl<'de, R> DeserializeSeed<'de> for DeserializeSeedHypercubeIsomorphismWithoutRing<R>
    where R: RingStore,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    type Value = HypercubeIsomorphism<R>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: serde::Deserializer<'de>
    {
        let decorated_base_ring: DecoratedBaseRing<R> = AsLocalPIR::from_zn(RingValue::from(self.ring.base_ring().get_ring().clone())).unwrap();
        let ZpeX = DensePolyRing::new_with(decorated_base_ring, "X", Global, STANDARD_CONVOLUTION);
        let deserialized = DeserializeSeedHypercubeIsomorphismData { poly_ring: &ZpeX }.deserialize(deserializer)?;
        assert_eq!(self.ring.m(), deserialized.m);
        assert_eq!(self.ring.characteristic(ZZi64).unwrap(), ZZi64.pow(deserialized.p, deserialized.e));
        let hypercube_structure = deserialized.hypercube_structure;
        let slot_ring_moduli = deserialized.slot_ring_moduli;
        let result = HypercubeIsomorphism::create::<false>(
            self.ring,
            hypercube_structure,
            ZpeX,
            slot_ring_moduli
        );
        return Ok(result);
    }
}

impl<R> Serialize for HypercubeIsomorphism<R>
    where R: RingStore + Serialize,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        SerializableNewtype::new("HypercubeIsomorphism", (self.ring(), SerializableHypercubeIsomorphismWithoutRing::new(self))).serialize(serializer)
    }
}

impl<'de, R> Deserialize<'de> for HypercubeIsomorphism<R>
    where R: RingStore + Deserialize<'de>,
        R::Type: CyclotomicRing,
        BaseRing<R>: Clone + ZnRing + CanHomFrom<StaticRingBase<i64>> + CanHomFrom<BigIntRingBase> + LinSolveRing + FromModulusCreateableZnRing + SerializableElementRing,
        AsFieldBase<DecoratedBaseRing<R>>: CanIsoFromTo<<DecoratedBaseRing<R> as RingStore>::Type> + SelfIso
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de>
    {
        DeserializeSeedNewtype::new("HypercubeIsomorphism", DeserializeSeedDependentTuple::new(
            PhantomData::<R>,
            |ring| DeserializeSeedHypercubeIsomorphismWithoutRing::new(ring)
        )).deserialize(deserializer)
    }
}
