use std::alloc::Global;
use std::marker::PhantomData;

use feanor_math::group::*;
use feanor_math::ring::*;
use feanor_math::rings::local::AsLocalPIR;
use feanor_math::rings::poly::PolyRing;
use feanor_math::rings::zn::*;
use feanor_math::serialization::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::poly::dense_poly::*;
use feanor_serde::dependent_tuple::DeserializeSeedDependentTuple;
use feanor_serde::newtype_struct::*;
use feanor_serde::seq::*;
use serde::de::DeserializeSeed;
use serde::{Deserialize, Serialize};
use feanor_serde::impl_deserialize_seed_for_dependent_struct;
use tracing::instrument;

use crate::number_ring::galois::*;
use crate::number_ring::hypercube::isomorphism::create_convolution;
use crate::number_ring::*;
use crate::{NiceZn, ZZbig};

use super::isomorphism::HypercubeIsomorphism;
use super::structure::{HypercubeStructure, HypercubeTypeData};

impl Serialize for HypercubeStructure {

    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        #[derive(Serialize)]
        #[serde(rename = "HypercubeStructureData")]
        struct SerializableHypercubeStructureData<'a, G: Serialize> {
            frobenius: SerializeWithGroup<'a, &'a CyclotomicGaloisGroup>,
            d: usize,
            ls: &'a [usize],
            gs: G,
            choice: &'a HypercubeTypeData
        }

        SerializableNewtypeStruct::new("HypercubeStructure", (&self.galois_group, SerializableHypercubeStructureData {
            choice: &self.choice,
            d: self.d,
            frobenius: SerializeWithGroup::new(self.p(), self.galois_group().parent()),
            ls: &self.ls,
            gs: SerializableSeq::new_with_len(self.gs.iter().map(|g| SerializeWithGroup::new(g, self.galois_group().parent())), self.gs.len())
        })).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for HypercubeStructure {

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de>
    {
        struct DeserializeSeedHypercubeStructureData {
            galois_group: CyclotomicGaloisGroup
        }

        fn derive_single_galois_group_deserializer<'a>(deserializer: &'a DeserializeSeedHypercubeStructureData) -> DeserializeWithGroup<&'a CyclotomicGaloisGroup> {
            DeserializeWithGroup::new(&deserializer.galois_group)
        }

        fn derive_multiple_galois_group_deserializer<'de, 'a>(deserializer: &'a DeserializeSeedHypercubeStructureData) -> impl use<'a, 'de> + DeserializeSeed<'de, Value = Vec<GaloisGroupEl>> {
            DeserializeSeedSeq::new(
                std::iter::repeat(DeserializeWithGroup::new(&deserializer.galois_group)),
                Vec::new(),
                |mut current, next| { current.push(next); current }
            )
        }

        impl_deserialize_seed_for_dependent_struct!{
            pub struct HypercubeStructureData<'de> using DeserializeSeedHypercubeStructureData {
                frobenius: GaloisGroupEl: derive_single_galois_group_deserializer,
                d: usize: |_| PhantomData,
                ls: Vec<usize>: |_| PhantomData,
                gs: Vec<GaloisGroupEl>: derive_multiple_galois_group_deserializer,
                choice: HypercubeTypeData: |_| PhantomData
            }
        }

        let mut deserialized_galois_group = None;
        Ok(DeserializeSeedNewtypeStruct::new("HypercubeStructure", DeserializeSeedDependentTuple::new(
            PhantomData::<Subgroup<CyclotomicGaloisGroup>>,
            |galois_group| {
                let parent = galois_group.parent().clone();
                deserialized_galois_group = Some(galois_group);
                DeserializeSeedHypercubeStructureData { galois_group: parent }
            }
        )).deserialize(deserializer).map(|data| {
            let mut result = HypercubeStructure::new(deserialized_galois_group.take().unwrap(), data.frobenius, data.d, data.ls, data.gs);
            result.choice = data.choice;
            return result;
        }).unwrap())
    }
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
        R::Type: NumberRingQuotient,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn + SerializableElementRing
{
    hypercube_isomorphism: &'a HypercubeIsomorphism<R>
}

impl<'a, R> SerializableHypercubeIsomorphismWithoutRing<'a, R>
    where R: RingStore,
        R::Type: NumberRingQuotient,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn + SerializableElementRing
{
    pub fn new(hypercube_isomorphism: &'a HypercubeIsomorphism<R>) -> Self {
        Self { hypercube_isomorphism }
    }
}

impl<'a, R> Serialize for SerializableHypercubeIsomorphismWithoutRing<'a, R>
    where R: RingStore,
        R::Type: NumberRingQuotient,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn + SerializableElementRing
{
    #[instrument(skip_all)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        #[derive(Serialize)]
        #[serde(rename = "HypercubeIsomorphismData", bound = "")]
        struct SerializableHypercubeIsomorphismData<'a, R>
            where R: RingStore,
                R::Type: PolyRing + SerializableElementRing
        {
            characteristic: SerializeOwnedWithRing<BigIntRing>,
            hypercube_structure: &'a HypercubeStructure,
            slot_ring_moduli: Vec<SerializeOwnedWithRing<R>>
        }

        let decorated_base_ring = AsLocalPIR::from_zn(RingValue::from(self.hypercube_isomorphism.ring().base_ring().get_ring().clone())).unwrap();
        let ZpeX = DensePolyRing::new(decorated_base_ring, "X");
        let hom = ZnReductionMap::new(self.hypercube_isomorphism.slot_ring().base_ring(), ZpeX.base_ring()).unwrap();
        SerializableHypercubeIsomorphismData {
            characteristic: SerializeOwnedWithRing::new(self.hypercube_isomorphism.ring().characteristic(ZZbig).unwrap(), ZZbig),
            hypercube_structure: self.hypercube_isomorphism.hypercube(),
            slot_ring_moduli: (0..self.hypercube_isomorphism.slot_count()).map(|i| 
                SerializeOwnedWithRing::new(self.hypercube_isomorphism.slot_ring_at(i).generating_poly(&ZpeX, &hom), &ZpeX)
            ).collect()
        }.serialize(serializer)
    }
}

///
/// A [`DeserializeSeed`] to deserialize a [`HypercubeIsomorphism`]
/// that has been serialized without the ring. Hence, for deserialization,
/// it is necessary that the ring is provided again. Therefore, we must
/// use a [`DeserializeSeed`] wrapping the ring, i.e. this struct.
/// 
pub struct DeserializeSeedHypercubeIsomorphismWithoutRing<R>
    where R: RingStore,
        R::Type: NumberRingQuotient,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn + SerializableElementRing
{
    ring: R
}

impl<R> DeserializeSeedHypercubeIsomorphismWithoutRing<R>
    where R: RingStore,
        R::Type: NumberRingQuotient,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn + SerializableElementRing
{
    pub fn new(ring: R) -> Self {
        Self { ring }
    }
}

impl<'de, R> DeserializeSeed<'de> for DeserializeSeedHypercubeIsomorphismWithoutRing<R>
    where R: RingStore,
        R::Type: NumberRingQuotient,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn + SerializableElementRing
{
    type Value = HypercubeIsomorphism<R>;

    #[instrument(skip_all)]
    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: serde::Deserializer<'de>
    {
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
                characteristic: El<BigIntRing>: |_| DeserializeWithRing::new(ZZbig),
                hypercube_structure: HypercubeStructure: |_| PhantomData,
                slot_ring_moduli: Vec<El<R>>: derive_multiple_poly_deserializer
            } where R: RingStore, R::Type: PolyRing + SerializableElementRing
        }

        let Zpe = AsLocalPIR::from_zn(RingValue::from(self.ring.base_ring().get_ring().clone())).unwrap();
        let convolution = create_convolution(self.ring.rank(), Zpe.integer_ring().abs_log2_ceil(Zpe.modulus()).unwrap());
        let ZpeX = DensePolyRing::new_with_convolution(Zpe, "X", Global, convolution);
        let deserialized = DeserializeSeedHypercubeIsomorphismData { poly_ring: &ZpeX }.deserialize(deserializer)?;
        assert!(self.ring.acting_galois_group().get_group() == deserialized.hypercube_structure.galois_group().get_group(), "ring mismatch");
        assert!(ZZbig.eq_el(&self.ring.characteristic(ZZbig).unwrap(), &deserialized.characteristic), "ring mismatch");
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
        R::Type: NumberRingQuotient,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn + SerializableElementRing
{
    #[instrument(skip_all)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        SerializableNewtypeStruct::new("HypercubeIsomorphism", (self.ring(), SerializableHypercubeIsomorphismWithoutRing::new(self))).serialize(serializer)
    }
}

impl<'de, R> Deserialize<'de> for HypercubeIsomorphism<R>
    where R: RingStore + Deserialize<'de>,
        R::Type: NumberRingQuotient,
        <<R::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn + SerializableElementRing
{
    #[instrument(skip_all)]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de>
    {
        DeserializeSeedNewtypeStruct::new("HypercubeIsomorphism", DeserializeSeedDependentTuple::new(
            PhantomData::<R>,
            |ring| DeserializeSeedHypercubeIsomorphismWithoutRing::new(ring)
        )).deserialize(deserializer)
    }
}
