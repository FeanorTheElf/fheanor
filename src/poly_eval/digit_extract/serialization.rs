use std::marker::PhantomData;

use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::integer::BigIntRing;
use feanor_math::ring::*;
use feanor_math::serialization::*;
use feanor_serde::impl_deserialize_seed_for_dependent_struct;
use feanor_serde::seq::DeserializeSeedSeq;
use serde::de::DeserializeSeed;
use serde::{Deserializer, Serialize};

use crate::cache::{DeserializeSeedDeserializableWithData, SerializeDeserializeWith, SerializeSerializableWithData};
use crate::circuit::PlaintextCircuit;
use crate::number_ring::galois::CyclotomicGaloisGroup;
use crate::poly_eval::digit_extract::{DigitExtract, DigitExtractionCircuit};

#[derive(Serialize)]
#[serde(rename = "DigitExtractCircuitData", bound = "")]
pub(super) struct SerializableDigitExtractCircuit<'a, D, R>
where
    R: ?Sized + SerializableElementRing,
    PlaintextCircuit<R>: SerializeDeserializeWith<D>,
{
    pub(super) circuit: SerializeSerializableWithData<'a, D, PlaintextCircuit<R>>,
    pub(super) global_mod_exp: usize,
    pub(super) extracted_digit_mod_exp: &'a [usize],
    pub(super) ignore: PhantomData<()>,
}

#[derive(Serialize)]
#[serde(rename = "DigitExtractData", bound = "")]
pub(super) struct SerializableDigitExtract<'a, D, R>
where
    R: ?Sized + SerializableElementRing,
    PlaintextCircuit<R>: SerializeDeserializeWith<D>,
{
    pub(super) extraction_circuits: Vec<SerializableDigitExtractCircuit<'a, D, R>>,
    pub(super) v: usize,
    pub(super) e: usize,
    pub(super) p: SerializeWithRing<'a, BigIntRing>,
    pub(super) ignore: PhantomData<()>,
}

#[derive(Clone, Copy)]
pub(super) struct DeserializeSeedDigitExtract<'a, R>
where
    R: RingStore,
    R::Type: SerializableElementRing,
{
    pub(super) rings: &'a [R],
    pub(super) galois_group: Option<&'a Subgroup<CyclotomicGaloisGroup>>,
}

impl<'a, 'de, R> DeserializeSeed<'de> for DeserializeSeedDigitExtract<'a, R>
where
    R: RingStore,
    R::Type: SerializableElementRing,
{
    type Value = DigitExtract<R::Type>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct DeserializeSeedDigitExtractCircuitData<D, R: ?Sized> {
            data: D,
            ring: PhantomData<R>,
        }

        impl_deserialize_seed_for_dependent_struct! {
            <{'de, Data, R}> pub struct DigitExtractCircuitData<{'de, R, Data}> using DeserializeSeedDigitExtractCircuitData<Data, R> {
                circuit: PlaintextCircuit<R>: |deserialize_seed: &DeserializeSeedDigitExtractCircuitData<Data, R>| DeserializeSeedDeserializableWithData::new(deserialize_seed.data.clone()),
                global_mod_exp: usize: |_| PhantomData::<usize>,
                extracted_digit_mod_exp: Vec<usize>: |_| PhantomData::<Vec<usize>>,
                ignore: PhantomData<Data>: |_| PhantomData::<PhantomData<Data>>
            } where R: ?Sized + SerializableElementRing,
                PlaintextCircuit<R>: SerializeDeserializeWith<Data>,
                Data: Clone
        }

        struct DeserializeSeedDigitExtractData<D, R: ?Sized> {
            circuit_deserialize_data: Vec<D>,
            ring: PhantomData<R>,
        }

        fn derive_circuit_deserializer<'de, 'a, D, R>(
            deserialize_seed: &'a DeserializeSeedDigitExtractData<D, R>,
        ) -> impl use<'a, 'de, D, R> + DeserializeSeed<'de, Value = Vec<DigitExtractionCircuit<R>>>
        where
            R: ?Sized + SerializableElementRing,
            PlaintextCircuit<R>: SerializeDeserializeWith<D>,
            D: Clone,
        {
            DeserializeSeedSeq::new(
                deserialize_seed
                    .circuit_deserialize_data
                    .iter()
                    .chain([deserialize_seed.circuit_deserialize_data.last().unwrap()])
                    .map(|data| DeserializeSeedDigitExtractCircuitData {
                        data: data.clone(),
                        ring: PhantomData,
                    }),
                Vec::new(),
                |mut current, next| {
                    current.push(DigitExtractionCircuit {
                        circuit: next.circuit,
                        global_mod_exp: next.global_mod_exp,
                        extracted_digit_mod_exp: next.extracted_digit_mod_exp,
                    });
                    current
                },
            )
        }

        impl_deserialize_seed_for_dependent_struct! {
            <{'de, R, Data}> pub struct DigitExtractData<{'de, R, Data}> using DeserializeSeedDigitExtractData<Data, R> {
                extraction_circuits: Vec<DigitExtractionCircuit<R>>: derive_circuit_deserializer,
                v: usize: |_| PhantomData::<usize>,
                e: usize: |_| PhantomData::<usize>,
                p: El<BigIntRing>: |_| DeserializeWithRing::new(BigIntRing::RING),
                ignore: PhantomData<Data>: |_| PhantomData::<PhantomData<Data>>
            } where R: ?Sized + SerializableElementRing,
                PlaintextCircuit<R>: SerializeDeserializeWith<Data>,
                Data: Clone
        }

        if let Some(galois_group) = self.galois_group {
            let result = DeserializeSeedDigitExtractData {
                ring: PhantomData,
                circuit_deserialize_data: self.rings.iter().skip(1).map(|ring| (ring, galois_group)).collect(),
            }
            .deserialize(deserializer)?;
            return Ok(DigitExtract::new_with_circuits(
                self.rings.last().unwrap(),
                result.p,
                result.e - result.v,
                result.v,
                result.extraction_circuits,
            ));
        } else {
            let result = DeserializeSeedDigitExtractData {
                ring: PhantomData,
                circuit_deserialize_data: self.rings.iter().skip(1).map(|ring| (ring,)).collect(),
            }
            .deserialize(deserializer)?;
            return Ok(DigitExtract::new_with_circuits(
                self.rings.last().unwrap(),
                result.p,
                result.e - result.v,
                result.v,
                result.extraction_circuits,
            ));
        }
    }
}
