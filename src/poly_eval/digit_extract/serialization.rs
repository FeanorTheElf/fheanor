
use std::marker::PhantomData;

use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::integer::BigIntRing;
use feanor_math::ring::{El, RingStore};
use feanor_math::serialization::{DeserializeWithRing, SerializableElementRing, SerializeOwnedWithRing};
use feanor_serde::dependent_tuple::DeserializeSeedDependentTuple;
use feanor_serde::impl_deserialize_seed_for_dependent_struct;
use feanor_serde::map::DeserializeSeedMapped;
use feanor_serde::seq::DeserializeSeedSeq;
use serde::{Deserializer, Serialize};
use serde::de::DeserializeSeed;
use crate::cache::SerializeDeserializeWith;
use crate::circuit::PlaintextCircuit;
use crate::circuit::serialization::{DeserializeSeedPlaintextCircuit, SerializablePlaintextCircuit};
use crate::number_ring::galois::CyclotomicGaloisGroup;
use crate::poly_eval::digit_extract::DigitExtract;

#[derive(Serialize)]
#[serde(rename = "DigitExtractData", bound = "")]
pub struct SerializableDigitExtract<'a, R>
    where R: RingStore + Copy,
        R::Type: SerializableElementRing
{
    pub(super) extraction_circuits: Vec<(&'a Vec<usize>, SerializablePlaintextCircuit<'a, R>)>,
    pub(super) v: usize,
    pub(super) e: usize,
    pub(super) p: SerializeOwnedWithRing<BigIntRing>
}

#[derive(Clone, Copy)]
pub struct DeserializeSeedDigitExtract<'a, R>
    where R: RingStore + Copy,
        R::Type: SerializableElementRing
{
    pub(super) ring: R,
    pub(super) galois_group: Option<&'a Subgroup<CyclotomicGaloisGroup>>
}

impl<'a, 'de, R> DeserializeSeed<'de> for DeserializeSeedDigitExtract<'a, R>
    where R: RingStore + Copy,
        R::Type: SerializableElementRing
{
    type Value = DigitExtract<R::Type>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
    {
        struct DeserializeSeedDigitExtractData<'a, R>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            circuit_deserializer: DeserializeSeedPlaintextCircuit<'a, R>
        }

        fn derive_circuit_deserializer<'de, 'a, 'b, R>(deserializer: &'b DeserializeSeedDigitExtractData<'a, R>) -> impl use <'a, 'b, 'de, R> + DeserializeSeed<'de, Value = Vec<(Vec<usize>, PlaintextCircuit<R::Type>)>>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            DeserializeSeedSeq::new(
                (0..).map(|_| DeserializeSeedDependentTuple::new(PhantomData::<Vec<usize>>, |required_digits| DeserializeSeedMapped::new(
                    deserializer.circuit_deserializer,
                    move |circuit| (required_digits, circuit)
                ))),
                Vec::new(),
                |mut current, next| { current.push(next); current }
            )
        }

        impl_deserialize_seed_for_dependent_struct!{
            <{'de, 'a, R}> pub struct DigitExtractData<{'de, R}> using DeserializeSeedDigitExtractData<'a, R> {
                extraction_circuits: Vec<(Vec<usize>, PlaintextCircuit<R::Type>)>: derive_circuit_deserializer,
                v: usize: |_| PhantomData::<usize>,
                e: usize: |_| PhantomData::<usize>,
                p: El<BigIntRing>: |_| DeserializeWithRing::new(BigIntRing::RING)
            } where R: RingStore + Copy,
                R::Type: SerializableElementRing
        }

        let result_data = if let Some(galois_group) = self.galois_group {
            DeserializeSeedDigitExtractData {
                circuit_deserializer: PlaintextCircuit::deserialize_with(&(self.ring, galois_group))
            }.deserialize(deserializer)?
        } else {
            DeserializeSeedDigitExtractData {
                circuit_deserializer: PlaintextCircuit::deserialize_with(&(self.ring, ))
            }.deserialize(deserializer)?
        };

        return Ok(DigitExtract::new_with_circuits(result_data.p, result_data.e, result_data.e - result_data.v, self.ring, result_data.extraction_circuits));
    }
}