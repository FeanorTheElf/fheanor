use std::marker::PhantomData;

use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::group::{DeserializeWithGroup, SerializeWithGroup};
use feanor_math::integer::BigIntRing;
use feanor_math::ring::*;
use feanor_math::serialization::{DeserializeWithRing, SerializableElementRing, SerializeWithRing};
use serde::de::DeserializeSeed;
use serde::Serialize;
use feanor_serde::{impl_deserialize_seed_for_dependent_enum, impl_deserialize_seed_for_dependent_struct};
use feanor_serde::seq::*;
use tracing::instrument;

use crate::ZZbig;
use crate::number_ring::galois::*;

use super::{Coefficient, LinearCombination, PlaintextCircuit, PlaintextCircuitGate};

#[derive(Serialize)]
#[serde(rename = "CoefficientData", bound = "")]
enum SerializableCoefficient<'a, R>
    where R: RingStore + Copy,
        R::Type: SerializableElementRing
{
    Integer(SerializeWithRing<'a, BigIntRing>),
    Other(SerializeWithRing<'a, R>)
}

#[derive(Serialize)]
#[serde(rename = "LinearCombinationData", bound = "")]
struct SerializableLinearCombination<C: Serialize, S: Serialize> {
    constant: C,
    factors: S
}

#[derive(Serialize)]
#[serde(rename = "MulGateData", bound = "")]
struct SerializablePlaintextCircuitMulGate<L: Serialize> {
    lhs: L,
    rhs: L
}

#[derive(Serialize)]
#[serde(rename = "SquareGateData", bound = "")]
struct SerializablePlaintextCircuitSquareGate<L: Serialize> {
    val: L
}

#[derive(Serialize)]
#[serde(rename = "GalGateData", bound = "")]
struct SerializablePlaintextCircuitGalGate<L: Serialize, G: Serialize> {
    automorphisms: G,
    input: L
}

#[derive(Serialize)]
#[serde(rename = "GateData", bound = "")]
enum SerializablePlaintextCircuitGate<L: Serialize, G: Serialize> {
    Mul(SerializablePlaintextCircuitMulGate<L>),
    Gal(SerializablePlaintextCircuitGalGate<L, G>),
    Square(SerializablePlaintextCircuitSquareGate<L>)
}

#[derive(Serialize)]
#[serde(rename = "PlaintextCircuitData", bound = "")]
struct SerializablePlaintextCircuitData<G: Serialize, O: Serialize> {
    input_count: usize,
    gates: G,
    output_transforms: O
}

pub(super) struct SerializablePlaintextCircuit<'a, R>
    where R: RingStore + Copy,
        R::Type: SerializableElementRing
{
    pub(super) circuit: &'a PlaintextCircuit<R::Type>,
    pub(super) ring: R,
    pub(super) galois_group: Option<&'a Subgroup<CyclotomicGaloisGroup>>
}

impl<'a, R> Serialize for SerializablePlaintextCircuit<'a, R>
    where R: RingStore + Copy,
        R::Type: SerializableElementRing
{
    #[instrument(skip_all)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        struct Constants {
            one: El<BigIntRing>,
            neg_one: El<BigIntRing>,
            zero: El<BigIntRing>
        }
        let constants = Constants {
            neg_one: ZZbig.neg_one(),
            one: ZZbig.one(),
            zero: ZZbig.zero()
        };
        fn serialize_coefficient<'a, R>(c: &'a Coefficient<R::Type>, ring: R, constants: &'a Constants) -> SerializableCoefficient<'a, R>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            match c {
                Coefficient::Integer(x) => SerializableCoefficient::Integer(SerializeWithRing::new(x, ZZbig)),
                Coefficient::One => SerializableCoefficient::Integer(SerializeWithRing::new(&constants.one, ZZbig)),
                Coefficient::NegOne => SerializableCoefficient::Integer(SerializeWithRing::new(&constants.neg_one, ZZbig)),
                Coefficient::Zero => SerializableCoefficient::Integer(SerializeWithRing::new(&constants.zero, ZZbig)),
                Coefficient::Other(x) => SerializableCoefficient::Other(SerializeWithRing::new(x, ring))
            }
        }
        fn serialize_lin_transform<'a, R: Copy + RingStore>(t: &'a LinearCombination<R::Type>, ring: R, constants: &'a Constants) -> SerializableLinearCombination<SerializableCoefficient<'a, R>, impl use<'a, R> + Serialize>
            where R::Type: SerializableElementRing,
                R: 'a
        {
            SerializableLinearCombination {
                constant: serialize_coefficient(&t.constant, ring, constants),
                factors: SerializableSeq::new_with_len(t.factors.iter().map(move |c| serialize_coefficient(c, ring, constants)), t.factors.len())
            }
        }
        SerializablePlaintextCircuitData {
            input_count: self.circuit.input_count,
            gates: SerializableSeq::new_with_len(self.circuit.gates.iter().map(|gate| match gate {
                PlaintextCircuitGate::Mul(lhs, rhs) => SerializablePlaintextCircuitGate::Mul(SerializablePlaintextCircuitMulGate {
                    lhs: serialize_lin_transform(lhs, self.ring, &constants), 
                    rhs: serialize_lin_transform(rhs, self.ring, &constants)
                }),
                PlaintextCircuitGate::Gal(gs, val) => SerializablePlaintextCircuitGate::Gal(SerializablePlaintextCircuitGalGate {
                    automorphisms: SerializableSeq::new_with_len(gs.iter().map(|g| SerializeWithGroup::new(g, self.galois_group.unwrap().parent())), gs.len()), 
                    input: serialize_lin_transform(val, self.ring, &constants)
                }),
                PlaintextCircuitGate::Square(val) => SerializablePlaintextCircuitGate::Square(SerializablePlaintextCircuitSquareGate { 
                    val: serialize_lin_transform(val, self.ring, &constants) 
                })
            }), self.circuit.gates.len()),
            output_transforms: SerializableSeq::new_with_len(self.circuit.output_transforms.iter().map(|t| serialize_lin_transform(t, self.ring, &constants)), self.circuit.output_transforms.len())
        }.serialize(serializer)
    }
}

#[derive(Copy, Clone)]
pub(super) struct DeserializeSeedPlaintextCircuit<'a, R>
    where R: RingStore + Copy,
        R::Type: SerializableElementRing
{
    pub(super) ring: R,
    pub(super) galois_group: Option<&'a Subgroup<CyclotomicGaloisGroup>>
}

impl<'de, 'a, R> DeserializeSeed<'de> for DeserializeSeedPlaintextCircuit<'a, R>
    where R: RingStore + Copy,
        R::Type: SerializableElementRing
{
    type Value = PlaintextCircuit<R::Type>;

    #[instrument(skip_all)]
    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: serde::Deserializer<'de>
    {
        #[derive(Clone)]
        struct DeserializeSeedCoefficient<R>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            deserializer: DeserializeWithRing<R>
        }

        impl_deserialize_seed_for_dependent_enum!{
            <{'de, R}> pub enum CoefficientData<{'de, R}> using DeserializeSeedCoefficient<R> {
                Integer(El<BigIntRing>): |_: DeserializeSeedCoefficient<R>| DeserializeWithRing::new(ZZbig),
                Other(El<R>): |d: DeserializeSeedCoefficient<R>| d.deserializer
            } where R: RingStore + Copy,
                R::Type: SerializableElementRing
        }

        #[derive(Clone)]
        struct DeserializeSeedLinearCombination<R>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            deserializer: DeserializeWithRing<R>
        }

        impl_deserialize_seed_for_dependent_struct!{
            <{'de, R}> pub struct LinearCombinationData<{'de, R}> using DeserializeSeedLinearCombination<R> {
                constant: CoefficientData<'de, R>: |d: &DeserializeSeedLinearCombination<R>| DeserializeSeedCoefficient { deserializer: d.deserializer.clone() },
                factors: Vec<CoefficientData<'de, R>>: |d: &DeserializeSeedLinearCombination<R>| DeserializeSeedSeq::new(
                    std::iter::repeat(DeserializeSeedCoefficient { deserializer: d.deserializer.clone() }),
                    Vec::new(),
                    |mut current, next| { current.push(next); current }
                )
            } where R: RingStore + Copy, 
                R::Type: SerializableElementRing
        }

        #[derive(Clone)]
        struct DeserializeSeedPlaintextCircuitMulGate<R>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            deserializer: DeserializeWithRing<R>
        }

        impl_deserialize_seed_for_dependent_struct!{
            <{'de, R}> pub struct MulGateData<{'de, R}> using DeserializeSeedPlaintextCircuitMulGate<R> {
                lhs: LinearCombinationData<'de, R>: |d: &DeserializeSeedPlaintextCircuitMulGate<R>| DeserializeSeedLinearCombination { deserializer: d.deserializer.clone() },
                rhs: LinearCombinationData<'de, R>: |d: &DeserializeSeedPlaintextCircuitMulGate<R>| DeserializeSeedLinearCombination { deserializer: d.deserializer.clone() }
            } where R: RingStore + Copy, 
                R::Type: SerializableElementRing
        }

        #[derive(Clone)]
        struct DeserializeSeedPlaintextCircuitSquareGate<R: RingStore + Copy>
            where R::Type: SerializableElementRing
        {
            deserializer: DeserializeWithRing<R>
        }

        impl_deserialize_seed_for_dependent_struct!{
            <{'de, R}> pub struct SquareGateData<{'de, R}> using DeserializeSeedPlaintextCircuitSquareGate<R> {
                val: LinearCombinationData<'de, R>: |d: &DeserializeSeedPlaintextCircuitSquareGate<R>| DeserializeSeedLinearCombination { deserializer: d.deserializer.clone() }
            } where R: RingStore + Copy, R::Type: SerializableElementRing
        }

        #[derive(Clone)]
        struct DeserializeSeedPlaintextCircuitGalGate<'a, R>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            galois_group: Option<&'a Subgroup<CyclotomicGaloisGroup>>,
            deserializer: DeserializeWithRing<R>
        }

        fn derive_gal_gate_deserializer<'de, 'a, R>(d: &DeserializeSeedPlaintextCircuitGalGate<'a, R>) -> impl use<'a, 'de, R> + DeserializeSeed<'de, Value = Vec<GaloisGroupEl>>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            let galois_group: &'a Subgroup<CyclotomicGaloisGroup> = d.galois_group.expect("cannot deserialize a circuit with galois gates if no galois group was specified");
            DeserializeSeedSeq::new(
                std::iter::repeat(DeserializeWithGroup::new(galois_group.parent())),
                Vec::new(),
                |mut current, next| { assert!(galois_group.contains(&next)); current.push(next); current }
            )
        }

        impl_deserialize_seed_for_dependent_struct!{
            <{'de, 'a, R}> pub struct GalGateData<{'de, R}> using DeserializeSeedPlaintextCircuitGalGate<'a, R> {
                automorphisms: Vec<GaloisGroupEl>: derive_gal_gate_deserializer,
                input: LinearCombinationData<'de, R>: |d: &DeserializeSeedPlaintextCircuitGalGate<R>| DeserializeSeedLinearCombination { deserializer: d.deserializer.clone() }
            } where R: RingStore + Copy, 
                R::Type: SerializableElementRing
        }

        #[derive(Clone)]
        struct DeserializeSeedPlaintextCircuitGate<'a, R>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            galois_group: Option<&'a Subgroup<CyclotomicGaloisGroup>>,
            deserializer: DeserializeWithRing<R>
        }

        impl_deserialize_seed_for_dependent_enum!{
            <{'de, 'a, R}> pub enum GateData<{'de, R}> using DeserializeSeedPlaintextCircuitGate<'a, R> {
                Mul(MulGateData<'de, R>): |d: DeserializeSeedPlaintextCircuitGate<'a, R>| DeserializeSeedPlaintextCircuitMulGate { deserializer: d.deserializer },
                Gal(GalGateData<'de, R>): |d: DeserializeSeedPlaintextCircuitGate<'a, R>| DeserializeSeedPlaintextCircuitGalGate { deserializer: d.deserializer, galois_group: d.galois_group },
                Square(SquareGateData<'de, R>): |d: DeserializeSeedPlaintextCircuitGate<'a, R>| DeserializeSeedPlaintextCircuitSquareGate { deserializer: d.deserializer }
            } where R: RingStore + Copy, 
                R::Type: SerializableElementRing
        }
        struct DeserializeSeedPlaintextCircuitData<'a, R>
            where R: RingStore + Copy,
                R::Type: SerializableElementRing
        {
            galois_group: Option<&'a Subgroup<CyclotomicGaloisGroup>>,
            deserializer: DeserializeWithRing<R>
        }

        impl_deserialize_seed_for_dependent_struct!{
            <{'de, 'a, R}> pub struct PlaintextCircuitData<{'de, R}> using DeserializeSeedPlaintextCircuitData<'a, R> {
                input_count: usize: |_| PhantomData,
                gates: Vec<GateData<'de, R>>: |d: &DeserializeSeedPlaintextCircuitData<'a, R>| DeserializeSeedSeq::new(
                    std::iter::repeat(DeserializeSeedPlaintextCircuitGate { deserializer: d.deserializer.clone(), galois_group: d.galois_group }),
                    Vec::new(),
                    |mut current, next| { current.push(next); current }
                ),
                output_transforms: Vec<LinearCombinationData<'de, R>>: |d: &DeserializeSeedPlaintextCircuitData<'a, R>| DeserializeSeedSeq::new(
                    std::iter::repeat(DeserializeSeedLinearCombination { deserializer: d.deserializer.clone() }),
                    Vec::new(),
                    |mut current, next| { current.push(next); current }
                )
            } where R: RingStore + Copy, 
                R::Type: SerializableElementRing
        }


        let convert_coefficient = |c: CoefficientData<_>| match c {
            CoefficientData::Integer((x, _)) if ZZbig.is_zero(&x) => Coefficient::Zero,
            CoefficientData::Integer((x, _)) if ZZbig.is_one(&x) => Coefficient::One,
            CoefficientData::Integer((x, _)) if ZZbig.is_neg_one(&x) => Coefficient::NegOne,
            CoefficientData::Integer((x, _)) => Coefficient::Integer(x),
            CoefficientData::Other((x, _)) => Coefficient::Other(x)
        };
        let convert_transform = |t: LinearCombinationData<_>| LinearCombination {
            constant: convert_coefficient(t.constant),
            factors: t.factors.into_iter().map(convert_coefficient).collect()
        };
        let res = DeserializeSeedPlaintextCircuitData {
            deserializer: DeserializeWithRing::new(self.ring),
            galois_group: self.galois_group
        }.deserialize(deserializer)?;
        let result = PlaintextCircuit {
            gates: res.gates.into_iter().map(|gate| match gate {
                GateData::Gal((gate, _)) => PlaintextCircuitGate::Gal(gate.automorphisms, convert_transform(gate.input)),
                GateData::Mul((gate, _)) => PlaintextCircuitGate::Mul(convert_transform(gate.lhs), convert_transform(gate.rhs)),
                GateData::Square((gate, _)) => PlaintextCircuitGate::Square(convert_transform(gate.val))
            }).collect(),
            input_count: res.input_count,
            output_transforms: res.output_transforms.into_iter().map(convert_transform).collect()
        };
        return Ok(result);
    }
}