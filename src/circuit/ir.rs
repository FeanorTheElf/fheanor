use std::alloc::Allocator;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::mem::replace;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;

use append_only_vec::AppendOnlyVec;
use feanor_math::algorithms::convolution::ConvolutionAlgorithm;
use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::primitive_int::*;
use feanor_math::ring::RingStore;
use feanor_math::ring::*;
use feanor_math::rings::extension::FreeAlgebra;
use feanor_math::rings::zn::*;
use feanor_math::seq::VectorFn;
use fhe_ir::*;
use tracing::instrument;

use crate::circuit::evaluator::CircuitEvaluator;
use crate::number_ring::galois::*;
use crate::number_ring::quotient_by_ideal::NumberRingQuotientByIdealBase;
use crate::*;
use crate::circuit::{Coefficient, PlaintextCircuit};
use crate::number_ring::NumberRingDescriptor;
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;

pub trait ElToIRRing: RingBase {

    type ElRepr: Display + FromStr;

    fn into_repr(&self, el: &Self::Element) -> Self::ElRepr;
    fn from_repr(&self, repr: &Self::ElRepr) -> Self::Element;
}

impl<NumberRing, ZnTy, A, C> ElToIRRing for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: NumberRingDescriptor,
        ZnTy: RingStore + Clone,
        ZnTy::Type: NiceZn,
        <ZnTy::Type as ZnRing>::IntegerRing: Default,
        A: FheanorAllocator,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type ElRepr = ValueList<ValueInt<<ZnTy::Type as ZnRing>::IntegerRing>>;

    fn into_repr(&self, el: &Self::Element) -> Self::ElRepr {
        ValueList::from(self.wrt_canonical_basis(&el).iter().map(|x| ValueInt::from(self.base_ring().smallest_lift(x))).collect::<Vec<_>>())
    }

    fn from_repr(&self, repr: &Self::ElRepr) -> Self::Element {
        let mod_modulus = self.base_ring().can_hom(self.base_ring().integer_ring()).unwrap();
        self.from_canonical_basis(repr.iter().map(|x| mod_modulus.map_ref(x)))
    }
}

impl<NumberRing, ZnTy, A, C> ElToIRRing for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: NumberRingDescriptor,
        ZnTy: RingStore + Clone,
        ZnTy::Type: NiceZn,
        <ZnTy::Type as ZnRing>::IntegerRing: Default,
        A: FheanorAllocator,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    type ElRepr = ValueList<ValueInt<<ZnTy::Type as ZnRing>::IntegerRing>>;

    fn into_repr(&self, el: &Self::Element) -> Self::ElRepr {
        ValueList::from(self.wrt_canonical_basis(&el).iter().map(|x| ValueInt::from(self.base_ring().smallest_lift(x))).collect::<Vec<_>>())
    }

    fn from_repr(&self, repr: &Self::ElRepr) -> Self::Element {
        let mod_modulus = self.base_ring().can_hom(self.base_ring().integer_ring()).unwrap();
        self.from_canonical_basis(repr.iter().map(|x| mod_modulus.map_ref(x)))
    }
}

impl ElToIRRing for BigIntRingBase {
    type ElRepr = ValueInt<BigIntRing>;

    fn from_repr(&self, repr: &Self::ElRepr) -> Self::Element {
        self.clone_el(repr)
    }

    fn into_repr(&self, el: &Self::Element) -> Self::ElRepr {
        ValueInt::from(self.clone_el(el))
    }
}

impl ElToIRRing for zn_64::ZnBase {

    type ElRepr = i64;

    fn from_repr(&self, repr: &Self::ElRepr) -> Self::Element {
        RingRef::new(self).can_hom(&ZZi64).unwrap().map_ref(repr)
    }

    fn into_repr(&self, el: &Self::Element) -> Self::ElRepr {
        self.smallest_lift(*el)
    }
}

impl<I> ElToIRRing for zn_big::ZnBase<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    type ElRepr = ValueInt<I>;

    fn from_repr(&self, repr: &Self::ElRepr) -> Self::Element {
        RingRef::new(self).can_hom(&I::default()).unwrap().map_ref(repr)
    }

    fn into_repr(&self, el: &Self::Element) -> Self::ElRepr {
        ValueInt::from(self.smallest_lift(self.clone_el(el)))
    }
}

impl ElToIRRing for StaticRingBase<i64> {

    type ElRepr = i64;

    fn from_repr(&self, repr: &Self::ElRepr) -> Self::Element {
        *repr
    }

    fn into_repr(&self, el: &Self::Element) -> Self::ElRepr {
        *el
    }
}

impl ElToIRRing for StaticRingBase<i128> {

    type ElRepr = i128;

    fn from_repr(&self, repr: &Self::ElRepr) -> Self::Element {
        *repr
    }

    fn into_repr(&self, el: &Self::Element) -> Self::ElRepr {
        *el
    }
}

pub struct ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    data: El<I>,
}

impl<I> ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    pub fn from(data: El<I>) -> Self {
        Self { data }
    }

    pub fn into(self) -> El<I> {
        self.data
    }
}

impl<I> Clone for ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    fn clone(&self) -> Self {
        Self {
            data: I::default().clone_el(&self.data)
        }
    }
}
impl<I> PartialEq for ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    fn eq(&self, other: &Self) -> bool {
        I::default().eq_el(self, other)
    }
}

impl<I> Eq for ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{}

impl<I> Display for ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        I::default().get_ring().dbg(&self.data, f)
    }
}

impl<I> Debug for ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl<I> FromStr for ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    type Err = ();
    
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        return Ok(Self::from(I::default().parse(s, 10).map_err(|()| ())?));
    }
}

impl<I> Deref for ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    type Target = El<I>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<I> DerefMut for ValueInt<I>
    where I: RingStore + Default,
        I::Type: IntegerRing
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

struct ToIREvaluator<'idents, 'constants, 'values, R: ?Sized + RingBase> {
    galois_group: Option<CyclotomicGaloisGroup>,
    identifiers: &'idents AppendOnlyVec<String>,
    constants: &'idents AppendOnlyVec<(String, &'constants Coefficient<R>)>,
    instructions: &'values AppendOnlyVec<Instruction<'idents>>
}

impl<'idents, 'constants, 'values, R: ?Sized + RingBase> ToIREvaluator<'idents, 'constants, 'values, R> {
    fn new_ident(&self) -> (usize, &'idents str) {
        let result = self.identifiers.len();
        self.identifiers.push(format!("%{}", result));
        return (result, self.identifiers[result].as_str());
    }

    fn new_plaintext(&self, value: &'constants Coefficient<R>) -> &'idents str {
        let result = self.constants.len();
        self.constants.push((format!("@{}", result), value));
        return self.constants[result].0.as_str();
    }
}

impl<'idents, 'constants, 'values, R: ?Sized + RingBase> Clone for ToIREvaluator<'idents, 'constants, 'values, R> {

    fn clone(&self) -> Self {
        Self {
            constants: self.constants,
            galois_group: self.galois_group.clone(),
            identifiers: self.identifiers,
            instructions: self.instructions
        }
    }
}

impl<'idents, 'constants, 'values, R: ?Sized + RingBase> CircuitEvaluator<'constants, usize, R> for ToIREvaluator<'idents, 'constants, 'values, R> {
    fn supports_gal(&self) -> bool { true }
    fn supports_mul(&self) -> bool { true }
    
    fn inner_prod<'a, I>(&mut self, data: I) -> usize
        where I: Iterator<Item = (&'constants Coefficient<R>, &'a usize)>,
            R: 'constants
    {
        let data = data.filter(|(coeff, _)| !coeff.is_zero()).collect::<Vec<_>>();
        if data.len() == 0 {
            let (id, name) = self.new_ident();
            self.instructions.push(Instruction::Zero { out: name });
            return id;
        } else if data.len() == 1 {
            return if let Coefficient::One = data[0].0 {
                *data[0].1
            } else if let Some(int) = data[0].0.as_integer() {
                if ZZbig.abs_log2_ceil(&int).unwrap_or(0) <= i64::BITS as usize {
                    let (id, name) = self.new_ident();
                    self.instructions.push(Instruction::MulIntCtx { out: name, value: self.identifiers[*data[0].1].as_str(), integer: int_cast(int, ZZi64, ZZbig) });
                    id
                } else {
                    let (id, name) = self.new_ident();
                    self.instructions.push(Instruction::MulPtxCtx { out: name, value: self.identifiers[*data[0].1].as_str(), plaintext: self.new_plaintext(&data[0].0) });
                    id
                }
            } else {
                let (id, name) = self.new_ident();
                self.instructions.push(Instruction::MulPtxCtx { out: name, value: self.identifiers[*data[0].1].as_str(), plaintext: self.new_plaintext(&data[0].0) });
                id
            };
        } else {
            let (id, name) = self.new_ident();
            let mut values = Vec::new();
            let mut coefficients = Vec::new();
            for (coeff, val) in data {
                values.push(self.identifiers[*val].as_str());
                coefficients.push(self.new_plaintext(coeff));
            }
            self.instructions.push(Instruction::InnerProduct { out: name, values: values, coefficients: coefficients });
            return id;
        }
    }

    fn add_constant(&mut self, val: usize, constant: &'constants Coefficient<R>) -> usize {
        let (id, name) = self.new_ident();
        self.instructions.push(Instruction::AddPtxCtx { out: name, value: self.identifiers[val].as_str(), plaintext: self.new_plaintext(constant) });
        return id;
    }

    fn gal(&mut self, val: usize, gs: &'constants [GaloisGroupEl]) -> Vec<usize> {
        let galois_group = self.galois_group.as_ref().expect("cannot create a circuit with galois gates, if no galois group is given");
        let mut outputs = Vec::new();
        let mut output_names = Vec::new();
        let mut exponents = Vec::new();
        for g in gs {
            let (id, name) = self.new_ident();
            output_names.push(name);
            outputs.push(id);
            exponents.push(galois_group.underlying_ring().smallest_lift(*galois_group.as_ring_el(g)));
        }
        self.instructions.push(Instruction::Galois { out: output_names, val: self.identifiers[val].as_str(), exponents: exponents });
        return outputs;
    }

    fn mul(&mut self, lhs: usize, rhs: usize) -> usize {
        let (id, name) = self.new_ident();
        self.instructions.push(Instruction::MulCtxCtx { out: name, lhs: self.identifiers[lhs].as_str(), rhs: self.identifiers[rhs].as_str() });
        return id;
    }

    fn square(&mut self, val: usize) -> usize {
        self.mul(val, val)
    }
}

#[instrument(skip_all)]
pub fn circuit_to_ir<R>(ring: R, galois_group: Option<&Subgroup<CyclotomicGaloisGroup>>, circuit: &PlaintextCircuit<R::Type>) -> Program<<R::Type as ElToIRRing>::ElRepr>
    where R: RingStore + Copy,
        R::Type: ElToIRRing
{
    let constants = AppendOnlyVec::new();
    let identifiers = AppendOnlyVec::new();
    let instructions = AppendOnlyVec::new();
    let evaluator = ToIREvaluator {
        constants: &constants,
        galois_group: galois_group.map(|Gal| Gal.parent().clone()),
        identifiers: &identifiers,
        instructions: &instructions
    };
    let mut circuit_inputs = Vec::new();
    let mut program_inputs = Vec::new();
    for _ in 0..circuit.input_count {
        let (id, name) = evaluator.new_ident();
        circuit_inputs.push(id);
        program_inputs.push(name);
    }
    let outputs = circuit.evaluate_generic(&circuit_inputs, evaluator.clone());
    for output in outputs {
        evaluator.instructions.push(Instruction::Return { val: evaluator.identifiers[output].as_str() });
    }
    return Program::new(
        &program_inputs, 
        instructions.into_vec(),
        constants.iter().map(|(k, v)| (k.as_str(), ring.get_ring().into_repr(&(*v).clone(ring).to_ring_el(ring)))).collect()
    );
}

#[instrument(skip_all)]
pub fn ir_to_circuit<R>(ring: R, galois_group: Option<&Subgroup<CyclotomicGaloisGroup>>, program: &Program<<R::Type as ElToIRRing>::ElRepr>) -> PlaintextCircuit<R::Type>
    where R: RingStore + Copy,
        R::Type: ElToIRRing
{
    program.check().unwrap();
    let mut mapping = HashMap::new();
    for (i, input) in program.inputs().enumerate() {
        mapping.insert(input, i);
    }
    let mut current = PlaintextCircuit::identity(program.inputs().len(), ring);
    let mut outputs = Vec::new();
    for inst in program.instructions_with_data() {
        let current_wires = current.output_count();
        match inst {
            GenericInstruction::Copy { out, val } => {
                current = PlaintextCircuit::identity(current_wires, ring).tensor(PlaintextCircuit::select(current_wires, &[*mapping.get(val).unwrap()], ring), ring).compose(current.output_twice(ring), ring);
                _ = mapping.insert(out, current_wires);
            },
            GenericInstruction::AddCtxCtx { out, lhs, rhs } => {
                current = PlaintextCircuit::identity(current_wires, ring).tensor(
                    PlaintextCircuit::add(ring).compose(PlaintextCircuit::select(current_wires, &[*mapping.get(lhs).unwrap(), *mapping.get(rhs).unwrap()], ring), ring), ring
                ).compose(current.output_twice(ring), ring);
                _ = mapping.insert(out, current_wires);
            },
            GenericInstruction::MulCtxCtx { out, lhs, rhs } => {
                if lhs == rhs {
                    current = PlaintextCircuit::identity(current_wires, ring).tensor(
                        PlaintextCircuit::square(ring).compose(PlaintextCircuit::select(current_wires, &[*mapping.get(lhs).unwrap()], ring), ring), ring
                    ).compose(current.output_twice(ring), ring);
                } else {
                    current = PlaintextCircuit::identity(current_wires, ring).tensor(
                        PlaintextCircuit::mul(ring).compose(PlaintextCircuit::select(current_wires, &[*mapping.get(lhs).unwrap(), *mapping.get(rhs).unwrap()], ring), ring), ring
                    ).compose(current.output_twice(ring), ring);
                }
                _ = mapping.insert(out, current_wires);
            },
            GenericInstruction::Galois { out, val, exponents } => {
                let galois_group = galois_group.as_ref().expect("cannot create a circuit with galois gates, if no galois group is given");
                current = PlaintextCircuit::identity(current_wires, ring).tensor(
                    PlaintextCircuit::gal_many(&exponents.iter().copied().map(|g| galois_group.from_representative(g)).collect::<Vec<_>>(), galois_group, ring)
                        .compose(PlaintextCircuit::select(current_wires, &[*mapping.get(val).unwrap()], ring), ring), ring
                ).compose(current.output_twice(ring), ring);
                for (i, out) in out.iter().copied().enumerate() {
                    _ = mapping.insert(out, current_wires + i);
                }
            },
            GenericInstruction::Zero { out } => {
                current = PlaintextCircuit::identity(current_wires, ring).tensor(PlaintextCircuit::constant_int(ZZbig.zero(), ring), ring).compose(current.output_twice(ring), ring);
                _ = mapping.insert(out, current_wires);
            },
            GenericInstruction::InnerProduct { out, values, coefficients } => {
                let mut all_coeffs = (0..current_wires).map(|_| Coefficient::Zero).collect::<Vec<_>>();
                for (val, coeff) in values.iter().zip(coefficients.iter()) {
                    let prev_coeff = replace(&mut all_coeffs[*mapping.get(*val).unwrap()], Coefficient::Zero);
                    all_coeffs[*mapping.get(*val).unwrap()] = prev_coeff.add(Coefficient::from(ring.get_ring().from_repr(coeff), ring), ring);
                }
                current = PlaintextCircuit::identity(current_wires, ring).tensor(
                    PlaintextCircuit::linear_transform(&all_coeffs, ring), ring
                ).compose(current.output_twice(ring), ring);
                _ = mapping.insert(out, current_wires);
            },
            GenericInstruction::AddPtxCtx { out, value, plaintext } => {
                current = PlaintextCircuit::identity(current_wires, ring).tensor(
                    PlaintextCircuit::add(ring).compose(PlaintextCircuit::select(current_wires, &[*mapping.get(value).unwrap()], ring)
                        .tensor(PlaintextCircuit::constant(ring.get_ring().from_repr(plaintext), ring), ring), ring), ring
                ).compose(current.output_twice(ring), ring);
                _ = mapping.insert(out, current_wires);
            },
            GenericInstruction::MulPtxCtx { out, value, plaintext } => {
                current = PlaintextCircuit::identity(current_wires, ring).tensor(
                    PlaintextCircuit::linear_transform_ring(&[ring.get_ring().from_repr(plaintext)], ring)
                        .compose(PlaintextCircuit::select(current_wires, &[*mapping.get(value).unwrap()], ring), ring), ring
                ).compose(current.output_twice(ring), ring);
                _ = mapping.insert(out, current_wires);
            },
            GenericInstruction::MulIntCtx { out, value, integer } => {
                let coefficient = match integer {
                    0 => Coefficient::Zero,
                    1 => Coefficient::One,
                    -1 => Coefficient::NegOne,
                    x => Coefficient::Integer(int_cast(x, ZZbig, ZZi64))
                };
                current = PlaintextCircuit::identity(current_wires, ring).tensor(
                    PlaintextCircuit::linear_transform(&[coefficient], ring)
                        .compose(PlaintextCircuit::select(current_wires, &[*mapping.get(value).unwrap()], ring), ring), ring
                ).compose(current.output_twice(ring), ring);
                _ = mapping.insert(out, current_wires);
            },
            GenericInstruction::Return { val } => {
                outputs.push(*mapping.get(val).unwrap());
            }
        }
        debug_assert_eq!(program.inputs().len(), current.input_count());
    }
    return PlaintextCircuit::select(current.output_count(), &outputs, ring).compose(current, ring);
}

#[cfg(test)]
use crate::lin_transform::pow2;
#[cfg(test)]
use crate::number_ring::hypercube::isomorphism::HypercubeIsomorphism;
#[cfg(test)]
use crate::number_ring::hypercube::structure::HypercubeStructure;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::NumberRingQuotientStore;
#[cfg(test)]
use crate::circuit::DEFAULT_EVALUATOR_COSTS;

#[test]
fn test_circuit_to_ir() {
    feanor_tracing::DelayedLogger::init_test();
    let ring = StaticRing::<i64>::RING;
    let x = PlaintextCircuit::linear_transform_ring(&[1], ring);
    let neg_x = PlaintextCircuit::linear_transform_ring(&[-1], ring);
    let x_neg_x = PlaintextCircuit::mul(ring).compose(x.clone(ring).tensor(neg_x, ring), ring).compose(x.output_twice(ring), ring);
    let two_minus_x_neg_x = PlaintextCircuit::add(ring).compose(x_neg_x.tensor(PlaintextCircuit::constant(2, ring), ring), ring);
    let circuit = PlaintextCircuit::square(ring).compose(two_minus_x_neg_x, ring); // (2 - x * x) * (2 - x * x)
    
    let program = Program::parse(r#"
        func(%0) {
            %1 = mul_ptx %0, @0
            %2 = mul %0, %1
            %3 = add_ptx %2, @1
            %4 = mul %3, %3
            return %4
        }
        @0: -1
        @1: 2
    "#.as_bytes()).unwrap();
    program.check().unwrap();
    assert_eq!(program, circuit_to_ir(ring, None, &circuit));
}

#[test]
fn test_ir_to_circuit() {
    feanor_tracing::DelayedLogger::init_test();
    let ring = StaticRing::<i64>::RING;
    let x = PlaintextCircuit::linear_transform_ring(&[1], ring);
    let neg_x = PlaintextCircuit::linear_transform_ring(&[-1], ring);
    let x_neg_x = PlaintextCircuit::mul(ring).compose(x.clone(ring).tensor(neg_x, ring), ring).compose(x.output_twice(ring), ring);
    let two_minus_x_neg_x = PlaintextCircuit::add(ring).compose(x_neg_x.tensor(PlaintextCircuit::constant(2, ring), ring), ring);
    let circuit = PlaintextCircuit::square(ring).compose(two_minus_x_neg_x, ring); // (2 - x * x) * (2 - x * x)
    
    let program = Program::parse(r#"
        func(%0) {
            %1 = mul_ptx %0, @0
            %2 = mul %0, %1
            %3 = add_ptx %2, @1
            %4 = mul %3, %3
            return %4
        }
        @0: -1
        @1: 2
    "#.as_bytes()).unwrap();
    program.check().unwrap();
    assert!(circuit.eq(&ir_to_circuit(ring, None, &program), ring, None));
}

#[test]
fn test_from_to_ir() {
    feanor_tracing::DelayedLogger::init_test();
    let m = 1 << 8;
    let e = 1;

    let P = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(m), zn_big::Zn::new(ZZbig, ZZbig.pow(int_cast(65537, ZZbig, ZZi64), e + 1)));
    let H = {
        let hypercube = HypercubeStructure::default_pow2_hypercube(P.acting_galois_group(), int_cast(65537, ZZbig, ZZi64));
        HypercubeIsomorphism::new(&P, &hypercube, Some("./cache"))
    };
    let coeffs_to_slots = pow2::coeffs_to_slots_thin(&H, 4, &DEFAULT_EVALUATOR_COSTS);
    let program = coeffs_to_slots.to_ir(&P, Some(P.acting_galois_group()));
    assert!(coeffs_to_slots.eq(&PlaintextCircuit::from_ir(&P, Some(P.acting_galois_group()), &program), &P, Some(P.acting_galois_group())));

    let P = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(m), zn_big::Zn::new(ZZbig, ZZbig.pow(int_cast(65537, ZZbig, ZZi64), e)));
    let H = H.change_modulus(&P);
    let slots_to_coeffs = pow2::slots_to_coeffs_thin(&H, 4, &DEFAULT_EVALUATOR_COSTS);
    let program = slots_to_coeffs.to_ir(&P, Some(P.acting_galois_group()));
    assert!(slots_to_coeffs.eq(&PlaintextCircuit::from_ir(&P, Some(P.acting_galois_group()), &program), &P, Some(P.acting_galois_group())));
}