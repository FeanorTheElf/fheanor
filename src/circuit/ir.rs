use std::alloc::Allocator;

use append_only_vec::AppendOnlyVec;
use feanor_math::algorithms::convolution::ConvolutionAlgorithm;
use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::int_cast;
use feanor_math::primitive_int::*;
use feanor_math::ring::RingStore;
use feanor_math::ring::*;
use feanor_math::rings::extension::FreeAlgebra;
use feanor_math::rings::zn::*;
use feanor_math::seq::VectorFn;
use fhe_ir::*;

use crate::circuit::evaluator::CircuitEvaluator;
use crate::number_ring::galois::*;
use crate::number_ring::quotient_by_ideal::NumberRingQuotientByIdealBase;
use crate::*;
use crate::circuit::{Coefficient, PlaintextCircuit};
use crate::number_ring::AbstractNumberRing;
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;

pub trait ElAsIntListRing: RingBase {

    fn as_int_list(&self, el: &Self::Element) -> Vec<i64>;
    fn from_int_list(&self, list: &[i64]) -> Self::Element;
}

impl<NumberRing, ZnTy, A, C> ElAsIntListRing for NumberRingQuotientByIntBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore + Clone,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn as_int_list(&self, el: &Self::Element) -> Vec<i64> {
        self.wrt_canonical_basis(el).iter().map(|x| int_cast(self.base_ring().smallest_lift(x), ZZi64, self.base_ring().integer_ring())).collect()
    }

    fn from_int_list(&self, list: &[i64]) -> Self::Element {
        let mod_modulus = self.base_ring().can_hom(&ZZi64).unwrap();
        self.from_canonical_basis(list.iter().copied().map(|x| mod_modulus.map(x)))
    }
}

impl<NumberRing, ZnTy, A, C> ElAsIntListRing for NumberRingQuotientByIdealBase<NumberRing, ZnTy, A, C>
    where NumberRing: AbstractNumberRing,
        ZnTy: RingStore + Clone,
        ZnTy::Type: NiceZn,
        A: Allocator + Clone,
        C: ConvolutionAlgorithm<ZnTy::Type>
{
    fn as_int_list(&self, el: &Self::Element) -> Vec<i64> {
        self.wrt_canonical_basis(el).iter().map(|x| int_cast(self.base_ring().smallest_lift(x), ZZi64, self.base_ring().integer_ring())).collect()
    }

    fn from_int_list(&self, list: &[i64]) -> Self::Element {
        let mod_modulus = self.base_ring().can_hom(&ZZi64).unwrap();
        self.from_canonical_basis(list.iter().copied().map(|x| mod_modulus.map(x)))
    }
}

impl ElAsIntListRing for StaticRingBase<i64> {

    fn as_int_list(&self, el: &Self::Element) -> Vec<i64> {
        vec![*el]
    }

    fn from_int_list(&self, list: &[i64]) -> Self::Element {
        assert_eq!(1, list.len());
        list[0]
    }
}

struct ToIREvaluator<'idents, 'constants, 'values, R: ?Sized + RingBase> {
    galois_group: CyclotomicGaloisGroup,
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
                let (id, name) = self.new_ident();
                self.instructions.push(Instruction::MulIntCtx { out: name, value: self.identifiers[*data[0].1].as_str(), integer: int as i64 });
                id
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
        let mut outputs = Vec::new();
        let mut output_names = Vec::new();
        let mut exponents = Vec::new();
        for g in gs {
            let (id, name) = self.new_ident();
            output_names.push(name);
            outputs.push(id);
            exponents.push(self.galois_group.underlying_ring().smallest_lift(*self.galois_group.as_ring_el(g)));
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

pub fn circuit_to_ir<R>(ring: R, galois_group: &Subgroup<CyclotomicGaloisGroup>, circuit: &PlaintextCircuit<R::Type>) -> Program
    where R: RingStore + Copy,
        R::Type: ElAsIntListRing
{
    let constants = AppendOnlyVec::new();
    let identifiers = AppendOnlyVec::new();
    let instructions = AppendOnlyVec::new();
    let evaluator = ToIREvaluator {
        constants: &constants,
        galois_group: galois_group.parent().clone(),
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
        constants.iter().map(|(k, v)| (k.as_str(), PlaintextData::from(ring.get_ring().as_int_list(&(*v).clone(ring).to_ring_el(ring))))).collect()
    );
}

#[test]
fn test_circuit_to_ir() {
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
        @0: [-1]
        @1: [2]
    "#.as_bytes()).unwrap();
    program.check().unwrap();
    assert_eq!(program, circuit_to_ir(ring, &CyclotomicGaloisGroupBase::new(2).into().full_subgroup(), &circuit));
}

#[test]
#[ignore]
fn generate_slots_to_coeffs() {
    use std::cell::LazyCell;
    use std::fs::File;
    use std::io::{BufWriter, Write};
    use crate::lin_transform::pow2;
    use crate::number_ring::hypercube::isomorphism::HypercubeIsomorphism;
    use crate::number_ring::hypercube::structure::HypercubeStructure;
    use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
    use crate::number_ring::NumberRingQuotientStore;
    use crate::circuit::create_circuit_cached;

    let P = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(1 << 16), zn_big::Zn::new(ZZbig, ZZbig.pow(int_cast(65537, ZZbig, ZZi64), 5)));
    let H = LazyCell::new(|| {
        let hypercube = HypercubeStructure::default_pow2_hypercube(P.acting_galois_group(), int_cast(65537, ZZbig, ZZi64));
        HypercubeIsomorphism::new::<true>(&&P, &hypercube, Some("."))
    });
    let coeffs_to_slots = create_circuit_cached::<_, _, true>(
        &P, 
        &filename_keys![coeffs2slots, m: 1 << 16, p: 65537, e: 5, levels: 4], 
        Some("."), 
        || pow2::coeffs_to_slots_thin(&H, 4)
    );
    let program = circuit_to_ir(&P, P.acting_galois_group(), &coeffs_to_slots);
    write!(BufWriter::new(File::open("./coeffs_to_slots_m65536_p65537_e5_levels4.fheir").unwrap()), "{}", program).unwrap();

    let P = NumberRingQuotientByIntBase::new(Pow2CyclotomicNumberRing::new(1 << 16), zn_big::Zn::new(ZZbig, ZZbig.pow(int_cast(65537, ZZbig, ZZi64), 4)));
    let H = LazyCell::new(|| H.change_modulus(&P));
    let slots_to_coeffs = create_circuit_cached::<_, _, true>(
        &P, 
        &filename_keys![coeffs2slots, m: 1 << 16, p: 65537, e: 5, levels: 4], 
        Some("."), 
        || pow2::slots_to_coeffs_thin(&H, 4)
    );
    let program = circuit_to_ir(&P, P.acting_galois_group(), &slots_to_coeffs);
    write!(BufWriter::new(File::open("./slots_to_coeffs_m65536_p65537_e4_levels4.fheir").unwrap()), "{}", program).unwrap();
}