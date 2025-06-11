use std::cell::RefCell;
use std::cmp::max;

use evaluator::CircuitEvaluator;
use evaluator::HomEvaluator;
use evaluator::HomEvaluatorGal;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::ring::*;

use crate::cyclotomic::*;

///
/// Contains [`serialization::DeserializeSeedPlaintextCircuit`], a [`serde::de::DeserializeSeed`] that
/// can deserialize a circuit when given the ring over which its coefficients are defined.
/// 
pub mod serialization;
///
/// Contains the trait [`evaluator::CircuitEvaluator`] and different implementations, which describe
/// how to evaluate an arithmetic circuit.
/// 
pub mod evaluator;

///
/// A coefficient used in a [`PlaintextCircuit`].
/// 
/// Generally speaking, this always represents an element of `R`
/// (which can be retrieved via [`Coefficient::to_ring_el()`]), but
/// special cases are stored separately for a more efficient evaluation.
/// 
pub enum Coefficient<R: ?Sized + RingBase> {
    Zero, One, NegOne, Integer(i32), Other(R::Element)
}

impl<R> Clone for Coefficient<R>
    where R: ?Sized + RingBase,
        R::Element: Clone
{
    fn clone(&self) -> Self {
        match self {
            Coefficient::Zero => Coefficient::Zero,
            Coefficient::One => Coefficient::One,
            Coefficient::NegOne => Coefficient::NegOne,
            Coefficient::Integer(x) => Coefficient::Integer(*x),
            Coefficient::Other(x) => Coefficient::Other(x.clone())
        }
    }
}

impl<R> Copy for Coefficient<R>
    where R: ?Sized + RingBase,
        R::Element: Copy
{}

impl<R: ?Sized + RingBase> Coefficient<R> {

    pub fn clone<S: RingStore<Type = R>>(&self, ring: S) -> Self {
        match self {
            Coefficient::Zero => Coefficient::Zero,
            Coefficient::One => Coefficient::One,
            Coefficient::NegOne => Coefficient::NegOne,
            Coefficient::Integer(x) => Coefficient::Integer(*x),
            Coefficient::Other(x) => Coefficient::Other(ring.clone_el(x))
        }
    }

    pub fn eq<S: RingStore<Type = R> + Copy>(&self, other: &Self, ring: S) -> bool {
        ring.eq_el(&self.clone(ring).to_ring_el(ring), &other.clone(ring).to_ring_el(ring))
    }

    ///
    /// Computes `self + x`, but avoids a full ring addition if `self` is zero.
    /// 
    pub fn add_to<S: RingStore<Type = R> + Copy>(&self, x: El<S>, ring: S) -> El<S> {
        match self {
            Coefficient::Zero => x,
            Coefficient::One => ring.add(x, ring.one()),
            Coefficient::NegOne => ring.add(x, ring.neg_one()),
            Coefficient::Integer(y) => ring.add(x, ring.int_hom().map(*y)),
            Coefficient::Other(y) => ring.add_ref_snd(x, y)
        }
    }

    ///
    /// Computes `self * x`, but avoids a full ring multiplication if `self`
    /// is stored as an integer.
    /// 
    pub fn mul_to<S: RingStore<Type = R> + Copy>(&self, x: El<S>, ring: S) -> El<S> {
        match self {
            Coefficient::Zero => ring.zero(),
            Coefficient::One => x,
            Coefficient::NegOne => ring.negate(x),
            Coefficient::Integer(y) => ring.int_hom().mul_map(x, *y),
            Coefficient::Other(y) => ring.mul_ref_snd(x, y)
        }
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Coefficient::Zero => true,
            _ => false
        }
    }

    fn from<S: RingStore<Type = R> + Copy>(el: El<S>, ring: S) -> Self {
        if ring.is_zero(&el) {
            Coefficient::Zero
        } else if ring.is_one(&el) {
            Coefficient::One
        } else {
            Coefficient::Other(el)
        }
    }

    pub fn to_ring_el<S: RingStore<Type = R>>(self, ring: S) -> El<S> {
        match self {
            Coefficient::Zero => ring.zero(),
            Coefficient::One => ring.one(),
            Coefficient::NegOne => ring.neg_one(),
            Coefficient::Integer(x) => ring.int_hom().map(x),
            Coefficient::Other(x) => x
        }
    }

    pub fn negate<S: RingStore<Type = R>>(self, ring: S) -> Self {
        match self {
            Coefficient::Zero => Coefficient::Zero,
            Coefficient::One => Coefficient::NegOne,
            Coefficient::NegOne => Coefficient::One,
            Coefficient::Integer(x) => Coefficient::Integer(-x),
            Coefficient::Other(x) => Coefficient::Other(ring.negate(x))
        }
    }

    pub fn add<S: RingStore<Type = R> + Copy>(self, other: Self, ring: S) -> Self {
        match (self, other) {
            (Coefficient::Zero, rhs) => rhs,
            (lhs, Coefficient::Zero) => lhs,
            (Coefficient::One, Coefficient::Integer(x)) => Coefficient::Integer(x + 1),
            (Coefficient::NegOne, Coefficient::Integer(x)) => Coefficient::Integer(x - 1),
            (Coefficient::Integer(x), Coefficient::One) => Coefficient::Integer(x + 1),
            (Coefficient::Integer(x), Coefficient::NegOne) => Coefficient::Integer(x - 1),
            (lhs, rhs) => Coefficient::Other(ring.add(lhs.to_ring_el(ring), rhs.to_ring_el(ring)))
        }
    }

    pub fn mul<S: RingStore<Type = R> + Copy>(self, other: Self, ring: S) -> Self {
        match (self, other) {
            (Coefficient::Zero, _) => Coefficient::Zero,
            (_, Coefficient::Zero) => Coefficient::Zero,
            (Coefficient::One, rhs) => rhs,
            (lhs, Coefficient::One) => lhs,
            (lhs, Coefficient::NegOne) => lhs.negate(ring),
            (Coefficient::NegOne, rhs) => rhs.negate(ring),
            (lhs, rhs) => Coefficient::Other(ring.mul(lhs.to_ring_el(ring), rhs.to_ring_el(ring)))
        }
    }

    ///
    /// Preserves integer coefficients, and maps ring elements as specified
    /// by the given function.
    /// 
    pub fn change_ring<S, F>(self, mut f: F) -> Coefficient<S>
        where F: FnMut(R::Element) -> S::Element,
            S: ?Sized + RingBase
    {
        match self {
            Coefficient::Integer(x) => Coefficient::Integer(x),
            Coefficient::NegOne => Coefficient::NegOne,
            Coefficient::Zero => Coefficient::Zero,
            Coefficient::One => Coefficient::One,
            Coefficient::Other(x) => Coefficient::Other(f(x))
        }
    }

}

///
/// A "linear combination" gate, which takes an affine linear combination
/// of an arbitrary number of inputs with coefficients in the ring, and produces
/// a single output.
/// 
struct LinearCombination<R: ?Sized + RingBase> {
    factors: Vec<Coefficient<R>>,
    constant: Coefficient<R>
}

impl<R: ?Sized + RingBase> LinearCombination<R> {

    fn clone<S: RingStore<Type = R> + Copy>(&self, ring: S) -> Self {
        Self {
            factors: self.factors.iter().map(|c| c.clone(ring)).collect(),
            constant: self.constant.clone(ring)
        }
    }

    fn evaluate_generic<'a, T, E>(&'a self, first_inputs: &[T], second_inputs: &[T], evaluator: &mut E) -> T
        where E: CircuitEvaluator<'a, T, R>
    {
        assert_eq!(self.factors.len(), first_inputs.len() + second_inputs.len());
        let current = evaluator.constant(&self.constant);
        let current = evaluator.add_inner_prod(
            current, 
            &self.factors[..first_inputs.len()],
            first_inputs
        );
        evaluator.add_inner_prod(
            current,
            &self.factors[first_inputs.len()..],
            second_inputs
        )
    }

    fn compose<S>(self, input_transforms: &[LinearCombination<R>], ring: S) -> LinearCombination<R>
        where S: RingStore<Type = R> + Copy
    {
        assert_eq!(self.factors.len(), input_transforms.len());
        if input_transforms.len() == 0 {
            return self.clone(ring);
        }
        let new_input_count = input_transforms[0].factors.len();
        assert!(input_transforms.iter().all(|t| t.factors.len() == new_input_count));
        let mut result_factors = (0..new_input_count).map(|_| Coefficient::Zero).collect::<Vec<_>>();
        let mut result_constant = self.constant.clone(ring);
        for (factor, t) in self.factors.into_iter().zip(input_transforms.iter()) {
            for i in 0..new_input_count {
                take_mut::take(&mut result_factors[i], |x| x.add(factor.clone(ring).mul(t.factors[i].clone(ring), ring), ring));
            }
            result_constant = result_constant.add(factor.mul(t.constant.clone(ring), ring), ring);
        }
        return LinearCombination {
            constant: result_constant,
            factors: result_factors
        };
    }
    
    fn change_ring<S, F1, F2>(self, change_summand: &mut F1, change_factor: &mut F2) -> LinearCombination<S>
        where F1: FnMut(Coefficient<R>) -> Coefficient<S>,
            F2: FnMut(Coefficient<R>) -> Coefficient<S>,
            S: ?Sized + RingBase
    {
        LinearCombination {
            constant: change_summand(self.constant),
            factors: self.factors.into_iter().map(|c| change_factor(c)).collect()
        }
    }
}

impl<R: RingBase + Default> PartialEq for LinearCombination<R> {
    
    fn eq(&self, other: &Self) -> bool {
        assert_eq!(self.factors.len(), other.factors.len());
        let ring = RingValue::<R>::default();
        return self.constant.eq(&other.constant, &ring) &&
            self.factors.iter().zip(other.factors.iter()).all(|(lhs, rhs)| lhs.eq(rhs, &ring));
    }
}

///
/// A nonlinear gate of a [`PlaintextCircuit`].
/// 
enum PlaintextCircuitGate<R: ?Sized + RingBase> {
    Mul(LinearCombination<R>, LinearCombination<R>),
    Square(LinearCombination<R>),
    Gal(Vec<CyclotomicGaloisGroupEl>, LinearCombination<R>)
}

impl<R: ?Sized + RingBase> PlaintextCircuitGate<R> {
    
    fn clone<S: RingStore<Type = R> + Copy>(&self, ring: S) -> Self {
        match self {
            PlaintextCircuitGate::Mul(lhs, rhs) => PlaintextCircuitGate::Mul(lhs.clone(ring), rhs.clone(ring)),
            PlaintextCircuitGate::Gal(gs, t) => PlaintextCircuitGate::Gal(gs.clone(), t.clone(ring)),
            PlaintextCircuitGate::Square(t) => PlaintextCircuitGate::Square(t.clone(ring))
        }
    }
}

impl<R: RingBase + Default> PartialEq for PlaintextCircuitGate<R> {
    
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PlaintextCircuitGate::Mul(self_lhs, self_rhs), PlaintextCircuitGate::Mul(other_lhs, other_rhs)) => self_lhs == other_lhs && self_rhs == other_rhs,
            (PlaintextCircuitGate::Square(self_t), PlaintextCircuitGate::Square(other_t)) => self_t == other_t,
            _ => false
        }
    }
}

///
/// Represents an arithmetic circuit (possibly including Galois gates) over
/// a ring of type `R`. 
/// 
/// In a sense, such a circuit can be considered to be a "HE program" that can
/// be run on encrypted inputs from the ring `R`. Of course, using a circuit for
/// HE computations is completely optional, the computations can also be performed
/// by directly operating on ciphertexts. At the very least, explicitly creating
/// a circuit will allow for much simpler testing, since it can also be executed
/// on unencrypted data.
/// 
/// Simple ways to create circuits are by using [`crate::digitextract::polys::low_depth_paterson_stockmeyer()`]
/// and [`crate::lintransform::matmul::MatmulTransform::matmul1d()`]. However, you 
/// can also manually build a circuit using the functions of [`PlaintextCircuit`], in
/// particular [`PlaintextCircuit::linear_transform()`], [`PlaintextCircuit::select()`],
/// [`PlaintextCircuit::tensor()`] and [`PlaintextCircuit::compose()`].
/// This allows specifying a circuit exactly, but is usually much more complicated than
/// computing a circuit from a linear transform or a set of polynomials.
/// 
/// Note that the ring is not stored by the circuit, but the same ring must be provided 
/// with every circuit operation that requires ring arithmetic. 
/// 
pub struct PlaintextCircuit<R: ?Sized + RingBase> {
    input_count: usize,
    gates: Vec<PlaintextCircuitGate<R>>,
    output_transforms: Vec<LinearCombination<R>>
}

impl<R: RingBase + Default> PartialEq for PlaintextCircuit<R> {

    fn eq(&self, other: &Self) -> bool {
        self.input_count == other.input_count && self.gates == other.gates && self.output_transforms == other.output_transforms
    }
}

impl<R: ?Sized + RingBase> PlaintextCircuit<R> {

    fn check_invariants(&self) {
        let mut current_count = self.input_count;
        for gate in &self.gates {
            match gate {
                PlaintextCircuitGate::Mul(lhs, rhs) => {
                    assert_eq!(current_count, lhs.factors.len());
                    assert_eq!(current_count, rhs.factors.len());
                    current_count += 1;
                },
                PlaintextCircuitGate::Gal(gs, t) => {
                    assert_eq!(current_count, t.factors.len());
                    current_count += gs.len();
                },
                PlaintextCircuitGate::Square(t) => {
                    assert_eq!(current_count, t.factors.len());
                    current_count += 1;
                }
            }
        }
        for out in &self.output_transforms {
            assert_eq!(current_count, out.factors.len());
        }
    }

    pub fn clone<S: RingStore<Type = R> + Copy>(&self, ring: S) -> Self {
        Self {
            gates: self.gates.iter().map(|gate| gate.clone(ring)).collect(),
            input_count: self.input_count,
            output_transforms: self.output_transforms.iter().map(|t| t.clone(ring)).collect()
        }
    }

    fn computed_wire_count(&self) -> usize {
        self.gates.iter().map(|gate| match gate {
            PlaintextCircuitGate::Mul(_, _) => 1,
            PlaintextCircuitGate::Square(_) => 1,
            PlaintextCircuitGate::Gal(gs, _) => gs.len()
        }).sum()
    }

    ///
    /// Creates the empty circuit, without in-or outputs.
    /// 
    pub fn empty() -> Self {
        Self {
            input_count: 0,
            gates: Vec::new(),
            output_transforms: Vec::new()
        }
    }

    ///
    /// Creates the constant circuit that always outputs the given constant
    /// ```text
    ///  |‾‾‾|
    ///  |___|
    ///    |
    /// ```
    /// 
    pub fn constant_i32<S: RingStore<Type = R>>(c: i32, _ring: S) -> Self {
        let result = Self {
            input_count: 0,
            gates: Vec::new(),
            output_transforms: vec![LinearCombination {
                constant: if c == 0{
                    Coefficient::Zero
                } else if c == 1 {
                    Coefficient::One
                } else {
                    Coefficient::Integer(c)
                },
                factors: Vec::new()
            }]
        };
        result.check_invariants();
        return result;
    }

    /// 
    /// Creates the constant circuit that always outputs the given constant
    /// ```text
    ///  |‾‾‾|
    ///  |___|
    ///    |
    /// ```
    /// 
    pub fn constant<S: RingStore<Type = R>>(el: El<S>, ring: S) -> Self {
        let result = Self {
            input_count: 0,
            gates: Vec::new(),
            output_transforms: vec![LinearCombination {
                constant: Coefficient::from(el, &ring),
                factors: Vec::new()
            }]
        };
        result.check_invariants();
        return result;
    }

    ///
    /// Computes a new circuit, which has the same graph structure as this circuit,
    /// and its constants are derived from this circuit's constants by the given function.
    /// 
    pub fn change_ring<S, F1, F2>(self, mut change_summand: F1, mut change_factor: F2) -> PlaintextCircuit<S>
        where F1: FnMut(Coefficient<R>) -> Coefficient<S>,
            F2: FnMut(Coefficient<R>) -> Coefficient<S>,
            S: ?Sized + RingBase
    {
        PlaintextCircuit {
            input_count: self.input_count,
            gates: self.gates.into_iter().map(|gate| match gate {
                PlaintextCircuitGate::Gal(gs, t) => PlaintextCircuitGate::Gal(gs, t.change_ring(&mut change_summand, &mut change_factor)),
                PlaintextCircuitGate::Mul(l, r) => PlaintextCircuitGate::Mul(l.change_ring(&mut change_summand, &mut change_factor), r.change_ring(&mut change_summand, &mut change_factor)),
                PlaintextCircuitGate::Square(t) => PlaintextCircuitGate::Square(t.change_ring(&mut change_summand, &mut change_factor))
            }).collect(),
            output_transforms: self.output_transforms.into_iter().map(|t| t.change_ring(&mut change_summand, &mut change_factor)).collect()
        }
    }

    ///
    /// Computes a new circuit, which has the same graph structure as this circuit,
    /// and its constants are derived from this circuit's constants by the given function.
    /// 
    pub fn change_ring_uniform<S, F>(self, f: F) -> PlaintextCircuit<S>
        where F: FnMut(Coefficient<R>) -> Coefficient<S>,
            S: ?Sized + RingBase
    {
        let f_refcell = RefCell::new(f);
        return self.change_ring(|x| (f_refcell.borrow_mut())(x), |x| (f_refcell.borrow_mut())(x));
    }

    /// 
    /// Creates the circuit that computes the linear transform of many input elements,
    /// w.r.t. the given list of coefficients.
    /// ```text
    ///        |   |   |   ...
    ///  |‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|
    ///  | c[0] x0 + c[1] x1 + ... |
    ///  |_________________________|
    ///              |
    /// ```
    /// If you want to pass the list of coefficients as ring elements, consider using
    /// [`PlaintextCircuit::linear_transform_ring()`].
    /// 
    pub fn linear_transform<S: RingStore<Type = R>>(coeffs: &[Coefficient<R>], ring: S) -> Self {
        let result = Self {
            input_count: coeffs.len(),
            gates: Vec::new(),
            output_transforms: vec![LinearCombination {
                constant: Coefficient::Zero,
                factors: coeffs.iter().map(|c| c.clone(&ring)).collect()
            }]
        };
        result.check_invariants();
        return result;
    }

    /// 
    /// Creates the circuit that computes the linear transform of many input elements,
    /// w.r.t. the given list of coefficients.
    /// ```text
    ///        |   |   |   ...
    ///  |‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|
    ///  | c[0] x0 + c[1] x1 + ... |
    ///  |_________________________|
    ///              |
    /// ```
    /// 
    pub fn linear_transform_ring<S: RingStore<Type = R>>(coeffs: &[El<S>], ring: S) -> Self {
        let result = Self {
            input_count: coeffs.len(),
            gates: Vec::new(),
            output_transforms: vec![LinearCombination {
                constant: Coefficient::Zero,
                factors: coeffs.iter().map(|c| Coefficient::from(ring.clone_el(c), &ring)).collect()
            }]
        };
        result.check_invariants();
        return result;
    }

    /// 
    /// Creates the circuit consisting of a single addition gate
    /// ```text
    ///   | |
    ///  |‾‾‾|
    ///  | + |
    ///  |___|
    ///    |
    /// ```
    /// This is a special case of [`PlaintextCircuit::linear_transform()`], in many cases
    /// the latter is more convenient to use.
    /// 
    pub fn add<S: RingStore<Type = R>>(_ring: S) -> Self {
        let result = Self {
            input_count: 2,
            gates: Vec::new(),
            output_transforms: vec![LinearCombination {
                constant: Coefficient::Zero,
                factors: vec![Coefficient::One, Coefficient::One]
            }]
        };
        return result;
    }

    ///
    /// Creates the circuit consisting of a single squaring gate
    /// ```text
    ///     |
    ///  |‾‾‾‾‾|
    ///  |  ^2 |
    ///  |_____|
    ///     |
    /// ```
    /// which is for most purposes equivalent to
    /// 
    /// ```text
    ///    |
    ///   |‾|
    ///  |‾‾‾|
    ///  | * |
    ///  |___|
    ///    |
    /// ```
    /// However, a square gate is stored separately, and may be evaluated
    /// more efficiently during circuit evaluation.
    /// 
    pub fn square<S: RingStore<Type = R>>(_ring: S) -> Self {
        let result = Self {
            input_count: 1,
            gates: vec![PlaintextCircuitGate::Square(LinearCombination {
                constant: Coefficient::Zero,
                factors: vec![Coefficient::One]
            })],
            output_transforms: vec![LinearCombination {
                constant: Coefficient::Zero,
                factors: vec![Coefficient::Zero, Coefficient::One]
            }]
        };
        return result;
    }

    /// 
    /// Creates the circuit consisting of a single subtraction gate
    /// ```text
    ///   | |
    ///  |‾‾‾|
    ///  | - |
    ///  |___|
    ///    |
    /// ```
    /// This is a special case of [`PlaintextCircuit::linear_transform()`], in many cases
    /// the latter is more convenient to use.
    /// 
    pub fn sub<S: RingStore<Type = R>>(_ring: S) -> Self {
        let result = Self {
            input_count: 2,
            gates: Vec::new(),
            output_transforms: vec![LinearCombination {
                constant: Coefficient::Zero,
                factors: vec![Coefficient::One, Coefficient::NegOne]
            }]
        };
        return result;
    }

    /// 
    /// Creates the circuit consisting of a single multiplication gate
    /// ```text
    ///   | |
    ///  |‾‾‾|
    ///  | * |
    ///  |___|
    ///    |
    /// ```
    /// 
    pub fn mul<S: RingStore<Type = R>>(_ring: S) -> Self {
        let result = Self {
            input_count: 2,
            gates: vec![PlaintextCircuitGate::Mul(
                LinearCombination {
                    constant: Coefficient::Zero,
                    factors: vec![Coefficient::One, Coefficient::Zero]
                },
                LinearCombination {
                    constant: Coefficient::Zero,
                    factors: vec![Coefficient::Zero, Coefficient::One]
                }
            )],
            output_transforms: vec![LinearCombination {
                constant: Coefficient::Zero,
                factors: vec![Coefficient::Zero, Coefficient::Zero, Coefficient::One]
            }]
        };
        result.check_invariants();
        return result;
    }

    /// 
    /// Creates the circuit consisting of a single Galois gate
    /// ```text
    ///    |
    ///  |‾‾‾|
    ///  | σ |
    ///  |___|
    ///    |
    /// ```
    /// 
    /// If the given automorphism is the identity, this will just
    /// give a circuit consisting of a single wire.
    /// 
    pub fn gal<S: RingStore<Type = R>>(g: CyclotomicGaloisGroupEl, galois_group: &CyclotomicGaloisGroup, ring: S) -> Self {
        Self::gal_many(std::slice::from_ref(&g), galois_group, ring)
    }

    /// 
    /// Creates the circuit consisting of a single multiple-Galois gate
    /// ```text
    ///         |
    ///  |‾‾‾‾‾‾‾‾‾‾‾‾‾|
    ///  | σ1, σ2, ... |
    ///  |_____________|
    ///    |   |  ...
    /// ```
    /// 
    /// All occurrences of the identity in the list of Galois automorphisms
    /// are automatically filtered out, and replaced by a direct wire to the
    /// input.
    /// 
    pub fn gal_many<S: RingStore<Type = R>>(gs: &[CyclotomicGaloisGroupEl], galois_group: &CyclotomicGaloisGroup, _ring: S) -> Self {
        let non_identity_gs = gs.iter().filter(|g| !galois_group.is_identity(**g)).copied().collect::<Vec<_>>();
        let len = non_identity_gs.len() + 1;
        let result = Self {
            input_count: 1,
            gates: vec![PlaintextCircuitGate::Gal(
                non_identity_gs, 
                LinearCombination {
                    constant: Coefficient::Zero,
                    factors: vec![Coefficient::One]
                }
            )],
            output_transforms:gs.iter().scan(0, |nonzero_gs, g| if galois_group.is_identity(*g) {
                Some(LinearCombination {
                    constant: Coefficient::Zero,
                    factors: [Coefficient::One].into_iter().chain((1..len).map(|_| Coefficient::Zero)).collect()
                })
            } else {
                *nonzero_gs += 1;
                Some(LinearCombination {
                    constant: Coefficient::Zero,
                    factors: (0..len).map(|j| if j == *nonzero_gs { Coefficient::One } else { Coefficient::Zero }).collect()
                })
            }).collect()
        };
        result.check_invariants();
        return result;
    }

    ///
    /// Copies all the output wires of this circuit, i.e. given a circuit
    /// ```text
    ///    | | | |
    ///   |‾‾‾‾‾‾‾|
    ///   |   C1  |
    ///   |_______|
    ///     | | |
    /// ```
    /// this computes
    /// ```text
    ///    | | | |
    ///   |‾‾‾‾‾‾‾|
    ///   |   C1  |
    ///   |_______|
    ///    |  ┊  ┊
    ///    |‾‾┊‾‾┊‾‾|
    ///    |  |‾‾┊‾‾┊‾‾|
    ///    |  |  |‾‾┊‾‾┊‾‾|
    ///    |  |  |  |  |  |
    /// ```
    /// 
    pub fn output_twice<S: RingStore<Type = R> + Copy>(self, ring: S) -> Self {
        self.output_times(2, ring)
    }

    ///
    /// Creates the circuit that drops the given number of wires, i.e. the circuit
    /// ```text
    ///   |  |  |  ...
    ///   ┴  ┴  ┴
    /// ```
    /// which has no output wires.
    /// 
    pub fn drop(wire_count: usize) -> Self {
        let result = Self {
            input_count: wire_count,
            gates: Vec::new(),
            output_transforms: Vec::new()
        };
        result.check_invariants();
        return result;
    }

    ///
    /// Creates the circuit that leaves all wires unchanged, i.e.
    /// ```text
    ///   |  |  |  |  ...
    ///   |  |  |  |  ...
    /// ```
    /// 
    pub fn identity<S: RingStore<Type = R>>(wire_count: usize, _ring: S) -> Self {
        let result = Self {
            input_count: wire_count,
            gates: Vec::new(),
            output_transforms: (0..wire_count).map(|i| LinearCombination {
                constant: Coefficient::Zero,
                factors: (0..wire_count).map(|j| if j == i { Coefficient::One } else { Coefficient::Zero }).collect()
            }).collect()
        };
        result.check_invariants();
        return result;
    }

    ///
    /// Creates the circuit that outputs the input wires at the indices given in `output_wires`.
    /// An input wire can be mentioned multiple times.
    /// 
    pub fn select<S: RingStore<Type = R>>(input_wire_count: usize, output_wires: &[usize], _ring: S) -> Self {
        let result = Self {
            input_count: input_wire_count,
            gates: Vec::new(),
            output_transforms: output_wires.iter().map(|i| {
                assert!(*i < input_wire_count);
                LinearCombination {
                    constant: Coefficient::Zero,
                    factors: (0..input_wire_count).map(|j| if *i == j { Coefficient::One } else { Coefficient::Zero }).collect()
                }
            }).collect()
        };
        result.check_invariants();
        return result;
    }

    pub fn output_times<S: RingStore<Type = R> + Copy>(self, times: usize, ring: S) -> Self {
        let result = Self {
            input_count: self.input_count,
            gates: self.gates.iter().map(|gate| gate.clone(ring)).collect(),
            output_transforms: (0..times).flat_map(|_| self.output_transforms.iter()).map(|lin| lin.clone(ring)).collect()
        };
        result.check_invariants();
        return result;
    }

    ///
    /// "Puts" two circuits "next to each other", i.e. given
    /// ```text
    ///    | | | |                  |
    ///   |‾‾‾‾‾‾‾|             |‾‾‾‾‾‾|
    ///   |   C1  |     and     |  C2  |
    ///   |_______|             |______|
    ///     | | |                 |  |
    /// ```
    /// this function computes the circuit
    /// ```text
    ///    | | | |  |
    ///   |‾‾‾‾‾‾‾|‾‾‾‾‾‾|
    ///   |   C1  |  C2  |
    ///   |_______|______|
    ///      | | |  | |
    /// ```
    /// 
    pub fn tensor<S: RingStore<Type = R>>(self, rhs: Self, ring: S) -> Self {
        let add_zeros = |vec: &[Coefficient<R>], index: usize, count: usize| 
            vec[0..index].iter().map(|c| c.clone(&ring))
                .chain(std::iter::repeat_with(|| Coefficient::Zero).take(count))
                .chain(vec[index..].iter().map(|c| c.clone(&ring)))
                .collect::<Vec<_>>();

        let map_self_transform = |t: &LinearCombination<R>| LinearCombination {
            constant: t.constant.clone(&ring),
            factors: add_zeros(&t.factors, self.input_count, rhs.input_count)
        };
        let map_rhs_transform = |t: &LinearCombination<R>| LinearCombination {
            constant: t.constant.clone(&ring),
            factors: add_zeros(&add_zeros(&t.factors, rhs.input_count, self.computed_wire_count()), 0, self.input_count)
        };
        let result = Self {
            input_count: self.input_count + rhs.input_count,
            gates: self.gates.iter().map(|gate| match gate {
                PlaintextCircuitGate::Mul(lhs, rhs) => PlaintextCircuitGate::Mul(
                    map_self_transform(&lhs),
                    map_self_transform(&rhs)
                ),
                PlaintextCircuitGate::Gal(gs, t) => PlaintextCircuitGate::Gal(
                    gs.clone(), 
                    map_self_transform(t)
                ),
                PlaintextCircuitGate::Square(t) => PlaintextCircuitGate::Square(
                    map_self_transform(t)
                )
            }).chain(
                rhs.gates.iter().map(|gate| match gate {
                    PlaintextCircuitGate::Mul(lhs, rhs) => PlaintextCircuitGate::Mul(
                        map_rhs_transform(&lhs),
                        map_rhs_transform(&rhs)
                    ),
                    PlaintextCircuitGate::Gal(gs, t) => PlaintextCircuitGate::Gal(
                        gs.clone(), 
                        map_rhs_transform(t)
                    ),
                    PlaintextCircuitGate::Square(t) => PlaintextCircuitGate::Square(
                        map_rhs_transform(t)
                    )
                })
            ).collect(),
            output_transforms: self.output_transforms.iter().map(|t| {
                assert_eq!(self.computed_wire_count() + self.input_count, t.factors.len());
                let added_inputs_t = map_self_transform(t);
                LinearCombination {
                    factors: add_zeros(&added_inputs_t.factors, self.input_count + rhs.input_count + self.computed_wire_count(), rhs.computed_wire_count()),
                    constant: added_inputs_t.constant
                }
            }).chain(rhs.output_transforms.iter().map(|t| {
                assert_eq!(rhs.computed_wire_count() + rhs.input_count, t.factors.len());
                map_rhs_transform(t)
            })).collect()
        };
        result.check_invariants();
        return result;
    }

    ///
    /// "Concatentates" two circuits, i.e. connects the output wires of the given circuit
    /// to the inputs of this circuit.
    /// 
    /// In other words, given
    /// ```text
    ///     |   |                  |
    ///   |‾‾‾‾‾‾‾|             |‾‾‾‾‾‾|
    ///   |   C1  |     and     |  C2  |
    ///   |_______|             |______|
    ///     | | |                 |  |
    /// ```
    /// this function computes the circuit
    /// ```text
    ///      |
    ///   |‾‾‾‾‾‾|
    ///   |  C2  |
    ///   |______|
    ///     |  |
    ///   |‾‾‾‾‾‾|
    ///   |  C1  |
    ///   |______|
    ///     | | |  
    /// ```
    /// 
    pub fn compose<S: RingStore<Type = R> + Copy>(self, first: Self, ring: S) -> Self {
        assert_eq!(first.output_count(), self.input_count());

        let map_transform = |t: &LinearCombination<R>| {
            let input_transform = LinearCombination {
                constant: t.constant.clone(&ring),
                factors: t.factors[0..self.input_count].iter().map(|c| c.clone(&ring)).collect()
            };
            let mut result = input_transform.compose(&first.output_transforms, ring);
            result.factors.extend(t.factors[self.input_count..].iter().map(|c| c.clone(&ring)));
            return result;
        };
        let result = Self {
            input_count: first.input_count,
            gates: first.gates.iter().map(|gate| gate.clone(ring)).chain(
                self.gates.iter().map(|gate| match gate {
                    PlaintextCircuitGate::Mul(lhs, rhs) => PlaintextCircuitGate::Mul(
                        map_transform(lhs),
                        map_transform(rhs),
                    ),
                    PlaintextCircuitGate::Gal(gs, t) => PlaintextCircuitGate::Gal(
                        gs.clone(),
                        map_transform(t)
                    ),
                    PlaintextCircuitGate::Square(t) => PlaintextCircuitGate::Square(
                        map_transform(t)
                    )
                })
            ).collect(),
            output_transforms: self.output_transforms.iter().map(map_transform).collect()
        };
        result.check_invariants();
        return result;
    }

    pub fn input_count(&self) -> usize {
        self.input_count
    }

    pub fn output_count(&self) -> usize {
        self.output_transforms.len()
    }
    
    ///
    /// Evaluates the circuit on inputs of type `T`, which in some sense encrypt/encode/represent
    /// elements of a ring, into which we can also embed the circuit constants.
    /// 
    /// More concretely, the ring whose elements are represented by `T` should support
    /// the following operations:
    ///  - `constant(c)` should return a `T` representing the ring element `c`
    ///  - `add_prod(y, c, x)` should return a `T` representing `y + c * x`
    ///  - `mul(x, y)` should return a `T` representing `x * y`
    ///  - `gal(gs, x)` should return a list of `T`s, with the `i`-th one representing `σ(x)` for `σ: 𝝵 -> 𝝵^gs[i]` 
    ///    the Galois automorphism defined by `gs[i]`  
    /// 
    /// Naturally, if the circuit does not contain multiplication gates (can be checked e.g. via [`PlaintextCircuit::has_multiplication_gates()`]),
    /// `add_prod` will never be called, and similarly for galois gates.
    /// 
    /// Note also that `constant` and `add_prod` are called even if the underlying element is `0` resp. `1`.
    /// Hence, it is recommended that the given functions for `constant` and `add_prod` perform a match on
    /// the given [`Coefficient`] and treat the `0` resp. `1` case differently.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use fheanor::circuit::*;
    /// # use fheanor::circuit::evaluator::*;
    /// # use feanor_math::ring::*;
    /// # use feanor_math::primitive_int::*;
    /// let circuit = PlaintextCircuit::add(StaticRing::<i64>::RING);
    /// assert_eq!(vec![3], circuit.evaluate_generic(
    ///     &[1 as i32, 2 as i32], 
    ///     DefaultCircuitEvaluator::new(
    ///         |x| x.to_ring_el(StaticRing::<i64>::RING) as i32, 
    ///         |x, c, y| x + c.mul_to(*y as i64, StaticRing::<i64>::RING) as i32,
    ///     )
    /// ));
    /// ```
    /// Of course, this example could have been more easily implemented using [`PlaintextCircuit::evaluate()`], since
    /// the operations used here exactly match the ones of `StaticRing::<i32>::RING`.
    /// 
    pub fn evaluate_generic<'a, T, E>(&'a self, inputs: &[T], mut evaluator: E) -> Vec<T>
        where E: CircuitEvaluator<'a, T, R>
    {
        assert_eq!(self.input_count, inputs.len());
        assert!(evaluator.supports_gal() || !self.has_galois_gates());
        assert!(evaluator.supports_mul() || !self.has_multiplication_gates());
        let mut current = Vec::new();
        for gate in &self.gates {
            match gate {
                PlaintextCircuitGate::Mul(lhs, rhs) => {
                    let lhs = lhs.evaluate_generic(inputs, &current, &mut evaluator);
                    let rhs = rhs.evaluate_generic(inputs, &current, &mut evaluator);
                    current.push(evaluator.mul(lhs, rhs));
                },
                PlaintextCircuitGate::Gal(gs, t) => {
                    let val = t.evaluate_generic(inputs, &current, &mut evaluator);
                    current.extend(evaluator.gal(val, gs));
                },
                PlaintextCircuitGate::Square(t) => {
                    let val = t.evaluate_generic(inputs, &current, &mut evaluator);
                    current.push(evaluator.square(val));
                }
            }
        }
        return self.output_transforms.iter().map(|t| t.evaluate_generic(inputs, &current, &mut evaluator)).collect()
    }

    ///
    /// Evaluates the given circuit on inputs from a ring into which we can
    /// embed the circuit constants.
    /// 
    /// Panics if the circuit contains galois gates.
    /// 
    pub fn evaluate_no_galois<S, H>(&self, inputs: &[S::Element], hom: H) -> Vec<S::Element>
        where S: ?Sized + RingBase,
            H: Homomorphism<R, S>
    {
        assert!(!self.has_galois_gates());
        return self.evaluate_generic(inputs, HomEvaluator::new(hom));
    }

    ///
    /// Evaluates the given circuit on inputs from a ring into which we can
    /// embed the circuit constants.
    /// 
    /// Note that the circuit might contain Galois gates, thus the given ring
    /// must support evaluation of Galois automorphisms. In case that it doesn't,
    /// you can use [`PlaintextCircuit::evaluate_no_galois()`].
    /// 
    pub fn evaluate<S, H>(&self, inputs: &[S::Element], hom: H) -> Vec<S::Element>
        where S: ?Sized + RingBase + CyclotomicRing,
            H: Homomorphism<R, S>
    {
        return self.evaluate_generic(inputs, HomEvaluatorGal::new(hom));
    }

    pub fn has_galois_gates(&self) -> bool {
        self.gates.iter().any(|gate| match gate {
            PlaintextCircuitGate::Gal(_, _) => true,
            PlaintextCircuitGate::Mul(_, _) => false,
            PlaintextCircuitGate::Square(_) => false
        })
    }

    pub fn has_multiplication_gates(&self) -> bool {
        self.gates.iter().any(|gate| match gate {
            PlaintextCircuitGate::Gal(_, _) => false,
            PlaintextCircuitGate::Mul(_, _) => true,
            PlaintextCircuitGate::Square(_) => true
        })
    }

    pub fn multiplication_gate_count(&self) -> usize {
        self.gates.iter().filter(|gate| match gate {
            PlaintextCircuitGate::Gal(_, _) => false,
            PlaintextCircuitGate::Mul(_, _) => true,
            PlaintextCircuitGate::Square(_) => true
        }).count()
    }

    ///
    /// Returns all galois automorphisms which are evaluated by some
    /// gate in this circuit.
    /// 
    /// This directly corresponds to those Galois automorphisms for which
    /// we require a Galois key when evaluating the circuit on encrypted
    /// inputs.
    /// 
    pub fn required_galois_keys(&self, galois_group: &CyclotomicGaloisGroup) -> Vec<CyclotomicGaloisGroupEl> {
        let mut result = self.gates.iter().flat_map(|gate| match gate {
            PlaintextCircuitGate::Gal(gs, _) => gs.iter().copied(),
            PlaintextCircuitGate::Mul(_, _) => [].iter().copied(),
            PlaintextCircuitGate::Square(_) => [].iter().copied()
        }).collect::<Vec<_>>();
        result.sort_unstable_by_key(|g| galois_group.representative(*g));
        result.dedup_by_key(|g| galois_group.representative(*g));
        return result;
    }
    
    ///
    /// Returns whether the circuit computes a linear map.
    /// 
    /// This is false if the circuit contains any multiplication gates.
    /// 
    pub fn is_linear(&self) -> bool {
        !self.has_multiplication_gates()
    }

    ///
    /// Returns the multiplicative depth of the `i`-th output, i.e.
    /// the maximal number of multiplication gates on a path from some input
    /// to the given output.
    /// 
    pub fn mul_depth(&self, i: usize) -> usize {
        let mut multiplicative_depths = Vec::new();
        multiplicative_depths.resize(self.input_count(), 0);
        let mult_depth_of_linear_combination = |lin_combination: &LinearCombination<_>, multiplicative_depths: &[usize]| {
            assert_eq!(lin_combination.factors.len(), multiplicative_depths.len());
            lin_combination.factors.iter().zip(multiplicative_depths.iter()).filter(|(factor, _)| !factor.is_zero()).map(|(_, d)| *d).max().unwrap_or(0)
        };
        for gate in &self.gates {
            let (new_depth, count) = match gate {
                PlaintextCircuitGate::Mul(lhs, rhs) => (max(mult_depth_of_linear_combination(lhs, &multiplicative_depths), mult_depth_of_linear_combination(rhs, &multiplicative_depths)) + 1, 1),
                PlaintextCircuitGate::Gal(gs, t) => (mult_depth_of_linear_combination(t, &multiplicative_depths), gs.len()),
                PlaintextCircuitGate::Square(t) => (mult_depth_of_linear_combination(t, &multiplicative_depths) + 1, 1)
            };
            multiplicative_depths.extend((0..count).map(|_| new_depth));
        }
        return mult_depth_of_linear_combination(&self.output_transforms[i], &multiplicative_depths);
    }

    ///
    /// Returns the maximal multiplicative depth of an output, i.e.
    /// the maximal number of multiplication gates on a path from some input
    /// to some output.
    /// 
    pub fn max_mul_depth(&self) -> usize {
        (0..self.output_count()).map(|i| self.mul_depth(i)).max().unwrap_or(0)
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::primitive_int::*;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;
#[cfg(test)]
use feanor_math::rings::extension::FreeAlgebraStore;
#[cfg(test)]
use crate::number_ring::quotient::NumberRingQuotientBase;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use serde::de::DeserializeSeed;
#[cfg(test)]
use serde::Serialize;
#[cfg(test)]
use serialization::DeserializeSeedPlaintextCircuit;
#[cfg(test)]
use serialization::SerializablePlaintextCircuit;

#[test]
fn test_circuit_tensor_compose() {
    let ring = StaticRing::<i64>::RING;
    let x = PlaintextCircuit::linear_transform_ring(&[1], ring);
    let x_sqr = PlaintextCircuit::mul(ring).compose(x.output_twice(ring), ring);
    assert!(PlaintextCircuit {
        input_count: 1,
        gates: vec![PlaintextCircuitGate::Mul(
            LinearCombination {
                constant: Coefficient::Zero,
                factors: vec![Coefficient::One]
            },
            LinearCombination {
                constant: Coefficient::Zero,
                factors: vec![Coefficient::One]
            }
        )],
        output_transforms: vec![LinearCombination {
            constant: Coefficient::Zero,
            factors: vec![Coefficient::Zero, Coefficient::One]
        }]
    } == x_sqr);

    let x = PlaintextCircuit::identity(1, ring);
    let y = PlaintextCircuit::identity(1, ring);
    let x_y_x_y = x.clone(&ring).tensor(y, ring).output_twice(ring);
    // z = 2 * x + 3 * y
    let x_y_z = x.clone(ring).tensor(x.clone(ring), ring).tensor(PlaintextCircuit::linear_transform_ring(&[2, 3], ring), ring).compose(x_y_x_y, ring);
    let xy_z = PlaintextCircuit::mul(ring).tensor(x, ring).compose(x_y_z, ring);
    // w = x * y * (2 * x + 3 * y)
    let w = PlaintextCircuit::mul(ring).compose(xy_z, ring);
    for x in -5..5 {
        for y in -5..5 {
            assert_eq!(x * y * (2 * x + 3 * y), w.evaluate_no_galois(&[x, y], ring.identity()).into_iter().next().unwrap());
        }
    }

    let w_1_sqr = PlaintextCircuit::mul(ring).compose(PlaintextCircuit::add(ring).compose(w.tensor(PlaintextCircuit::constant(1, ring), ring), ring).output_twice(ring), ring);
    for x in -5..5 {
        for y in -5..5 {
            assert_eq!(StaticRing::<i64>::RING.pow(x * y * (2 * x + 3 * y) + 1, 2), w_1_sqr.evaluate_no_galois(&[x, y], ring.identity()).into_iter().next().unwrap());
        }
    }
}

#[test]
fn test_circuit_tensor_compose_with_galois() {
    let ring = NumberRingQuotientBase::new(Pow2CyclotomicNumberRing::new(16), Zn::new(17));

    let x = PlaintextCircuit::identity(1, &ring);
    let y = PlaintextCircuit::identity(1, &ring);
    let xy = PlaintextCircuit::mul(&ring).compose(x.tensor(y, &ring), &ring);
    let conj_xy = PlaintextCircuit::gal(ring.galois_group().from_representative(-1), &ring.galois_group(), &ring).compose(xy.clone(&ring), &ring);
    let partial_trace_xy = PlaintextCircuit::add(&ring).compose(xy.tensor(conj_xy, &ring), &ring).compose(PlaintextCircuit::identity(2, &ring).output_twice(&ring), &ring);

    for x_e in 0..8 {
        for y_e in 0..8 {
            let x = ring.pow(ring.canonical_gen(), x_e);
            let y = ring.pow(ring.canonical_gen(), y_e);
            let xy = ring.mul_ref(&x, &y);
            let conj_xy = ring.mul(ring.pow(ring.canonical_gen(), 16 - x_e), ring.pow(ring.canonical_gen(), 16 - y_e));
            assert_el_eq!(
                &ring,
                ring.add(xy, conj_xy),
                partial_trace_xy.evaluate(&[x, y], ring.identity()).into_iter().next().unwrap()
            );
        }
    }
}

#[test]
fn test_giant_step_circuit() {
    let ring = StaticRing::<i64>::RING;
    let powers = PlaintextCircuit::identity(1, ring).tensor(PlaintextCircuit::mul(ring), ring).tensor(PlaintextCircuit::mul(ring), ring).compose(
        PlaintextCircuit::mul(ring).output_times(4, ring).tensor(PlaintextCircuit::identity(1, ring), ring),
        ring
    ).compose(
        PlaintextCircuit::identity(1, ring).output_times(3, ring),
        ring
    );
    assert_eq!(vec![4, 16, 8], powers.evaluate_no_galois(&[2], ring.identity()));

    let permuted_baby_step_dupl_input = PlaintextCircuit::constant(1, ring).tensor(PlaintextCircuit::identity(1, ring), ring).tensor(powers, ring);
    assert_eq!(vec![1, 2, 4, 16, 8], permuted_baby_step_dupl_input.evaluate_no_galois(&[2, 2], ring.identity()));

    let copy_input = PlaintextCircuit::identity(1, ring).output_twice(ring);
    assert_eq!(vec![2, 2], copy_input.evaluate_no_galois(&[2], ring.identity()));

    let permuted_baby_steps = permuted_baby_step_dupl_input.compose(copy_input, ring);
    assert_eq!(vec![1, 2, 4, 16, 8], permuted_baby_steps.evaluate_no_galois(&[2], ring.identity()));

    let baby_steps = PlaintextCircuit::select(5, &[0, 1, 2, 4, 3], ring).compose(permuted_baby_steps, ring);
    assert_eq!(1, baby_steps.input_count());
    assert_eq!(5, baby_steps.output_count());
    assert_eq!(vec![1, 2, 4, 8, 16], baby_steps.evaluate_no_galois(&[2], ring.identity()));

    let giant_steps_before_baby_steps = PlaintextCircuit::constant(1, ring).tensor(PlaintextCircuit::identity(1, ring), ring);
    let baby_and_giant_steps = PlaintextCircuit::identity(4, ring).tensor(giant_steps_before_baby_steps, ring).compose(baby_steps, ring);
    assert_eq!(vec![1, 2, 4, 8, 1, 16], baby_and_giant_steps.evaluate_no_galois(&[2], ring.identity()));
}

#[test]
fn test_serialization() {
    let ring = StaticRing::<i64>::RING;
    let x = PlaintextCircuit::linear_transform_ring(&[1], ring);
    let neg_x = PlaintextCircuit::linear_transform_ring(&[-1], ring);
    let x_neg_x = PlaintextCircuit::mul(ring).compose(x.clone(ring).tensor(neg_x, ring), ring).compose(x.output_twice(ring), ring);
    let two_minus_x_neg_x = PlaintextCircuit::add(ring).compose(x_neg_x.tensor(PlaintextCircuit::constant(2, ring), ring), ring);
    let circuit = PlaintextCircuit::square(ring).compose(two_minus_x_neg_x, ring);

    for x in -100..100 {
        assert_eq!((2 - x * x) * (2 - x * x), circuit.evaluate_no_galois(&[x], ring.identity()).into_iter().next().unwrap());
    }

    let serializer = serde_assert::Serializer::builder().is_human_readable(true).build();
    let tokens = SerializablePlaintextCircuit::new_no_galois(&ring, &circuit).serialize(&serializer).unwrap();
    let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(true).build();
    let deserialized_circuit = DeserializeSeedPlaintextCircuit::new_no_galois(&ring).deserialize(&mut deserializer).unwrap();
    assert!(deserialized_circuit == circuit);

    let serializer = serde_assert::Serializer::builder().is_human_readable(false).build();
    let tokens = SerializablePlaintextCircuit::new_no_galois(&ring, &circuit).serialize(&serializer).unwrap();
    let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(false).build();
    let deserialized_circuit = DeserializeSeedPlaintextCircuit::new_no_galois(&ring).deserialize(&mut deserializer).unwrap();
    assert!(deserialized_circuit == circuit);
}