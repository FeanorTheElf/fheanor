use std::marker::PhantomData;

use feanor_math::homomorphism::Homomorphism;
use feanor_math::ring::*;

use crate::cyclotomic::{CyclotomicGaloisGroupEl, CyclotomicRing, CyclotomicRingStore};

use super::Coefficient;

///
/// Trait for objects that can evaluate arithmetic circuits.
/// 
/// This clearly has some similarity with rings, since we can always
/// evaluate an arithmetic circuit over a ring. However, it is more general,
/// such as to allow for the evaluation of circuits on more general inputs,
/// in particular of course on encrypted data.
/// 
/// Hence, if we consider circuits to be "programs", this would be the
/// equivalent of a "virtual machine" running those programs.
/// 
/// If you want to evaluate a circuit on ring elements, use [`HomEvaluator`]
/// or [`HomEvaluatorGal`]. Otherwise, you can build a custom evaluator
/// using [`DefaultCircuitEvaluator`], for example as follows:
/// ```
/// # use fheanor::circuit::*;
/// # use fheanor::circuit::evaluator::*;
/// # use feanor_math::ring::*;
/// # use feanor_math::primitive_int::*;
/// let ring = StaticRing::<i64>::RING;
/// let square_xy = PlaintextCircuit::square(ring).compose(PlaintextCircuit::mul(ring), ring);
/// // assume that, for some reason, we want to wrap the integers in Box; instead of
/// // implementing our own ring which has boxed integers as elements, we use DefaultCircuitEvaluator
/// assert_eq!(36, *square_xy.evaluate_generic(
///     &[Box::new(2), Box::new(3)],
///     DefaultCircuitEvaluator::new(
///         /* create constant = */ |x| Box::new(x.to_ring_el(ring)),
///         /* add product = */ |base, lhs, rhs| Box::new(*base + lhs.to_ring_el(ring) * **rhs)
///     )
///         .with_mul(|lhs: Box<i64>, rhs| Box::new(*lhs * *rhs))
///         // this is optional, but may improve performance if squaring is cheaper than general multiplication
///         .with_square(|x| Box::new(ring.pow(*x, 2)))
/// ).into_iter().next().unwrap());
/// ```
/// 
pub trait CircuitEvaluator<'a, T, R: ?Sized + RingBase> {

    fn supports_gal(&self) -> bool;
    fn supports_mul(&self) -> bool;
    fn mul(&mut self, lhs: T, rhs: T) -> T;
    fn square(&mut self, val: T) -> T;
    fn constant(&mut self, constant: &'a Coefficient<R>) -> T;
    fn add_inner_prod(&mut self, dst: T, lhs: &'a [Coefficient<R>], rhs: &[T]) -> T;
    fn gal(&mut self, val: T, gs: &'a [CyclotomicGaloisGroupEl]) -> Vec<T>;
}

pub struct HomEvaluator<R, S, H>
    where R: ?Sized + RingBase,
        S: ?Sized + RingBase,
        H: Homomorphism<R, S>
{
    from: PhantomData<Box<R>>,
    to: PhantomData<Box<S>>,
    hom: H
}

impl<R, S, H> HomEvaluator<R, S, H>
    where R: ?Sized + RingBase,
        S: ?Sized + RingBase,
        H: Homomorphism<R, S>
{
    pub fn new(hom: H) -> Self {
        Self {
            from: PhantomData,
            to: PhantomData,
            hom: hom
        }
    }
}

impl<'a, R, S, H> CircuitEvaluator<'a, S::Element, R> for HomEvaluator<R, S, H>
    where R: ?Sized + RingBase,
        S: ?Sized + RingBase,
        H: Homomorphism<R, S>
{
    fn supports_gal(&self) -> bool { false }
    fn supports_mul(&self) -> bool { true }

    fn add_inner_prod(&mut self, dst: S::Element, lhs: &[Coefficient<R>], rhs: &[S::Element]) -> S::Element {
        self.hom.codomain().sum(
            [dst].into_iter().chain(lhs.iter().zip(rhs.iter()).filter_map(|(l, r)| match l {
                Coefficient::Zero => None,
                Coefficient::One => Some(self.hom.codomain().clone_el(r)),
                Coefficient::NegOne => Some(self.hom.codomain().negate(self.hom.codomain().clone_el(r))),
                Coefficient::Integer(x) => Some(self.hom.codomain().int_hom().mul_ref_fst_map(r, *x)),
                Coefficient::Other(x) => Some(self.hom.mul_ref_map(r, x))
            }))
        )
    }

    fn constant(&mut self, constant: &Coefficient<R>) -> S::Element {
        self.hom.map(constant.clone(self.hom.domain()).to_ring_el(self.hom.domain()))
    }

    fn gal(&mut self, _val: S::Element, _gs: &[CyclotomicGaloisGroupEl]) -> Vec<S::Element> {
        panic!()
    }

    fn mul(&mut self, lhs: S::Element, rhs: S::Element) -> S::Element {
        self.hom.codomain().mul(lhs, rhs)
    }

    fn square(&mut self, val: S::Element) -> S::Element {
        self.hom.codomain().pow(val, 2)
    }
}

pub struct HomEvaluatorGal<R, S, H>
    where R: ?Sized + RingBase,
        S: ?Sized + RingBase + CyclotomicRing,
        H: Homomorphism<R, S>
{
    from: PhantomData<Box<R>>,
    to: PhantomData<Box<S>>,
    hom: H
}

impl<R, S, H> HomEvaluatorGal<R, S, H>
    where R: ?Sized + RingBase,
        S: ?Sized + RingBase + CyclotomicRing,
        H: Homomorphism<R, S>
{
    pub fn new(hom: H) -> Self {
        Self {
            from: PhantomData,
            to: PhantomData,
            hom: hom
        }
    }
}

impl<'a, R, S, H> CircuitEvaluator<'a, S::Element, R> for HomEvaluatorGal<R, S, H>
    where R: ?Sized + RingBase,
        S: ?Sized + RingBase + CyclotomicRing,
        H: Homomorphism<R, S>
{
    fn supports_gal(&self) -> bool { true }
    fn supports_mul(&self) -> bool { true }

    fn add_inner_prod(&mut self, dst: S::Element, lhs: &[Coefficient<R>], rhs: &[S::Element]) -> S::Element {
        self.hom.codomain().sum(
            [dst].into_iter().chain(lhs.iter().zip(rhs.iter()).filter_map(|(l, r)| match l {
                Coefficient::Zero => None,
                Coefficient::One => Some(self.hom.codomain().clone_el(r)),
                Coefficient::NegOne => Some(self.hom.codomain().negate(self.hom.codomain().clone_el(r))),
                Coefficient::Integer(x) => Some(self.hom.codomain().int_hom().mul_ref_fst_map(r, *x)),
                Coefficient::Other(x) => Some(self.hom.mul_ref_map(r, x))
            }))
        )
    }

    fn constant(&mut self, constant: &Coefficient<R>) -> S::Element {
        self.hom.map(constant.clone(self.hom.domain()).to_ring_el(self.hom.domain()))
    }

    fn gal(&mut self, val: S::Element, gs: &[CyclotomicGaloisGroupEl]) -> Vec<S::Element> {
        self.hom.codomain().apply_galois_action_many(&val, gs)
    }

    fn mul(&mut self, lhs: S::Element, rhs: S::Element) -> S::Element {
        self.hom.codomain().mul(lhs, rhs)
    }

    fn square(&mut self, val: S::Element) -> S::Element {
        self.hom.codomain().pow(val, 2)
    }
}

///
/// A "compile time [`Option`]".
/// 
/// In other words, this trait describes types that either store
/// a [`Possibly::T`] or a empty, but may be restricted to one of the
/// two possibilities. 
/// 
pub trait Possibly {
    type T;
    const IS_PRESENT: bool;

    fn get_mut(&mut self) -> &mut Self::T
        where Self: Possibly<IS_PRESENT = true>;
    fn get(&self) -> &Self::T
        where Self: Possibly<IS_PRESENT = true>;
    fn get_mut_option(&mut self) -> Option<&mut Self::T>;
    fn get_option(&self) -> Option<&Self::T>;
}

pub struct Present<T> {
    t: T
}

impl<T> Possibly for Present<T> {
    type T = T;
    const IS_PRESENT: bool = true;

    fn get_mut(&mut self) -> &mut Self::T {
        &mut self.t
    }
    fn get(&self) -> &Self::T {
        &self.t
    }
    fn get_mut_option(&mut self) -> Option<&mut Self::T> {
        Some(self.get_mut())
    }
    fn get_option(&self) -> Option<&Self::T> {
        Some(self.get())
    }
}

pub struct Absent<T> {
    t: PhantomData<T>
}

impl<T> Possibly for Absent<T> {
    type T = T;
    const IS_PRESENT: bool = false;

    fn get_mut(&mut self) -> &mut Self::T
        where Self: Possibly<IS_PRESENT = true>
    {
        unreachable!()
    }
    fn get(&self) -> &Self::T
        where Self: Possibly<IS_PRESENT = true>
    {
        unreachable!()
    }
    fn get_mut_option(&mut self) -> Option<&mut Self::T> {
        None
    }
    fn get_option(&self) -> Option<&Self::T> {
        None
    }
}

pub struct DefaultCircuitEvaluator<'a, T, R: ?Sized + RingBase, FnMul, FnConst, FnAddProd, FnSquare, FnGal, FnInnerProd>
    where FnMul: Possibly, FnMul::T: FnMut(T, T) -> T,
        FnConst: FnMut(&'a Coefficient<R>) -> T,
        FnAddProd: Possibly, FnAddProd::T: FnMut(T, &'a Coefficient<R>, &T) -> T,
        FnSquare: Possibly, FnSquare::T: FnMut(T) -> T,
        FnGal: Possibly, FnGal::T: FnMut(T, &'a [CyclotomicGaloisGroupEl]) -> Vec<T>,
        FnInnerProd: Possibly, FnInnerProd::T: FnMut(T, &'a [Coefficient<R>], &[T]) -> T,
        R: 'a
{
    element: PhantomData<T>,
    ring: PhantomData<&'a R>,
    mul: FnMul,
    constant: FnConst,
    add_prod: FnAddProd,
    square: FnSquare,
    gal: FnGal,
    inner_product: FnInnerProd
}

impl<'a, T, R: ?Sized + RingBase, FnConst, FnAddProd> DefaultCircuitEvaluator<'a, T, R, Absent<fn(T, T) -> T>, FnConst, Present<FnAddProd>, Absent<fn(T) -> T>, Absent<fn(T, &[CyclotomicGaloisGroupEl]) -> Vec<T>>, Absent<fn(T, &[Coefficient<R>], &[T]) -> T>>
    where FnConst: FnMut(&'a Coefficient<R>) -> T,
        FnAddProd: FnMut(T, &'a Coefficient<R>, &T) -> T,
        R: 'a
{
    pub fn new(constant: FnConst, add_prod: FnAddProd) -> Self {
        Self {
            element: PhantomData,
            add_prod: Present { t: add_prod },
            constant: constant,
            mul: Absent { t: PhantomData },
            gal: Absent { t: PhantomData },
            inner_product: Absent { t: PhantomData },
            square: Absent { t: PhantomData },
            ring: PhantomData
        }
    }
}

impl<'a, T, R: ?Sized + RingBase, FnMul, FnConst, FnAddProd, FnSquare, FnGal, FnInnerProd> CircuitEvaluator<'a, T, R> for DefaultCircuitEvaluator<'a, T, R, FnMul, FnConst, FnAddProd, FnSquare, FnGal, FnInnerProd>
    where FnMul: Possibly, FnMul::T: FnMut(T, T) -> T,
        FnConst: FnMut(&'a Coefficient<R>) -> T,
        FnAddProd: Possibly, FnAddProd::T: FnMut(T, &'a Coefficient<R>, &T) -> T,
        FnSquare: Possibly, FnSquare::T: FnMut(T) -> T,
        FnGal: Possibly, FnGal::T: FnMut(T, &'a [CyclotomicGaloisGroupEl]) -> Vec<T>,
        FnInnerProd: Possibly, FnInnerProd::T: FnMut(T, &'a [Coefficient<R>], &[T]) -> T,
        R: 'a,
        T: 'a
{
    fn supports_gal(&self) -> bool { <FnGal as Possibly>::IS_PRESENT }
    fn supports_mul(&self) -> bool { <FnMul as Possibly>::IS_PRESENT }

    fn add_inner_prod(&mut self, dst: T, lhs: &'a [Coefficient<R>], rhs: &[T]) -> T {
        assert_eq!(lhs.len(), rhs.len());
        if let Some(inner_prod) = self.inner_product.get_mut_option() {
            return inner_prod(dst, lhs, rhs);
        } else {
            let mut current = dst;
            for i in 0..lhs.len() {
                current = self.add_prod.get_mut_option().unwrap()(current, &lhs[i], &rhs[i]);
            }
            return current;
        }
    }

    fn mul(&mut self, lhs: T, rhs: T) -> T {
        if let Some(mul) = self.mul.get_mut_option() {
            mul(lhs, rhs)
        } else {
            panic!("Circuit contains multiplication gates, but no galois function has been specified during evaluator creation")
        }
    }

    fn constant(&mut self, constant: &'a Coefficient<R>) -> T {
        (self.constant)(constant)
    }

    fn gal(&mut self, val: T, gs: &'a [CyclotomicGaloisGroupEl]) -> Vec<T> {
        if let Some(gal) = self.gal.get_mut_option() {
            gal(val, gs)
        } else {
            panic!("Circuit contains Galois gates, but no galois function has been specified during evaluator creation")
        }
    }

    fn square(&mut self, val: T) -> T {
        if let Some(square) = self.square.get_mut_option() {
            square(val)
        } else {
            let zero = (self.constant)(&Coefficient::Zero);
            let val_copy = self.add_inner_prod(zero, &[Coefficient::One], std::slice::from_ref(&val));
            self.mul(val, val_copy)
        }
    }
}

impl<'a, T, R: ?Sized + RingBase, FnMul, FnConst, FnAddProd, FnGal, FnInnerProd> DefaultCircuitEvaluator<'a, T, R, FnMul, FnConst, FnAddProd, Absent<fn(T) -> T>, FnGal, FnInnerProd>
    where FnMul: Possibly, FnMul::T: FnMut(T, T) -> T,
        FnConst: FnMut(&'a Coefficient<R>) -> T,
        FnAddProd: Possibly, FnAddProd::T: FnMut(T, &'a Coefficient<R>, &T) -> T,
        FnGal: Possibly, FnGal::T: FnMut(T, &'a [CyclotomicGaloisGroupEl]) -> Vec<T>,
        FnInnerProd: Possibly, FnInnerProd::T: FnMut(T, &'a [Coefficient<R>], &[T]) -> T,
        R: 'a,
        T: 'a
{
    pub fn with_square<FnSquare>(self, square: FnSquare) -> DefaultCircuitEvaluator<'a, T, R, FnMul, FnConst, FnAddProd, Present<FnSquare>, FnGal, FnInnerProd>
        where FnSquare: FnMut(T) -> T
    {
        DefaultCircuitEvaluator {
            add_prod: self.add_prod,
            constant: self.constant,
            element: self.element,
            gal: self.gal,
            inner_product: self.inner_product,
            mul: self.mul,
            ring: self.ring,
            square: Present { t: square }
        }
    }
}

impl<'a, T, R: ?Sized + RingBase, FnSquare, FnConst, FnAddProd, FnGal, FnInnerProd> DefaultCircuitEvaluator<'a, T, R, Absent<fn(T, T) -> T>, FnConst, FnAddProd, FnSquare, FnGal, FnInnerProd>
    where FnSquare: Possibly, FnSquare::T: FnMut(T) -> T,
        FnConst: FnMut(&'a Coefficient<R>) -> T,
        FnAddProd: Possibly, FnAddProd::T: FnMut(T, &'a Coefficient<R>, &T) -> T,
        FnGal: Possibly, FnGal::T: FnMut(T, &'a [CyclotomicGaloisGroupEl]) -> Vec<T>,
        FnInnerProd: Possibly, FnInnerProd::T: FnMut(T, &'a [Coefficient<R>], &[T]) -> T,
        R: 'a,
        T: 'a
{
    pub fn with_mul<FnMul>(self, mul: FnMul) -> DefaultCircuitEvaluator<'a, T, R, Present<FnMul>, FnConst, FnAddProd, FnSquare, FnGal, FnInnerProd>
        where FnMul: FnMut(T, T) -> T
    {
        DefaultCircuitEvaluator {
            add_prod: self.add_prod,
            constant: self.constant,
            element: self.element,
            gal: self.gal,
            inner_product: self.inner_product,
            mul: Present { t: mul },
            ring: self.ring,
            square: self.square
        }
    }
}

impl<'a, T, R: ?Sized + RingBase, FnMul, FnConst, FnAddProd, FnSquare, FnInnerProd> DefaultCircuitEvaluator<'a, T, R, FnMul, FnConst, FnAddProd, FnSquare, Absent<fn(T, &[CyclotomicGaloisGroupEl]) -> Vec<T>>, FnInnerProd>
    where FnMul: Possibly, FnMul::T: FnMut(T, T) -> T,
        FnConst: FnMut(&'a Coefficient<R>) -> T,
        FnAddProd: Possibly, FnAddProd::T: FnMut(T, &'a Coefficient<R>, &T) -> T,
        FnSquare: Possibly, FnSquare::T: FnMut(T) -> T,
        FnInnerProd: Possibly, FnInnerProd::T: FnMut(T, &'a [Coefficient<R>], &[T]) -> T,
        R: 'a,
        T: 'a
{
    pub fn with_gal<FnGal>(self, gal: FnGal) -> DefaultCircuitEvaluator<'a, T, R, FnMul, FnConst, FnAddProd, FnSquare, Present<FnGal>, FnInnerProd>
        where FnGal: FnMut(T, &'a [CyclotomicGaloisGroupEl]) -> Vec<T>
    {
        DefaultCircuitEvaluator {
            add_prod: self.add_prod,
            constant: self.constant,
            element: self.element,
            gal: Present { t: gal },
            inner_product: self.inner_product,
            mul: self.mul,
            ring: self.ring,
            square: self.square
        }
    }
}

impl<'a, T, R: ?Sized + RingBase, FnMul, FnConst, FnAddProd, FnSquare, FnGal> DefaultCircuitEvaluator<'a, T, R, FnMul, FnConst, FnAddProd, FnSquare, FnGal, Absent<fn(T, &[Coefficient<R>], &[T]) -> T>>
    where FnMul: Possibly, FnMul::T: FnMut(T, T) -> T,
        FnConst: FnMut(&'a Coefficient<R>) -> T,
        FnAddProd: Possibly, FnAddProd::T: FnMut(T, &'a Coefficient<R>, &T) -> T,
        FnSquare: Possibly, FnSquare::T: FnMut(T) -> T,
        FnGal: Possibly, FnGal::T: FnMut(T, &'a [CyclotomicGaloisGroupEl]) -> Vec<T>,
        R: 'a,
        T: 'a
{
    pub fn with_inner_product<FnInnerProd>(self, inner_product: FnInnerProd) -> DefaultCircuitEvaluator<'a, T, R, FnMul, FnConst, FnAddProd, FnSquare, FnGal, Present<FnInnerProd>>
        where FnInnerProd: FnMut(T, &'a [Coefficient<R>], &[T]) -> T
    {
        DefaultCircuitEvaluator {
            add_prod: self.add_prod,
            constant: self.constant,
            element: self.element,
            gal: self.gal,
            inner_product: Present { t: inner_product },
            mul: self.mul,
            ring: self.ring,
            square: self.square
        }
    }
}
