use std::marker::PhantomData;

use feanor_math::algorithms::matmul::ComputeInnerProduct;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::generic_impls::map_from_integer_ring;
use feanor_math::ring::*;

use super::Coefficient;
use crate::ZZbig;
use crate::number_ring::galois::*;
use crate::number_ring::{NumberRingQuotient, NumberRingQuotientStore};

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
/// or [`HomEvaluatorGal`]. Otherwise, you can build a custom evaluator.
pub trait CircuitEvaluator<'a, T, R: ?Sized + RingBase> {
    fn supports_gal(&self) -> bool;
    fn supports_mul(&self) -> bool;
    fn mul(&mut self, lhs: T, rhs: T) -> T;
    fn square(&mut self, val: T) -> T;
    fn gal(&mut self, val: T, gs: &'a [GaloisGroupEl]) -> Vec<T>;
    fn add_constant(&mut self, val: T, constant: &'a Coefficient<R>) -> T;
    fn inner_prod<'b, I>(&mut self, data: I) -> T
    where
        I: Iterator<Item = (&'a Coefficient<R>, &'b T)>,
        R: 'a,
        T: 'b;
}

pub struct HomEvaluator<R, S, H>
where
    R: ?Sized + RingBase,
    S: ?Sized + RingBase,
    H: Homomorphism<R, S>,
{
    from: PhantomData<Box<R>>,
    to: PhantomData<Box<S>>,
    hom: H,
}

impl<R, S, H> HomEvaluator<R, S, H>
where
    R: ?Sized + RingBase,
    S: ?Sized + RingBase,
    H: Homomorphism<R, S>,
{
    pub fn new(hom: H) -> Self {
        Self {
            from: PhantomData,
            to: PhantomData,
            hom,
        }
    }
}

impl<'a, R, S, H> CircuitEvaluator<'a, S::Element, R> for HomEvaluator<R, S, H>
where
    R: ?Sized + RingBase,
    S: ?Sized + RingBase,
    H: Homomorphism<R, S>,
{
    fn supports_gal(&self) -> bool { false }
    fn supports_mul(&self) -> bool { true }

    fn inner_prod<'b, I>(&mut self, data: I) -> S::Element
    where
        I: Iterator<Item = (&'a Coefficient<R>, &'b S::Element)>,
        R: 'a,
        S::Element: 'b,
    {
        let result = ComputeInnerProduct::inner_product_ref_fst(
            self.hom.codomain().get_ring(),
            data.filter_map(|(l, r)| match l {
                Coefficient::Zero => None,
                Coefficient::One => Some((r, self.hom.codomain().one())),
                Coefficient::NegOne => Some((r, self.hom.codomain().neg_one())),
                Coefficient::Integer(x) => {
                    Some((r, map_from_integer_ring(ZZbig, self.hom.codomain(), ZZbig.clone_el(x))))
                }
                Coefficient::Other(x) => Some((r, self.hom.map_ref(x))),
            }),
        );
        return result;
    }

    fn add_constant(&mut self, mut val: S::Element, constant: &'a Coefficient<R>) -> S::Element {
        self.hom.codomain().add_assign(
            &mut val,
            self.hom
                .map(constant.clone(self.hom.domain()).to_ring_el(self.hom.domain())),
        );
        return val;
    }

    fn gal(&mut self, _val: S::Element, _gs: &[GaloisGroupEl]) -> Vec<S::Element> { panic!() }

    fn mul(&mut self, lhs: S::Element, rhs: S::Element) -> S::Element {
        let result = self.hom.codomain().mul(lhs, rhs);
        return result;
    }

    fn square(&mut self, val: S::Element) -> S::Element {
        let result = self.hom.codomain().pow(val, 2);
        return result;
    }
}

pub struct HomEvaluatorGal<R, S, H>
where
    R: ?Sized + RingBase,
    S: ?Sized + RingBase + NumberRingQuotient,
    H: Homomorphism<R, S>,
{
    base: HomEvaluator<R, S, H>,
}

impl<R, S, H> HomEvaluatorGal<R, S, H>
where
    R: ?Sized + RingBase,
    S: ?Sized + RingBase + NumberRingQuotient,
    H: Homomorphism<R, S>,
{
    pub fn new(hom: H) -> Self {
        Self {
            base: HomEvaluator::new(hom),
        }
    }
}

impl<'a, R, S, H> CircuitEvaluator<'a, S::Element, R> for HomEvaluatorGal<R, S, H>
where
    R: ?Sized + RingBase,
    S: ?Sized + RingBase + NumberRingQuotient,
    H: Homomorphism<R, S>,
{
    fn supports_gal(&self) -> bool { true }
    fn supports_mul(&self) -> bool { true }

    fn inner_prod<'b, I>(&mut self, data: I) -> S::Element
    where
        I: Iterator<Item = (&'a Coefficient<R>, &'b S::Element)>,
        R: 'a,
        S::Element: 'b,
    {
        self.base.inner_prod(data)
    }

    fn add_constant(&mut self, val: S::Element, constant: &'a Coefficient<R>) -> S::Element {
        self.base.add_constant(val, constant)
    }

    fn gal(&mut self, val: S::Element, gs: &[GaloisGroupEl]) -> Vec<S::Element> {
        self.base.hom.codomain().apply_galois_action_many(&val, gs)
    }

    fn mul(&mut self, lhs: S::Element, rhs: S::Element) -> S::Element { self.base.mul(lhs, rhs) }

    fn square(&mut self, val: S::Element) -> S::Element { self.base.square(val) }
}
