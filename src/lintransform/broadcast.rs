use std::alloc::Allocator;
use std::cell::RefCell;

use feanor_math::homomorphism::Homomorphism;
use feanor_math::primitive_int::StaticRing;
use feanor_math::algorithms::sqr_mul::generic_pow_shortest_chain_table;
use feanor_math::rings::zn::zn_64::{Zn, ZnEl};
use feanor_math::assert_el_eq;
use feanor_math::ring::*;

use crate::cyclotomic::{CyclotomicGaloisGroup, CyclotomicGaloisGroupEl};
use crate::number_ring::odd_cyclotomic::CompositeCyclotomicNumberRing;
use crate::number_ring::{HECyclotomicNumberRing, HENumberRing};
use crate::number_ring::quotient::{NumberRingQuotient, NumberRingQuotientBase};
use crate::number_ring::hypercube::{DefaultHypercube, HypercubeIsomorphism, HypercubeStructure};

pub struct Broadcast1d<NumberRing, A>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone
{
    shift_elements: Vec<CyclotomicGaloisGroupEl>,
    clear_slots_factor: El<NumberRingQuotient<NumberRing, Zn, A>>,
    number_ring: NumberRing
}

impl<NumberRing, A> Broadcast1d<NumberRing, A>
    where NumberRing: HECyclotomicNumberRing + Clone,
        A: Allocator + Clone
{
    pub fn new(H: &DefaultHypercube<NumberRing, A>, dim_index: usize) -> Self {
        Self {
            clear_slots_factor: H.from_slot_values(H.hypercube().hypercube_iter(|slot_index| if slot_index[dim_index] == 0 {
                H.slot_ring().one()
            } else {
                H.slot_ring().zero()
            })),
            shift_elements: (0..H.hypercube().m(dim_index)).map(|i| H.hypercube().map_1d(dim_index, i as i64)).collect::<Vec<_>>(),
            number_ring: H.ring().get_ring().number_ring().clone()
        }
    }
}

impl<NumberRing, A> HELinearTransform<NumberRing, A> for Broadcast1d<NumberRing, A>
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone
{
    fn number_ring(&self) -> &NumberRing {
        &self.number_ring
    }

    fn evaluate_generic<T, AddFn, ScaleFn, ApplyGaloisFn, CloneFn>(
            &self,
            input: T,
            add_fn: AddFn,
            mut scale_fn: ScaleFn,
            apply_galois_fn: ApplyGaloisFn,
            clone_fn: CloneFn
        ) -> T
            where AddFn: FnMut(T, &T) -> T,
                ScaleFn: FnMut(T, &El<NumberRingQuotient<NumberRing, Zn, A>>) -> T,
                ApplyGaloisFn: FnMut(T, &[CyclotomicGaloisGroupEl]) -> Vec<T>,
                CloneFn: FnMut(&T) -> T
    {
        let add_fn = RefCell::new(add_fn);
        let apply_galois_fn = RefCell::new(apply_galois_fn);
        let clone_fn = RefCell::new(clone_fn);
        generic_pow_shortest_chain_table::<_, _, _, _, _, !>(
            (1, Some(scale_fn(input, &self.clear_slots_factor))), 
            &(self.shift_elements.len() as i64), 
            StaticRing::<i64>::RING, 
            |(i, x)| {
                if let Some(x) = x {
                    Ok((2 * i, Some(add_fn.borrow_mut()(apply_galois_fn.borrow_mut()(clone_fn.borrow_mut()(x), &vec![self.shift_elements[*i]]).into_iter().next().unwrap(), x))))
                } else {
                    assert_eq!(0, *i);
                    Ok((0, None))
                }
            }, |(i, x), (j, y)| {
                if x.is_none() {
                    assert_eq!(0, *i);
                    return Ok((i + j, y.as_ref().map(|y| clone_fn.borrow_mut()(y))));
                } else if y.is_none() {
                    assert_eq!(0, *j);
                    return Ok((i + j, x.as_ref().map(|x| clone_fn.borrow_mut()(x))));
                }
                Ok((i + j, Some(add_fn.borrow_mut()(apply_galois_fn.borrow_mut()(clone_fn.borrow_mut()(x.as_ref().unwrap()), &vec![self.shift_elements[*j]]).into_iter().next().unwrap(), y.as_ref().unwrap()))))
            }, 
            |(i, x)| (*i, x.as_ref().map(|x| clone_fn.borrow_mut()(x))), 
            (0, None)
        ).unwrap_or_else(|x| x).1.unwrap()
    }
}

#[test]
fn test_broadcast() {
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(5 * 7), 11);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);
    assert_eq!(7, H.hypercube().factor_of_n(0).unwrap());
    assert_eq!(2, H.hypercube().m(0));
    assert_eq!(5, H.hypercube().factor_of_n(1).unwrap());
    assert_eq!(4, H.hypercube().m(1));

    let input = H.from_slot_values((0..8).map(|i| H.slot_ring().int_hom().map(i)));
    let expected = H.from_slot_values((0..8).map(|i| H.slot_ring().int_hom().map(i % 4)));
    let broadcast = Broadcast1d::new(&H, 0);
    let actual = broadcast.evaluate(&ring, ring.clone_el(&input));
    assert_el_eq!(H.ring(), expected, actual);

    let expected = H.from_slot_values((0..8).map(|i| H.slot_ring().int_hom().map((i / 4) * 4)));
    let broadcast = Broadcast1d::new(&H, 1);
    let actual = broadcast.evaluate(&ring, input);
    assert_el_eq!(H.ring(), expected, actual);
}