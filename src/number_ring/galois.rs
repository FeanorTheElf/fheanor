use std::fmt::Debug;
use std::marker::PhantomData;

use feanor_math::algorithms::discrete_log::{multiplicative_order, Subgroup};
use feanor_math::algorithms::eea::inv_crt;
use feanor_math::algorithms::int_factor::{factor, is_prime_power};
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::group::{AbelianGroupBase, AbelianGroupStore, GroupValue, MultGroup, MultGroupEl, SerializableElementGroup};
use feanor_math::integer::int_cast;
use feanor_math::rings::finite::FiniteRingStore;
use feanor_math::rings::zn::zn_64::{Zn, ZnEl};
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnRingStore;
use feanor_serde::newtype_struct::{DeserializeSeedNewtypeStruct, SerializableNewtypeStruct};
use serde::de::DeserializeSeed;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{euler_phi, ZZbig, ZZi64};

///
/// Represents the Galois group of the `m`-th cyclotomic number field by
/// its isomorphic subgroup of `(Z/mZ)*`.
/// 
#[derive(Clone, Serialize, Deserialize)]
pub struct CyclotomicGaloisGroupBase {
    group: MultGroup<Zn>,
    order: usize
}

pub type CyclotomicGaloisGroup = GroupValue<CyclotomicGaloisGroupBase>;

impl CyclotomicGaloisGroupBase {

    pub fn new(m: u64) -> GroupValue<Self> {
        let ring = Zn::new(m);
        let group = MultGroup::new(ring);
        let order = euler_phi(&factor(ZZi64, m as i64)) as usize;
        return GroupValue::from(Self {
            order: order,
            group: group
        });
    }

    pub fn subgroup<I>(self, generators: I) -> Subgroup<CyclotomicGaloisGroup>
        where I: IntoIterator<Item = GaloisGroupEl>
    {
        let order = int_cast(self.order as i64, ZZbig, ZZi64);
        Subgroup::new(GroupValue::from(self), order, generators.into_iter().collect())
    }

    pub fn full_subgroup(self) -> Subgroup<CyclotomicGaloisGroup> {
        let order = int_cast(self.order as i64, ZZbig, ZZi64);
        let mut generators = Vec::new();
        for (p, e) in factor(ZZi64, self.m() as i64) {
            let pe = ZZi64.pow(p, e);
            let rest = ZZi64.checked_div(&(self.m() as i64), &pe).unwrap();
            if p == 2 {
                generators.push(inv_crt(-1, 1, &pe, &rest, ZZi64));
                generators.push(inv_crt(5, 1, &pe, &rest, ZZi64));
            } else {
                let Zpe = Zn::new(pe as u64);
                let gen = get_multiplicative_generator(Zpe);
                generators.push(inv_crt(Zpe.smallest_lift(gen), 1, &pe, &rest, ZZi64));
            }
        }
        return Subgroup::new(GroupValue::from(self.clone()), order, generators.into_iter().map(|x| self.from_ring_el(self.underlying_ring().coerce(&ZZi64, x))).collect());
    }

    ///
    /// Returns the ring `Z/mZ` whose units form this group.
    /// 
    pub fn underlying_ring(&self) -> &Zn {
        self.group.underlying_ring()
    }

    ///
    /// Interprets a group element as ring element of `Z/mZ`.
    /// 
    pub fn as_ring_el<'a>(&self, value: &'a GaloisGroupEl) -> &'a ZnEl {
        self.group.as_ring_el(&value.value)
    }

    ///
    /// Converts a ring element of `Z/mZ` to a group element of this group.
    /// Panics if the ring element is not a unit, i.e. in `(Z/mZ)*`.
    /// 
    pub fn from_ring_el(&self, el: ZnEl) -> GaloisGroupEl {
        GaloisGroupEl { value: self.group.from_ring_el(el).unwrap() }
    }

    ///
    /// Returns `m` such that this group is isomorphic to `(Z/mZ)*`.
    /// 
    /// Note that `m` is not necessarily unique, as for odd `m`, we have
    /// `(Z/mZ)* ~ (Z/2mZ)*`. In this case, an arbitrary suitable `m`
    /// will be returned. The same `m` is returned during the whole lifetime
    /// of the object, and all functionality that depends on `m` must use
    /// this value of `m`.
    /// 
    pub fn m(&self) -> u64 {
        *self.underlying_ring().modulus() as u64
    }

    ///
    /// Returns the order of a group element, i.e. the smallest `k` such that
    /// `value^k = 1`.
    /// 
    pub fn element_order(&self, value: &GaloisGroupEl) -> usize {
        multiplicative_order(
            *self.as_ring_el(value),
            self.underlying_ring()
        ) as usize
    }

    ///
    /// Interprets `x` as a representative for an element in `Z/mZ`, and converts
    /// it into a group element. Panics if `x` is not a unit in `Z/mZ`, i.e. not
    /// in `(Z/mZ)*`.
    /// 
    pub fn from_representative(&self, x: i64) -> GaloisGroupEl {
        self.from_ring_el(self.underlying_ring().coerce(&ZZi64, x))
    }

    ///
    /// Returns the smallest nonnegative integer that represents the coset of `x`
    /// in `Z/mZ`.
    /// 
    pub fn representative(&self, x: &GaloisGroupEl) -> u64 {
        self.underlying_ring().smallest_positive_lift(*self.as_ring_el(x)) as u64
    }

    ///
    /// Returns the number of elements in this finite group.
    /// 
    pub fn group_order(&self) -> usize {
        self.order
    }
}

pub trait CyclotomicGaloisGroupOps: AbelianGroupStore {

    fn underlying_ring(&self) -> &Zn;

    fn as_ring_el<'a>(&self, value: &'a GaloisGroupEl) -> &'a ZnEl;

    fn from_ring_el(&self, el: ZnEl) -> GaloisGroupEl;

    ///
    /// Returns a positive integer `m` such that this group embeds into `(Z/mZ)*`.
    /// 
    /// This is not necessarily the minimal such `m`. The same `m` is returned during
    /// the whole lifetime of the object, and all functionality that depends on `m`
    /// must use this value of `m`.
    /// 
    fn m(&self) -> u64;

    fn element_order(&self, value: &GaloisGroupEl) -> usize;

    fn from_representative(&self, x: i64) -> GaloisGroupEl;

    fn representative(&self, x: &GaloisGroupEl) -> u64;

    fn group_order(&self) -> usize;

    ///
    /// Returns whether the embedding of this group into `(Z/mZ)*` is
    /// an isomorphism, where `m` is the positive integer given by
    /// [`CyclotomicGaloisGroupOps::m()`].
    /// 
    fn is_full_cyclotomic_galois_group(&self) -> bool;
}

impl CyclotomicGaloisGroupOps for CyclotomicGaloisGroup {

    fn underlying_ring(&self) -> &Zn {
        self.get_group().underlying_ring()
    }

    fn as_ring_el<'a>(&self, value: &'a GaloisGroupEl) -> &'a ZnEl {
        self.get_group().as_ring_el(value)
    }

    fn from_ring_el(&self, el: ZnEl) -> GaloisGroupEl {
        self.get_group().from_ring_el(el)
    }

    fn m(&self) -> u64 {
        self.get_group().m()
    }

    fn element_order(&self, value: &GaloisGroupEl) -> usize {
        self.get_group().element_order(value)
    }

    fn from_representative(&self, x: i64) -> GaloisGroupEl {
        self.get_group().from_representative(x)
    }

    fn representative(&self, x: &GaloisGroupEl) -> u64 {
        self.get_group().representative(x)
    }

    fn group_order(&self) -> usize {
        self.get_group().group_order()
    }
    
    fn is_full_cyclotomic_galois_group(&self) -> bool {
        true
    }
}

impl CyclotomicGaloisGroupOps for Subgroup<CyclotomicGaloisGroup> {

    fn as_ring_el<'a>(&self, value: &'a GaloisGroupEl) -> &'a ZnEl {
        self.parent().as_ring_el(value)
    }

    fn element_order(&self, value: &GaloisGroupEl) -> usize {
        self.parent().element_order(value)
    }

    fn from_representative(&self, x: i64) -> GaloisGroupEl {
        let result = self.parent().from_representative(x);
        assert!(self.contains(&result));
        return result;
    }

    fn from_ring_el(&self, el: ZnEl) -> GaloisGroupEl {
        let result = self.parent().from_ring_el(el);
        assert!(self.contains(&result));
        return result;
    }

    fn m(&self) -> u64 {
        self.parent().m()
    }

    fn group_order(&self) -> usize {
        int_cast(self.subgroup_order(), ZZi64, ZZbig) as usize
    }

    fn representative(&self, x: &GaloisGroupEl) -> u64 {
        self.parent().representative(x)
    }

    fn underlying_ring(&self) -> &Zn {
        self.parent().underlying_ring()
    }

    fn is_full_cyclotomic_galois_group(&self) -> bool {
        ZZbig.eq_el(&self.subgroup_order(), &int_cast(self.parent().group_order() as i64, ZZbig, ZZi64))
    }
}

impl PartialEq for CyclotomicGaloisGroupBase {

    fn eq(&self, other: &Self) -> bool {
        self.group.get_group() == other.group.get_group()
    }
}

impl Eq for CyclotomicGaloisGroupBase {}

impl AbelianGroupBase for CyclotomicGaloisGroupBase {

    type Element = GaloisGroupEl;

    fn clone_el(&self, x: &Self::Element) -> Self::Element {
        x.clone()
    }

    fn eq_el(&self, lhs: &Self::Element, rhs: &Self::Element) -> bool {
        self.group.eq_el(&lhs.value, &rhs.value)
    }

    fn hash<H: std::hash::Hasher>(&self, x: &Self::Element, hasher: &mut H) {
        self.group.hash(&x.value, hasher)
    }

    fn inv(&self, x: &Self::Element) -> Self::Element {
        GaloisGroupEl { value: self.group.inv(&x.value) }
    }

    fn op(&self, lhs: Self::Element, rhs: Self::Element) -> Self::Element {
        GaloisGroupEl { value: self.group.op(lhs.value, rhs.value) }
    }

    fn identity(&self) -> Self::Element {
        GaloisGroupEl { value: self.group.identity() }
    }
}

impl Debug for CyclotomicGaloisGroupBase {

    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(Z/{}Z)*", self.underlying_ring().modulus())
    }
}

impl SerializableElementGroup for CyclotomicGaloisGroupBase {

    fn serialize<S>(&self, el: &Self::Element, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        SerializableNewtypeStruct::new("GaloisGroupEl", self.representative(el)).serialize(serializer)
    }

    fn deserialize<'de, D>(&self, deserializer: D) -> Result<Self::Element, D::Error>
        where D: Deserializer<'de>
    {
        DeserializeSeedNewtypeStruct::new("GaloisGroupEl", PhantomData::<u64>).deserialize(deserializer).map(|x| self.from_representative(x as i64))
    }
}

#[derive(Debug, Clone)]
pub struct GaloisGroupEl {
    value: MultGroupEl<Zn>
}

pub fn get_multiplicative_generator(ring: Zn) -> ZnEl {
    let (p, e) = is_prime_power(ZZi64, ring.modulus()).unwrap();
    assert!(*ring.modulus() % 2 == 1, "for even m, Z/mZ* is either equal to Z/(m/2)Z* or not cyclic");
    let mut rng = oorandom::Rand64::new(ring.integer_ring().default_hash(ring.modulus()) as u128);
    let order = ZZi64.pow(p, e - 1) * (p - 1);
    let order_factorization = factor(&ZZi64, order);
    'test_generator: loop {
        let potential_generator = ring.random_element(|| rng.rand_u64());
        if !ring.is_unit(&potential_generator) {
            continue 'test_generator;
        }
        for (p, _) in &order_factorization {
            if ring.is_one(&ring.pow(potential_generator, (order / p) as usize)) {
                continue 'test_generator;
            }
        }
        return potential_generator;
    }
}
