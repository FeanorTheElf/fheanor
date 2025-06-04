use std::fmt::Debug;
use std::marker::PhantomData;

use feanor_math::algorithms::discrete_log::order;
use feanor_math::ring::*;
use feanor_math::delegate;
use feanor_math::rings::extension::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::rings::zn::*;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::serialization::*;
use feanor_math::wrapper::RingElementWrapper;
use feanor_math::divisibility::DivisibilityRingStore;
use serde::de::DeserializeSeed;
use serde::Deserialize;
use serde::Serialize;

use crate::euler_phi;
use crate::ZZi64;

///
/// Represents the group `(Z/mZ)^*`, which is isomorphic to the Galois
/// group of a cyclotomic number field.
/// 
#[derive(Clone, Copy)]
pub struct CyclotomicGaloisGroup {
    ring: Zn,
    order: usize
}

impl PartialEq for CyclotomicGaloisGroup {

    fn eq(&self, other: &Self) -> bool {
        self.ring.get_ring() == other.ring.get_ring()
    }
}

impl Eq for CyclotomicGaloisGroup {}

impl CyclotomicGaloisGroup {

    pub fn new(m: u64) -> Self {
        Self {
            ring: Zn::new(m),
            order: euler_phi(&factor(ZZi64, m as i64)) as usize
        }
    }

    pub fn identity(&self) -> CyclotomicGaloisGroupEl {
        CyclotomicGaloisGroupEl { value: self.ring.one() }
    }

    pub fn mul(&self, lhs: CyclotomicGaloisGroupEl, rhs: CyclotomicGaloisGroupEl) -> CyclotomicGaloisGroupEl {
        CyclotomicGaloisGroupEl { value: self.ring.mul(lhs.value, rhs.value) }
    }

    pub fn invert(&self, value: CyclotomicGaloisGroupEl) -> CyclotomicGaloisGroupEl {
        CyclotomicGaloisGroupEl { value: self.ring.invert(&value.value).unwrap() }
    }

    pub fn representative(&self, value: CyclotomicGaloisGroupEl) -> usize {
        self.ring.smallest_positive_lift(value.value) as usize
    }

    pub fn from_representative(&self, value: i64) -> CyclotomicGaloisGroupEl {
        self.from_ring_el(self.ring.coerce(&ZZi64, value))
    }

    pub fn from_ring_el(&self, value: ZnEl) -> CyclotomicGaloisGroupEl {
        assert!(self.ring.is_unit(&value));
        CyclotomicGaloisGroupEl { value }
    }

    pub fn negate(&self, value: CyclotomicGaloisGroupEl) -> CyclotomicGaloisGroupEl {
        CyclotomicGaloisGroupEl { value: self.ring.negate(value.value) }
    }

    pub fn prod<I>(&self, it: I) -> CyclotomicGaloisGroupEl
        where I: IntoIterator<Item = CyclotomicGaloisGroupEl>
    {
        it.into_iter().fold(self.identity(), |a, b| self.mul(a, b))
    }

    pub fn pow(&self, base: CyclotomicGaloisGroupEl, power: i64) -> CyclotomicGaloisGroupEl {
        if power >= 0 {
            CyclotomicGaloisGroupEl { value: self.ring.pow(base.value, power as usize) }
        } else {
            self.invert(CyclotomicGaloisGroupEl { value: self.ring.pow(base.value, (-power) as usize) })
        }
    }

    pub fn is_identity(&self, value: CyclotomicGaloisGroupEl) -> bool {
        self.ring.is_one(&value.value)
    }

    pub fn eq_el(&self, lhs: CyclotomicGaloisGroupEl, rhs: CyclotomicGaloisGroupEl) -> bool {
        self.ring.eq_el(&lhs.value, &rhs.value)
    }

    ///
    /// Returns `m` such that this group is the Galois group of the `m`-th cyclotomic number
    /// field `Q[𝝵]`, where `𝝵` is an `m`-th primitive root of unity.
    /// 
    pub fn m(&self) -> usize {
        *self.ring.modulus() as usize
    }

    pub fn to_ring_el(&self, value: CyclotomicGaloisGroupEl) -> ZnEl {
        value.value
    }

    pub fn underlying_ring(&self) -> &Zn {
        &self.ring
    }

    pub fn group_order(&self) -> usize {
        self.order
    }

    pub fn element_order(&self, value: CyclotomicGaloisGroupEl) -> usize {
        order(
            &RingElementWrapper::new(&self.ring, value.value), 
            self.group_order() as i64, 
            |a, b| a * b, 
            RingElementWrapper::new(&self.ring, self.ring.one())
        ) as usize
    }
}

impl Debug for CyclotomicGaloisGroup {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(Z/{}Z)*", self.ring.modulus())
    }
}

pub struct SerializableCyclotomicGaloisGroupEl<'a>(&'a CyclotomicGaloisGroup, CyclotomicGaloisGroupEl);

impl<'a> SerializableCyclotomicGaloisGroupEl<'a> {
    pub fn new(galois_group: &'a CyclotomicGaloisGroup, el: CyclotomicGaloisGroupEl) -> Self {
        Self(galois_group, el)
    }
}

impl<'a> Serialize for SerializableCyclotomicGaloisGroupEl<'a> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        SerializableNewtype::new("CyclotomicGaloisGroupEl", &SerializeOwnedWithRing::new(self.1.value, &self.0.ring)).serialize(serializer)
    }
}

#[derive(Copy, Clone)]
pub struct DeserializeSeedCyclotomicGaloisGroupEl<'a>(&'a CyclotomicGaloisGroup);

impl<'a> DeserializeSeedCyclotomicGaloisGroupEl<'a> {
    pub fn new(galois_group: &'a CyclotomicGaloisGroup) -> Self {
        Self(galois_group)
    }
}

impl<'a, 'de> DeserializeSeed<'de> for DeserializeSeedCyclotomicGaloisGroupEl<'a> {
    type Value = CyclotomicGaloisGroupEl;

    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
        DeserializeSeedNewtype::new("CyclotomicGaloisGroupEl", DeserializeWithRing::new(&self.0.ring)).deserialize(deserializer).map(|g| CyclotomicGaloisGroupEl { value: g })
    }
}

impl Serialize for CyclotomicGaloisGroup {
    
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        SerializableNewtype::new("CyclotomicGaloisGroup", self.ring.modulus()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for CyclotomicGaloisGroup {

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de>
    {
        DeserializeSeedNewtype::new("CyclotomicGaloisGroup", PhantomData::<i64>).deserialize(deserializer).map(|m| Self {
            ring: Zn::new(m as u64),
            order: euler_phi(&factor(ZZi64, m as i64)) as usize
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CyclotomicGaloisGroupEl {
    value: El<Zn>
}

///
/// Trait for rings `R[X]/(Phi_m(X))`, for a base ring `R`. Note that `Phi_m` is allowed to factor in `R`, 
/// hence this ring might not be integral. Furthermore, the residue class of `X`, i.e. the root of unity, 
/// must be given by [`feanor_math::rings::extension::FreeAlgebra::canonical_gen()`].
/// 
/// # Nontrivial automorphisms
/// 
/// See [`feanor_math::rings::extension::FreeAlgebra`].
/// 
/// Note that computing this particular map when given arbitrary isomorphic instances `R`, `S`
/// can be difficult for specific implementations, hence it is not required that for all isomorphic
/// instances `R, S: RingType` with `RingType: CyclotomicRing` we have `R.has_canonical_hom(S).is_some()`.
/// Naturally, it is always required that `R.has_canonical_iso(R).is_some()`.
/// 
/// # Ambiguity in some situations
/// 
/// There is some ambiguity, as for `m` odd, we have `R[X]/(Phi_m) ~ R[X]/(Phi_(2m))` are isomorphic.
/// It is up to implementations which of these representations should be exposed via this trait.
/// Naturally, this should be consistent - i.e. `self.canonical_gen()` should always return
/// a `self.m()`-th root of unity.
/// 
pub trait CyclotomicRing: FreeAlgebra {

    ///
    /// The cyclotomic order, i.e. the multiplicative order of `self.canonical_gen()`.
    /// The degree of this ring extension is `phi(self.m())` where `phi` is Euler's totient
    /// function. This is sometimes also called the conductor of this cyclotomic ring.
    ///
    fn m(&self) -> usize;

    ///
    /// Returns the Galois group of this ring, which we define as the Galois group of the number field
    /// `Q[X]/(Phi_m)`. The ring itself may or may not have more automorphisms (depending on `R`), but ever
    /// Galois group element does induce an automorphism of this ring, which can be accessed via
    /// [`CyclotomicRing::apply_galois_action()`].
    /// 
    fn galois_group(&self) -> CyclotomicGaloisGroup {
        CyclotomicGaloisGroup::new(self.m() as u64)
    }

    ///
    /// Computes `g(x)` for the given Galois automorphism `g`.
    /// 
    fn apply_galois_action(&self, x: &Self::Element, g: CyclotomicGaloisGroupEl) -> Self::Element;

    ///
    /// Computes `g(x)` for each Galois automorphism `g` in the given list.
    /// 
    /// This may be faster than using [`CyclotomicRing::apply_galois_action()`] multiple times.
    /// 
    fn apply_galois_action_many(&self, x: &Self::Element, gs: &[CyclotomicGaloisGroupEl]) -> Vec<Self::Element> {
        gs.iter().map(move |g| self.apply_galois_action(&x, *g)).collect()
    }
}

///
/// The [`RingStore`] belonging to [`CyclotomicRing`]
/// 
pub trait CyclotomicRingStore: RingStore
    where Self::Type: CyclotomicRing
{
    delegate!{ CyclotomicRing, fn m(&self) -> usize }
    delegate!{ CyclotomicRing, fn galois_group(&self) -> CyclotomicGaloisGroup }
    delegate!{ CyclotomicRing, fn apply_galois_action(&self, el: &El<Self>, s: CyclotomicGaloisGroupEl) -> El<Self> }
    delegate!{ CyclotomicRing, fn apply_galois_action_many(&self, el: &El<Self>, gs: &[CyclotomicGaloisGroupEl]) -> Vec<El<Self>> }
}

impl<R: RingStore> CyclotomicRingStore for R
    where R::Type: CyclotomicRing
{}

#[cfg(any(test, feature = "generic_tests"))]
pub fn generic_test_cyclotomic_ring_axioms<R: CyclotomicRingStore>(ring: R)
    where R::Type: CyclotomicRing
{
    use feanor_math::assert_el_eq;
    use feanor_math::primitive_int::*;
    use feanor_math::algorithms::int_factor::factor;
    use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
    use feanor_math::rings::poly::*;
    use feanor_math::rings::poly::sparse_poly::SparsePolyRing;
    use feanor_math::seq::*;
    use feanor_math::homomorphism::Homomorphism;

    let zeta = ring.canonical_gen();
    let m = ring.m();
    
    assert_el_eq!(&ring, &ring.one(), &ring.pow(ring.clone_el(&zeta), m as usize));
    for (p, _) in factor(&StaticRing::<i64>::RING, m as i64) {
        assert!(!ring.eq_el(&ring.one(), &ring.pow(ring.clone_el(&zeta), m as usize / p as usize)));
    }

    // test minimal polynomial of zeta
    let poly_ring = SparsePolyRing::new(&StaticRing::<i64>::RING, "X");
    let cyclo_poly = cyclotomic_polynomial(&poly_ring, m as usize);

    let x = ring.pow(ring.clone_el(&zeta), ring.rank());
    let x_vec = ring.wrt_canonical_basis(&x);
    assert_eq!(ring.rank(), x_vec.len());
    for i in 0..x_vec.len() {
        assert_el_eq!(ring.base_ring(), &ring.base_ring().negate(ring.base_ring().int_hom().map(*poly_ring.coefficient_at(&cyclo_poly, i) as i32)), &x_vec.at(i));
    }
    assert_el_eq!(&ring, &x, &ring.from_canonical_basis((0..x_vec.len()).map(|i| x_vec.at(i))));

    // test basis wrt_root_of_unity_basis linearity and compatibility from_canonical_basis/wrt_root_of_unity_basis
    for i in (0..ring.rank()).step_by(5) {
        for j in (1..ring.rank()).step_by(7) {
            if i == j {
                continue;
            }
            let element = ring.from_canonical_basis((0..ring.rank()).map(|k| if k == i { ring.base_ring().one() } else if k == j { ring.base_ring().int_hom().map(2) } else { ring.base_ring().zero() }));
            let expected = ring.add(ring.pow(ring.clone_el(&zeta), i), ring.int_hom().mul_map(ring.pow(ring.clone_el(&zeta), j), 2));
            assert_el_eq!(&ring, &expected, &element);
            let element_vec = ring.wrt_canonical_basis(&expected);
            for k in 0..ring.rank() {
                if k == i {
                    assert_el_eq!(ring.base_ring(), &ring.base_ring().one(), &element_vec.at(k));
                } else if k == j {
                    assert_el_eq!(ring.base_ring(), &ring.base_ring().int_hom().map(2), &element_vec.at(k));
                } else {
                    assert_el_eq!(ring.base_ring(), &ring.base_ring().zero(), &element_vec.at(k));
                }
            }
        }
    }
}
