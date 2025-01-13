use std::fmt::Debug;

use feanor_math::algorithms::discrete_log::order;
use feanor_math::ring::*;
use feanor_math::delegate;
use feanor_math::rings::extension::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::rings::zn::*;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::primitive_int::StaticRing;
use feanor_math::wrapper::RingElementWrapper;
use feanor_math::divisibility::DivisibilityRingStore;

use crate::euler_phi;

const ZZi64: StaticRing<i64> = StaticRing::RING;

#[derive(Clone, Copy)]
pub struct CyclotomicGaloisGroup {
    ring: Zn,
    order: usize
}

impl CyclotomicGaloisGroup {

    pub fn new(n: u64) -> Self {
        Self {
            ring: Zn::new(n),
            order: euler_phi(&factor(ZZi64, n as i64)) as usize
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

    pub fn n(&self) -> usize {
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

#[derive(Debug, Clone, Copy)]
pub struct CyclotomicGaloisGroupEl {
    value: El<Zn>
}

///
/// Trait for rings `R[X]/(Phi_n)`, for a base ring `R`. Note that `Phi_n` is allowed to factor in `R`, hence this ring
/// might not be integral. Furthermore, the residue class of `X`, i.e. the root of unity, must be given by 
/// [`feanor_math::rings::extension::FreeAlgebra::canonical_gen()`].
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
/// a `self.n()`-th root of unity.
/// 
pub trait CyclotomicRing: FreeAlgebra {

    ///
    /// The cyclotomic order, i.e. the multiplicative order of `self.canonical_gen()`.
    /// The degree of this ring extension is `phi(self.n())` where `phi` is Euler's totient
    /// function.
    ///
    fn n(&self) -> u64;

    fn galois_group(&self) -> CyclotomicGaloisGroup {
        CyclotomicGaloisGroup::new(self.n())
    }

    fn apply_galois_action(&self, x: &Self::Element, g: CyclotomicGaloisGroupEl) -> Self::Element;

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
    delegate!{ CyclotomicRing, fn n(&self) -> u64 }
    delegate!{ CyclotomicRing, fn galois_group(&self) -> CyclotomicGaloisGroup }
    delegate!{ CyclotomicRing, fn apply_galois_action(&self, el: &El<Self>, s: CyclotomicGaloisGroupEl) -> El<Self> }
    delegate!{ CyclotomicRing, fn apply_galois_action_many(&self, el: &El<Self>, gs: &[CyclotomicGaloisGroupEl]) -> Vec<El<Self>> }
}

impl<R: RingStore> CyclotomicRingStore for R
    where R::Type: CyclotomicRing
{}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::primitive_int::*;
#[cfg(test)]
use feanor_math::algorithms;
#[cfg(test)]
use feanor_math::rings::poly::*;
#[cfg(test)]
use feanor_math::rings::poly::sparse_poly::SparsePolyRing;
#[cfg(test)]
use feanor_math::seq::*;

#[cfg(any(test, feature = "generic_tests"))]
pub fn generic_test_cyclotomic_ring_axioms<R: CyclotomicRingStore>(ring: R)
    where R::Type: CyclotomicRing
{
    use feanor_math::homomorphism::Homomorphism;

    let zeta = ring.canonical_gen();
    let n = ring.n();
    
    assert_el_eq!(&ring, &ring.one(), &ring.pow(ring.clone_el(&zeta), n as usize));
    for (p, _) in algorithms::int_factor::factor(&StaticRing::<i64>::RING, n as i64) {
        assert!(!ring.eq_el(&ring.one(), &ring.pow(ring.clone_el(&zeta), n as usize / p as usize)));
    }

    // test minimal polynomial of zeta
    let poly_ring = SparsePolyRing::new(&StaticRing::<i64>::RING, "X");
    let cyclo_poly = algorithms::cyclotomic::cyclotomic_polynomial(&poly_ring, n as usize);

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
