use std::cmp::max;

use feanor_math::algorithms::discrete_log::discrete_log;
use feanor_math::algorithms::eea::{signed_gcd, signed_lcm};
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::iters::clone_slice;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::iters::multi_cartesian_product;
use feanor_math::ring::*;
use feanor_math::rings::finite::FiniteRingStore;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::homomorphism::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_rns;
use feanor_math::seq::*;
use feanor_math::wrapper::RingElementWrapper;
use serde::{Deserialize, Serialize};

use crate::{cyclotomic::*, ZZi64};
use crate::euler_phi;

///
/// Represents a hypercube, which is a map
/// ```text
///   h: { 0, ..., m1 - 1 } x ... x { 0, ..., mr - 1 } -> (Z/nZ)^*
///                      a1,  ...,  ar                 -> prod_i gi^ai
/// ```
/// such that the composition `(mod <p>) ∘ h` is a bijection.
/// 
/// We use the following notation:
///  - `n` and `p` as above
///  - `d` is the order of `<p>` as subgroup of `(Z/nZ)*`
///  - `mi` is the length of the `i`-th "hypercube dimension" as above
///  - `gi` is the generator of the `i`-th hypercube dimension
/// 
#[derive(Clone)]
pub struct HypercubeStructure {
    pub(super) galois_group: CyclotomicGaloisGroup,
    pub(super) p: CyclotomicGaloisGroupEl,
    pub(super) d: usize,
    pub(super) ms: Vec<usize>,
    pub(super) ord_gs: Vec<usize>,
    pub(super) gs: Vec<CyclotomicGaloisGroupEl>,
    pub(super) representations: Vec<(CyclotomicGaloisGroupEl, /* first element is frobenius */ Box<[usize]>)>,
    pub(super) choice: HypercubeTypeData
}

#[derive(Clone, Serialize, Deserialize, PartialEq)]
pub enum HypercubeTypeData {
    Generic, 
    /// if the hypercube dimensions correspond directly to prime power factors of `n`, 
    /// we store this correspondence here, as it can be used to explicitly work with the
    /// relationship between hypercube dimensions and tensor factors of `Z[𝝵]`
    CyclotomicTensorProductHypercube(Vec<(i64, usize)>)
}

impl PartialEq for HypercubeStructure {
    fn eq(&self, other: &Self) -> bool {
        self.galois_group == other.galois_group && 
            self.galois_group.eq_el(self.p, other.p) &&
            self.d == other.d && 
            self.ms == other.ms &&
            self.gs.iter().zip(other.gs.iter()).all(|(l, r)| self.galois_group.eq_el(*l, *r)) &&

            self.choice == other.choice
    }
}

impl HypercubeStructure {

    pub fn new(galois_group: CyclotomicGaloisGroup, p: CyclotomicGaloisGroupEl, d: usize, ms: Vec<usize>, gs: Vec<CyclotomicGaloisGroupEl>) -> Self {
        assert_eq!(ms.len(), gs.len());
        // check order of p
        assert!(galois_group.is_identity(galois_group.pow(p, d as i64)));
        for (factor, _) in factor(ZZi64, d as i64) {
            assert!(!galois_group.is_identity(galois_group.pow(p, d as i64 / factor)));
        }
        // check whether the given values indeed define a bijection modulo `<p>`
        let mut all_elements = multi_cartesian_product([(0..d)].into_iter().chain(ms.iter().map(|mi| 0..*mi)), |idxs| (
            galois_group.prod(idxs.iter().zip([&p].into_iter().chain(gs.iter())).map(|(i, g)| galois_group.pow(*g, *i as i64))),
            clone_slice(idxs)
        ), |_, x| *x).collect::<Vec<_>>();
        all_elements.sort_unstable_by_key(|(g, _)| galois_group.representative(*g));
        assert!((1..all_elements.len()).all(|i| !galois_group.eq_el(all_elements[i - 1].0, all_elements[i].0)), "not a bijection");
        assert_eq!(galois_group.group_order(), all_elements.len());

        return Self {
            galois_group: galois_group,
            p: p,
            d: d,
            ms: ms,
            ord_gs: gs.iter().map(|g| galois_group.element_order(*g)).collect(),
            gs: gs,
            choice: HypercubeTypeData::Generic,
            representations: all_elements
        };
    }

    ///
    /// Computes "the" Halevi-Shoup hypercube as described in <https://ia.cr/2014/873>.
    /// 
    /// Note that the Halevi-Shoup hypercube is unique except for the ordering of prime
    /// factors of `n`. This function uses a deterministic but unspecified ordering.
    /// 
    pub fn halevi_shoup_hypercube(galois_group: CyclotomicGaloisGroup, p: i64) -> Self {

        ///
        /// Stores information about a factor in the representation `(Z/nZ)* = (Z/n1Z)* x ... (Z/nrZ)*`
        /// and about `<p> <= (Z/niZ)^*` (considering `p` to be the "orthogonal" projection of `p in (Z/nZ)*`
        /// into `(Z/niZ)*`).
        /// 
        /// The one exception is the case `ni = 2^e`, since `(Z/2^eZ)*` is not cyclic (for `e > 2`).
        /// We then store it as a single factor (if `(Z/2^eZ)* = <p, g>` for some generator `g`) or as
        /// two factors otherwise.
        /// 
        struct HypercubeDimension {
            g_main: ZnEl,
            order_of_projected_p: i64,
            group_order: i64,
            factor_n: (i64, usize)
        }

        let n = galois_group.n() as i64;
        assert!(signed_gcd(n, p, ZZi64) == 1, "n and p must be coprime");

        // the unit group (Z/nZ)* decomposes as X (Z/niZ)*; this gives rise to the natural hypercube structure,
        // although technically many possible hypercube structures are possible
        let mut factorization = factor(ZZi64, n);
        // this makes debugging easier, since we have a canonical order
        factorization.sort_unstable_by_key(|(p, _)| *p);
        let Zn_rns = zn_rns::Zn::new(factorization.iter().map(|(q, k)| Zn::new(ZZi64.pow(*q, *k) as u64)).collect(), ZZi64);
        let Zn = Zn::new(n as u64);
        let iso = Zn.into_can_hom(zn_big::Zn::new(ZZi64, n)).ok().unwrap().compose((&Zn_rns).into_can_iso(zn_big::Zn::new(ZZi64, n)).ok().unwrap());
        let from_crt = |index: usize, value: ZnEl| iso.map(Zn_rns.from_congruence((0..factorization.len()).map(|j| if j == index { value } else { Zn_rns.at(j).one() })));

        let mut dimensions = Vec::new();
        for (i, (q, k)) in factorization.iter().enumerate() {
            let Zqk = Zn_rns.at(i);
            if *q == 2 {
                // `(Z/2^kZ)*` is an exception, since it is not cyclic
                if *k == 1 {
                    continue;
                } else if *k == 2 {
                    unimplemented!()
                } else {
                    // `(Z/2^kZ)*` is isomorphic to `<g1> x <g2>` where `<g1> ~ Z/2^(k - 2)Z` and `<g2> ~ Z/2Z`
                    let g1 = Zqk.int_hom().map(5);
                    let ord_g1 = ZZi64.pow(*q, *k as usize - 2);
                    let g2 = Zqk.can_hom(&ZZi64).unwrap().map(-1);
                    if p % 4 == 1 {
                        // `p` is in `<g1>`
                        let logg1_p = unit_group_dlog(Zqk, g1, ord_g1, Zqk.can_hom(&ZZi64).unwrap().map(p)).unwrap();
                        dimensions.push(HypercubeDimension {
                            order_of_projected_p: ord_g1 / signed_gcd(logg1_p, ord_g1, &ZZi64), 
                            group_order: ord_g1,
                            g_main: from_crt(i, g1),
                            factor_n: (2, *k),
                        });
                        dimensions.push(HypercubeDimension {
                            order_of_projected_p: 1, 
                            group_order: 2,
                            g_main: from_crt(i, g2),
                            factor_n: (2, *k),
                        });
                    } else {
                        // `<p, g1> = (Z/2^kZ)*` and `p * g2 in <g1>`
                        let logg1_pg2 = unit_group_dlog(Zqk, g1, ord_g1, Zqk.mul(Zqk.can_hom(&ZZi64).unwrap().map(p), g2)).unwrap();
                        dimensions.push(HypercubeDimension {
                            order_of_projected_p: max(ord_g1 / signed_gcd(logg1_pg2, ord_g1, &ZZi64), 2),
                            group_order: 2 * ord_g1,
                            g_main: from_crt(i, g1),
                            factor_n: (2, *k)
                        });
                    }
                }
            } else {
                // `(Z/q^kZ)*` is cyclic
                let g = get_multiplicative_generator(*Zqk, &[(*q, *k)]);
                let ord_g = euler_phi(&[(*q, *k)]);
                let logg_p = unit_group_dlog(Zqk, g, ord_g, Zqk.can_hom(&ZZi64).unwrap().map(p)).unwrap();
                let ord_p = ord_g / signed_gcd(logg_p, ord_g, ZZi64);
                dimensions.push(HypercubeDimension {
                    order_of_projected_p: ord_p, 
                    group_order: ord_g,
                    g_main: from_crt(i, g),
                    factor_n: (*q, *k)
                });
            }
        }

        dimensions.sort_by_key(|dim| -(dim.order_of_projected_p as i64));
        let mut current_d = 1;
        let lengths = dimensions.iter().map(|dim| {
            let new_d = signed_lcm(current_d, dim.order_of_projected_p as i64, ZZi64);
            let len = dim.group_order as i64 / (new_d / current_d);
            current_d = new_d;
            return len as usize;
        }).collect::<Vec<_>>();

        let mut result = Self::new(
            galois_group,
            galois_group.from_representative(p),
            current_d as usize,
            lengths,
            dimensions.iter().map(|dim| galois_group.from_ring_el(dim.g_main)).collect()
        );
        result.choice = HypercubeTypeData::CyclotomicTensorProductHypercube(dimensions.iter().map(|dim| dim.factor_n).collect());
        return result;
    }

    ///
    /// Applies the hypercube structure map to the unit vector multiple `steps * e_(dim_idx)`,
    /// i.e. computes the galois automorphism corresponding to the shift by `steps` steps
    /// along the `dim_idx`-th hypercube dimension.
    /// 
    pub fn map_1d(&self, dim_idx: usize, steps: i64) -> CyclotomicGaloisGroupEl {
        assert!(dim_idx < self.dim_count());
        self.galois_group.pow(self.gs[dim_idx], steps)
    }

    ///
    /// Applies the hypercube structure map to the given vector.
    /// 
    /// It is not enforced that the entries of the vector are contained in
    /// `{ 0, ..., m1 - 1 } x ... x { 0, ..., mr - 1 }`, for values outside this
    /// range the natural extension of `h` to `Z^r` is used, i.e.
    /// ```text
    ///   h:       Z^r      ->   (Z/nZ)^*
    ///      a1,  ...,  ar  -> prod_i gi^ai
    /// ```
    /// 
    pub fn map(&self, idxs: &[i64]) -> CyclotomicGaloisGroupEl {
        assert_eq!(self.ms.len(), idxs.len());
        self.galois_group.prod(idxs.iter().zip(self.gs.iter()).map(|(i, g)| self.galois_group.pow(*g, *i)))
    }

    ///
    /// Same as [`HypercubeStructure::map()`], but for a vector with
    /// unsigned entries.
    /// 
    pub fn map_usize(&self, idxs: &[usize]) -> CyclotomicGaloisGroupEl {
        assert_eq!(self.ms.len(), idxs.len());
        self.galois_group.prod(idxs.iter().zip(self.gs.iter()).map(|(i, g)| self.galois_group.pow(*g, *i as i64)))
    }

    ///
    /// Computes the "standard preimage" of the given `g` under `h`.
    /// 
    /// This is the vector `(a0, a1, ..., ar)` such that `g = p^a0 h(a1, ..., ar)` and
    /// each `ai` is within `{ 0, ..., mi - 1 }`.
    /// 
    pub fn std_preimage(&self, g: CyclotomicGaloisGroupEl) -> &[usize] {
        let idx = self.representations.binary_search_by_key(&self.galois_group.representative(g), |(g, _)| self.galois_group.representative(*g)).unwrap();
        return &self.representations[idx].1;
    }

    ///
    /// Returns whether each dimension of the hypercube corresponds to a factor `ni` of
    /// `n` (with `ni` coprime to `n/ni`). This is the case for the Halevi-Shoup hypercube,
    /// and very useful in some situations. If this is the case, you can query the factor
    /// of `n` corresponding to some dimension by [`HypercubeStructure::factor_of_n()`].
    /// 
    pub fn is_tensor_product_compatible(&self) -> bool {
        match self.choice {
            HypercubeTypeData::CyclotomicTensorProductHypercube(_) => true,
            HypercubeTypeData::Generic => false
        }
    }

    ///
    /// Returns the factor `ni` of `n` (coprime to `n/ni`) which the `i`-th hypercube
    /// dimension corresponds to. This is only applicable if the hypercube was constructed
    /// from a (partial) factorization of `n`, i.e. [`HypercubeStructure::is_tensor_product_compatible()`]
    /// returns true. Otherwise, this function will return `None`.
    /// 
    pub fn factor_of_n(&self, dim_idx: usize) -> Option<i64> {
        assert!(dim_idx < self.dim_count());
        match &self.choice {
            HypercubeTypeData::CyclotomicTensorProductHypercube(factors_n) => Some(ZZi64.pow(factors_n[dim_idx].0, factors_n[dim_idx].1)),
            HypercubeTypeData::Generic => None
        }
    }

    ///
    /// Returns `p` as an element of `(Z/nZ)*`.
    /// 
    pub fn p(&self) -> CyclotomicGaloisGroupEl {
        self.p
    }

    ///
    /// Returns the Galois automorphism corresponding to the power-of-`p^power`
    /// frobenius automorphism of the slot ring.
    /// 
    pub fn frobenius(&self, power: i64) -> CyclotomicGaloisGroupEl {
        self.galois_group.pow(self.p(), power)
    }

    ///
    /// Returns the rank `d` of the slot ring.
    /// 
    pub fn d(&self) -> usize {
        self.d
    }

    ///
    /// Returns the length `mi` of the `i`-th hypercube dimension.
    /// 
    pub fn m(&self, i: usize) -> usize {
        assert!(i < self.ms.len());
        self.ms[i]
    }

    ///
    /// Returns the generator `gi` corresponding to the `i`-th hypercube dimension.
    /// 
    pub fn g(&self, i: usize) -> CyclotomicGaloisGroupEl {
        assert!(i < self.ms.len());
        self.gs[i]
    }

    ///
    /// Returns the order of `gi` in the group `(Z/nZ)*`.
    /// 
    pub fn ord_g(&self, i: usize) -> usize {
        assert!(i < self.ms.len());
        self.ord_gs[i]
    }

    ///
    /// Returns `n`, i.e. the multiplicative order of the root of unity of the main ring.
    /// This is also sometimes called the conductor of the cyclotomic number ring.
    /// 
    pub fn n(&self) -> usize {
        self.galois_group().n()
    }

    ///
    /// Returns the number of dimensions in the hypercube.
    /// 
    pub fn dim_count(&self) -> usize {
        self.gs.len()
    }

    ///
    /// Returns the Galois group isomorphic to `(Z/nZ)*` that this hypercube
    /// describes.
    /// 
    pub fn galois_group(&self) -> &CyclotomicGaloisGroup {
        &self.galois_group
    }

    ///
    /// Returns the number of elements of `{ 0, ..., m1 - 1 } x ... x { 0, ..., mr - 1 }`
    /// or equivalently `(Z/nZ)*/<p>`, which is equal to the to the number of slots of 
    /// `Fp[X]/(Phi_n(X))`.
    /// 
    pub fn element_count(&self) -> usize {
        ZZi64.prod(self.ms.iter().map(|mi| *mi as i64)) as usize
    }

    ///
    /// Creates an iterator that yields a value for each element of `{ 0, ..., m1 - 1 } x ... x { 0, ..., mr - 1 }` 
    /// resp. `(Z/nZ)*/<p>`. Hence, these elements correspond to the slots of `Fp[X]/(Phi_n(X))`.
    /// 
    /// The given closure will be called on each element of `{ 0, ..., m1 - 1 } x ... x { 0, ..., mr - 1 }`.
    /// The returned iterator will iterate over the results of the closure.
    /// 
    pub fn hypercube_iter<'b, G, T>(&'b self, for_slot: G) -> impl ExactSizeIterator<Item = T> + use<'b, G, T>
        where G: 'b + Clone + FnMut(&[usize]) -> T,
            T: 'b
    {
        let mut it = multi_cartesian_product(
            self.ms.iter().map(|l| (0..*l)),
            for_slot,
            |_, x| *x
        );
        (0..self.element_count()).map(move |_| it.next().unwrap())
    }

    ///
    /// Creates an iterator that one representative of each element of `(Z/nZ)*/<p>`, which
    /// also is in the image of this hypercube structure.
    /// 
    /// The order is compatible with [`HypercubeStructure::hypercube_iter()`].
    /// 
    pub fn element_iter<'b>(&'b self) -> impl ExactSizeIterator<Item = CyclotomicGaloisGroupEl> + use<'b> {
        self.hypercube_iter(|idxs| self.map_usize(idxs))
    }
}

pub fn get_multiplicative_generator(ring: Zn, factorization: &[(i64, usize)]) -> ZnEl {
    assert_eq!(*ring.modulus(), ZZi64.prod(factorization.iter().map(|(p, e)| ZZi64.pow(*p, *e))));
    assert!(*ring.modulus() % 2 == 1, "for even n, Z/nZ* is either equal to Z/(n/2)Z* or not cyclic");
    let mut rng = oorandom::Rand64::new(ring.integer_ring().default_hash(ring.modulus()) as u128);
    let order = euler_phi(factorization);
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

pub fn unit_group_dlog(ring: &Zn, base: ZnEl, order: i64, value: ZnEl) -> Option<i64> {
    discrete_log(
        RingElementWrapper::new(&ring, value), 
        &RingElementWrapper::new(&ring, base), 
        order, 
        |x, y| x * y, 
        RingElementWrapper::new(&ring, ring.one())
    )
}

#[test]
fn test_halevi_shoup_hypercube() {
    let galois_group = CyclotomicGaloisGroup::new(11 * 31);
    let hypercube_structure = HypercubeStructure::halevi_shoup_hypercube(galois_group, 2);
    assert_eq!(10, hypercube_structure.d());
    assert_eq!(2, hypercube_structure.dim_count());

    assert_eq!(1, hypercube_structure.m(0));
    assert_eq!(30, hypercube_structure.m(1));

    let galois_group = CyclotomicGaloisGroup::new(32);
    let hypercube_structure = HypercubeStructure::halevi_shoup_hypercube(galois_group, 7);
    assert_eq!(4, hypercube_structure.d());
    assert_eq!(1, hypercube_structure.dim_count());

    assert_eq!(4, hypercube_structure.m(0));

    let galois_group = CyclotomicGaloisGroup::new(32);
    let hypercube_structure = HypercubeStructure::halevi_shoup_hypercube(galois_group, 17);
    assert_eq!(2, hypercube_structure.d());
    assert_eq!(2, hypercube_structure.dim_count());

    assert_eq!(4, hypercube_structure.m(0));
    assert_eq!(2, hypercube_structure.m(1));
}

#[test]
fn test_serialization() {
    for hypercube in [
        HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(11 * 31), 2),
        HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(32), 7),
        HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(32), 17)
    ] {
        let serializer = serde_assert::Serializer::builder().is_human_readable(true).build();
        let tokens = hypercube.serialize(&serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(true).build();
        let deserialized_hypercube = HypercubeStructure::deserialize(&mut deserializer).unwrap();

        assert!(hypercube.galois_group() == deserialized_hypercube.galois_group());
        assert_eq!(hypercube.dim_count(), deserialized_hypercube.dim_count());
        assert_eq!(hypercube.is_tensor_product_compatible(), deserialized_hypercube.is_tensor_product_compatible());
        for i in 0..hypercube.dim_count() {
            assert_eq!(hypercube.m(i), deserialized_hypercube.m(i));
            assert!(hypercube.galois_group().eq_el(hypercube.g(i), deserialized_hypercube.g(i)));
            assert_eq!(hypercube.ord_g(i), deserialized_hypercube.ord_g(i));
        }

        let serializer = serde_assert::Serializer::builder().is_human_readable(false).build();
        let tokens = hypercube.serialize(&serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(false).build();
        let deserialized_hypercube = HypercubeStructure::deserialize(&mut deserializer).unwrap();

        assert!(hypercube.galois_group() == deserialized_hypercube.galois_group());
        assert_eq!(hypercube.dim_count(), deserialized_hypercube.dim_count());
        assert_eq!(hypercube.is_tensor_product_compatible(), deserialized_hypercube.is_tensor_product_compatible());
        for i in 0..hypercube.dim_count() {
            assert_eq!(hypercube.m(i), deserialized_hypercube.m(i));
            assert!(hypercube.galois_group().eq_el(hypercube.g(i), deserialized_hypercube.g(i)));
            assert_eq!(hypercube.ord_g(i), deserialized_hypercube.ord_g(i));
        }
    }
}