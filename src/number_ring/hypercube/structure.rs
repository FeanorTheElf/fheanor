use std::borrow::Cow;
use std::marker::PhantomData;

use feanor_math::algorithms::discrete_log::*;
use feanor_math::algorithms::eea::{signed_gcd, signed_lcm};
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::group::*;
use feanor_math::integer::{int_cast, BigIntRing, IntegerRingStore};
use feanor_math::iters::clone_slice;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::iters::multi_cartesian_product;
use feanor_math::ring::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::homomorphism::*;
use feanor_math::pid::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_rns;
use feanor_math::seq::*;
use feanor_serde::dependent_tuple::DeserializeSeedDependentTuple;
use feanor_serde::impl_deserialize_seed_for_dependent_struct;
use feanor_serde::newtype_struct::{DeserializeSeedNewtypeStruct, SerializableNewtypeStruct};
use feanor_serde::seq::{DeserializeSeedSeq, SerializableSeq};
use serde::de::DeserializeSeed;
use serde::{Deserialize, Serialize};

use crate::{euler_phi, ZZbig, ZZi64};
use crate::number_ring::galois::*;

///
/// Represents a hypercube structure, which is a map into the relative Galois
/// group `G` of a number ring over a subring
/// ```text
///   h: { 0, ..., l_1 - 1 } x ... x { 0, ..., l_r - 1 } -> G
///                      a_1,  ...,  a_r                 -> prod_i g_i^a_i
/// ```
/// such that the composition `(mod <p>) ∘ h` is a bijection, where `p` is
/// distinguished element of `G`.
/// 
/// We use the following notation:
///  - `G` is the Galois group of a number ring over a subring, thus a subgroup
///    of `(Z/mZ)*` (since fheanor currently only supports cyclotomic rings)
///  - `p` is a distinguished element of `G`; In applications, it will be the
///    Frobenius automorphism associated to a prime ideal of the subring
///  - `d` is the order of `<p>` as subgroup of `G`
///  - `l_i` is the length of the `i`-th "hypercube dimension" as above
///  - `l` is the product of all `l_i`, thus the total number of slots
///  - `g_i` is the generator of the `i`-th hypercube dimension
/// 
/// A special kind of hypercube structure is "Halevi-Shoup hypercube structure",
/// characterized by the fact that each `g_i` is mapped to the `i`-th unit vector
/// under some isomorphism
/// ```text
///   (Z/mZ)* -> (Z/m_1Z)* x ... x (Z/m_rZ)*
/// ```
/// for the factorization `m = m_1 ... m_r` into pairwise coprime factors. In this
/// case, the factors `m_i` can be queried using [`HypercubeStructure::factor_of_m()`].
/// Note that in this case, we have that `l_i = ord( g_i mod <p> ) | ord( g_i ) | phi(m_i)`.
/// If `l_i = ord( g_i mod <p> ) = ord( g_i ) = phi(m_i)`, the dimension is called good.
/// 
#[derive(Clone)]
pub struct HypercubeStructure {
    // visible at pub(super) to be accessed by serialization routines
    pub(super) galois_group: Subgroup<CyclotomicGaloisGroup>,
    pub(super) frobenius: GaloisGroupEl,
    pub(super) d: usize,
    pub(super) ls: Vec<usize>,
    pub(super) ord_gs: Vec<usize>,
    pub(super) gs: Vec<GaloisGroupEl>,
    pub(super) representations: Vec<(GaloisGroupEl, /* first element is frobenius */ Box<[usize]>)>,
    pub(super) signed_normalization_offset: (Vec<usize>, GaloisGroupEl),
    pub(super) choice: HypercubeTypeData
}

#[derive(Clone, Serialize, Deserialize, PartialEq)]
pub enum HypercubeTypeData {
    Generic, 
    /// if the hypercube dimensions correspond directly to prime power factors of `m`, 
    /// we store this correspondence here, as it can be used to explicitly work with the
    /// relationship between hypercube dimensions and tensor factors of `Z[𝝵]`
    CyclotomicTensorProductHypercube(Vec<(i64, usize)>)
}

impl PartialEq for HypercubeStructure {
    fn eq(&self, other: &Self) -> bool {
        self.galois_group.get_group() == other.galois_group.get_group() && 
            self.galois_group.eq_el(self.p(), &other.p()) &&
            self.d == other.d && 
            self.ls == other.ls &&
            self.gs.iter().zip(other.gs.iter()).all(|(l, r)| self.galois_group.eq_el(l, r)) &&
            self.choice == other.choice
    }
}

impl HypercubeStructure {

    pub fn new(galois_group: Subgroup<CyclotomicGaloisGroup>, frobenius: GaloisGroupEl, d: usize, ls: Vec<usize>, gs: Vec<GaloisGroupEl>) -> Self {
        assert_eq!(ls.len(), gs.len());
        assert_eq!(d, galois_group.element_order(&frobenius));
        assert!(galois_group.contains(&frobenius));
        assert!(gs.iter().all(|g| galois_group.contains(g)));

        // check whether the given values indeed define a bijection modulo `<p>`
        let mut all_elements = multi_cartesian_product([(0..d)].into_iter().chain(ls.iter().map(|l_i| 0..*l_i)), |idxs| (
            idxs.iter().zip([&frobenius].into_iter().chain(gs.iter()))
                .map(|(i, g)| galois_group.pow(g, &int_cast(*i as i64, ZZbig, ZZi64)))
                .fold(galois_group.identity(), |current, next| galois_group.op(current, next)),
            clone_slice(idxs)
        ), |_, x| *x).collect::<Vec<_>>();
        all_elements.sort_unstable_by_key(|(g, _)| galois_group.representative(g));
        assert!((1..all_elements.len()).all(|i| !galois_group.eq_el(&all_elements[i - 1].0, &all_elements[i].0)), "not a bijection");
        assert_eq!(int_cast(galois_group.subgroup_order(), ZZi64, ZZbig) as usize, all_elements.len());

        let signed_normalization_offset = [d].iter().chain(ls.iter()).map(|x| (x - 1).div_ceil(2)).collect::<Vec<_>>();
        let signed_normalization_offset_el = [&frobenius].into_iter().chain(gs.iter()).zip(signed_normalization_offset.iter())
            .map(|(g, k)| galois_group.pow(g, &int_cast(*k as i64, ZZbig, ZZi64)))
            .fold(galois_group.identity(), |x, y| galois_group.op(x, y));

        let ord_gs = gs.iter().map(|g| galois_group.element_order(g)).collect();
        return Self {
            galois_group: galois_group,
            frobenius: frobenius,
            d: d,
            ls,
            ord_gs: ord_gs,
            gs: gs,
            signed_normalization_offset: (signed_normalization_offset, signed_normalization_offset_el),
            choice: HypercubeTypeData::Generic,
            representations: all_elements
        };
    }

    ///
    /// Computes a hypercube structure for a subgroup of the power-of-two cyclotomic
    /// Galois group. The generated hypercube structure will have at most two dimensions,
    /// and at most one of them will have length `> 2`.
    /// 
    /// Note that `(Z/2^(e + 2)Z)* ~ Z/2^eZ x Z/2Z`. Under this isomorphism,
    /// a subgroup `G` of `(Z/2^(e + 2)Z)*` has one of the following shapes:
    ///  - `{ (k i, 0) | i }`
    ///  - `{ (k i, i) | i }`
    ///  - `{ (2 k i, j) | i, j }`
    /// 
    /// for `k = 2^e / |G|`.
    /// 
    /// Moreover, we have the following options for `<p>`:
    ///  - `{ (k i, 0) | i }` implies `<p> = { (l i, 0) | i }`
    ///  - `{ (k i, i) | i }` implies `<p> = { (l i, 0) | i }` or `<p> = { (l i, i) | i}`
    ///  - `{ (2 k i, j) | i, j }` implies `<p> = { (l i, 0) | i }` or `<p> = { (l i, i) | i }`
    /// 
    /// for `l = 2^e / ord(p)`.
    /// 
    pub fn default_pow2_hypercube(galois_group: &Subgroup<CyclotomicGaloisGroup>, p: El<BigIntRing>) -> Self {

        let m = galois_group.m() as i64;
        let log2_m = ZZi64.abs_log2_ceil(&m).unwrap();
        assert!(m == 1 << log2_m, "m must be a power of two for default_pow2_hypercube()");
        let p_mod_m = int_cast(ZZbig.euclidean_rem(p, &int_cast(m, ZZbig, ZZi64)), ZZi64, ZZbig);
        assert!(signed_gcd(m, p_mod_m, ZZi64) == 1, "m and p must be coprime");
        let frobenius = galois_group.from_representative(p_mod_m);
        let Gal = galois_group.parent();

        let order = galois_group.group_order();
        let d = galois_group.element_order(&frobenius);
        let g1 = Gal.from_representative(5);
        let g2 = Gal.from_representative(-1);
        if order == ZZi64.pow(2, log2_m - 1) as usize || galois_group.contains(&g2) {
            // the third case, `G ~ <2k> x {0, 1}`
            if p_mod_m % 4 == 3 {
                let g1_pow_2k = Gal.pow(&g1, &int_cast(ZZi64.checked_div(&ZZi64.pow(2, log2_m - 1), &(order as i64)).unwrap(), ZZbig, ZZi64));
                return Self::new(
                    galois_group.clone(),
                    frobenius,
                    d,
                    vec![order / d],
                    vec![g1_pow_2k]
                );
            } else {
                let g1_pow_2k = Gal.pow(&g1, &int_cast(ZZi64.checked_div(&ZZi64.pow(2, log2_m - 1), &(order as i64)).unwrap(), ZZbig, ZZi64));
                return Self::new(
                    galois_group.clone(),
                    frobenius,
                    d,
                    vec![order / d / 2, 2],
                    vec![g1_pow_2k, g2]
                );
            }
        }

        let k = ZZi64.checked_div(&ZZi64.pow(2, log2_m - 2), &(order as i64)).unwrap();
        let g1_pow_k = Gal.pow(&g1, &int_cast(k, ZZbig, ZZi64));
        if galois_group.contains(&g1_pow_k) {
            // the first case, `G ~ <k> x {0}`
            return Self::new(
                galois_group.clone(),
                frobenius,
                d,
                vec![order / d],
                vec![g1_pow_k]
            );
        } else {
            // the second case, `G ~ <(k, 1)>`
            let g2_g1_pow_k = Gal.op(g1_pow_k, g2);
            debug_assert!(galois_group.contains(&g2_g1_pow_k));
            return Self::new(
                galois_group.clone(),
                frobenius,
                d,
                vec![order / d],
                vec![g2_g1_pow_k]
            );
        }
    }

    ///
    /// Computes "the" Halevi-Shoup hypercube as described in <https://ia.cr/2014/873>.
    /// 
    /// Note that the Halevi-Shoup hypercube is unique except for the ordering of prime
    /// factors of `m`. This function uses a deterministic but unspecified ordering.
    /// 
    pub fn halevi_shoup_hypercube(galois_group: &Subgroup<CyclotomicGaloisGroup>, p: El<BigIntRing>) -> Self {

        assert!(galois_group.is_full_cyclotomic_galois_group());
        assert!(galois_group.m() % 2 == 1, "the halevi-shoup hypercube structure only exists for odd m");
        let galois_group = galois_group.parent().clone();

        ///
        /// Stores information about a factor in the representation `(Z/mZ)* = (Z/m_1Z)* x ... (Z/m_rZ)*`
        /// and about `<p> <= (Z/m_iZ)^*` (considering `p` to be the "orthogonal" projection of `p in (Z/mZ)*`
        /// into `(Z/m_iZ)*`).
        /// 
        /// The one exception is the case `m_i = 2^e`, since `(Z/2^eZ)*` is not cyclic (for `e > 2`).
        /// We then store it as a single factor (if `(Z/2^eZ)* = <p, g>` for some generator `g`) or as
        /// two factors otherwise.
        /// 
        struct HypercubeDimension {
            g_main: ZnEl,
            order_of_projected_p: i64,
            group_order: i64,
            factor_m: (i64, usize)
        }

        let m = galois_group.m() as i64;
        let frobenius = int_cast(ZZbig.euclidean_rem(p, &int_cast(m, ZZbig, ZZi64)), ZZi64, ZZbig);
        assert!(signed_gcd(m, frobenius, ZZi64) == 1, "m and p must be coprime");

        // the unit group `(Z/mZ)*` decomposes as `X (Z/m_iZ)*`; this gives rise to the natural hypercube structure,
        // although technically many possible hypercube structures are possible
        let mut factorization = factor(ZZi64, m);
        // this makes debugging easier, since we have a canonical order
        factorization.sort_unstable_by_key(|(p, _)| *p);
        let zm_rns = zn_rns::Zn::new(factorization.iter().map(|(q, k)| Zn::new(ZZi64.pow(*q, *k) as u64)).collect(), ZZi64);
        let zm = Zn::new(m as u64);
        let iso = zm.into_can_hom(zn_big::Zn::new(ZZi64, m)).ok().unwrap().compose((&zm_rns).into_can_iso(zn_big::Zn::new(ZZi64, m)).ok().unwrap());
        let from_crt = |index: usize, value: ZnEl| iso.map(zm_rns.from_congruence((0..factorization.len()).map(|j| if j == index { value } else { zm_rns.at(j).one() })));

        let mut dimensions = Vec::new();
        for (i, (q, k)) in factorization.iter().enumerate() {
            let Zqk = zm_rns.at(i);
            assert!(*q != 2);
            // `(Z/q^kZ)*` is cyclic
            let g = get_multiplicative_generator(*Zqk);
            let ord_g = euler_phi(&[(*q, *k)]);
            let logg_p = unit_group_dlog(Zqk, g, Zqk.can_hom(&ZZi64).unwrap().map(frobenius)).unwrap();
            let ord_p = ord_g / signed_gcd(logg_p, ord_g, ZZi64);
            dimensions.push(HypercubeDimension {
                order_of_projected_p: ord_p, 
                group_order: ord_g,
                g_main: from_crt(i, g),
                factor_m: (*q, *k)
            });
        }

        dimensions.sort_by_key(|dim| -(dim.order_of_projected_p as i64));
        let mut current_d = 1;
        let lengths = dimensions.iter().map(|dim| {
            let new_d = signed_lcm(current_d, dim.order_of_projected_p as i64, ZZi64);
            let len = dim.group_order as i64 / (new_d / current_d);
            current_d = new_d;
            len as usize
        }).collect::<Vec<_>>();

        let p_repr = galois_group.from_representative(frobenius);
        let gs = dimensions.iter().map(|dim| galois_group.from_ring_el(dim.g_main)).collect();
        let mut result = Self::new(
            galois_group.into().full_subgroup(),
            p_repr,
            current_d as usize,
            lengths,
            gs
        );
        result.choice = HypercubeTypeData::CyclotomicTensorProductHypercube(dimensions.iter().map(|dim| dim.factor_m).collect());
        return result;
    }

    ///
    /// Applies the hypercube structure map to the unit vector multiple `steps * e_(dim_idx)`.
    /// 
    /// In other words, this computes the galois automorphism corresponding to the shift by `steps`
    /// steps along the `dim_idx`-th hypercube dimension. Be careful, elements that are "moved out" on
    /// one end of the hypercolumn can cause unexpected behavior. For most hypercubes, including all
    /// Halevi-Shoup hypercubes, a Frobenius conjugate of any element that is moved out will be moved
    /// in at the other end. Moving out zeros will never cause any problems, however, but always move
    /// in zero on the other side.
    /// 
    pub fn map_1d(&self, dim_idx: usize, steps: i64) -> GaloisGroupEl {
        assert!(dim_idx < self.dim_count());
        self.galois_group.pow(&self.gs[dim_idx], &int_cast(steps, ZZbig, ZZi64))
    }

    ///
    /// Applies the hypercube structure map to the given vector.
    /// 
    /// It is not enforced that the entries of the vector are contained in
    /// `{ 0, ..., l_i - 1 } x ... x { 0, ..., l_i - 1 }`, for values outside this
    /// range the natural extension of `h` to `Z^r` is used, i.e.
    /// ```text
    ///   h:       Z^r        ->   (Z/mZ)^*
    ///      a_1,  ...,  a_r  -> prod_i g_i^a_i
    /// ```
    /// 
    pub fn map(&self, idxs: &[i64]) -> GaloisGroupEl {
        assert_eq!(self.ls.len(), idxs.len());
        idxs.iter().zip(self.gs.iter()).map(|(i, g)| self.galois_group.pow(g, &int_cast(*i, ZZbig, ZZi64)))
            .fold(self.galois_group().identity(), |current, next| self.galois_group().op(current, next))
    }

    ///
    /// Same as [`HypercubeStructure::map()`], except that the given vector should
    /// have `dim_count + 1` entries, and the first entry is treated as the exponent
    /// of the Frobenius.
    /// 
    pub fn map_incl_frobenius(&self, idxs: &[i64]) -> GaloisGroupEl {
        assert_eq!(self.ls.len() + 1, idxs.len());
        self.galois_group.op(self.map(&idxs[1..]), self.frobenius(idxs[0]))
    }

    ///
    /// Same as [`HypercubeStructure::map()`], but for a vector with
    /// unsigned entries.
    /// 
    pub fn map_usize(&self, idxs: &[usize]) -> GaloisGroupEl {
        assert_eq!(self.ls.len(), idxs.len());
        idxs.iter().zip(self.gs.iter()).map(|(i, g)| self.galois_group.pow(g, &int_cast(*i as i64, ZZbig, ZZi64)))
            .fold(self.galois_group().identity(), |current, next| self.galois_group().op(current, next))
    }

    ///
    /// Computes the "standard preimage" of the given `g` under `h`.
    /// 
    /// This is the vector `(a_0, a_1, ..., a_r)` such that `g = p^a_0 h(a_1, ..., a_r)` and
    /// `a_0 in { 0, ..., d - 1 }` and `a_i` for `i > 0` is within `{ 0, ..., l_i - 1 }`.
    /// 
    pub fn std_preimage<'a>(&'a self, g: &GaloisGroupEl) -> Cow<'a, [usize]> {
        let idx = self.representations.binary_search_by_key(&self.galois_group.representative(g), |(g, _)| self.galois_group.representative(g)).unwrap();
        return Cow::Borrowed(&self.representations[idx].1);
    }

    ///
    /// Computes the "signed standard preimage" of the given `g` under `h`.
    /// 
    /// This is the vector `(a_0, a_1, ..., a_r)` such that `g = p^a_0 h(a_1, ..., a_r)` and
    /// `a_0 in { (1 - d)/2, ..., (d - 1)/2 }` and `a_i` for `i > 0` is within `{ (1 - l_i)/2, ..., (l_i - 1)/2 }`
    /// (rounding every quotient towards negative infinity, if necessary).
    /// 
    pub fn std_preimage_signed<'a>(&'a self, g: &GaloisGroupEl) -> Cow<'a, [i64]> {
        Cow::Owned(
            self.std_preimage(&self.galois_group.op_ref(g, &self.signed_normalization_offset.1))
            .iter().copied().zip(self.signed_normalization_offset.0.iter().copied())
            .map(|(x, offset)| x as i64 - offset as i64)
            .collect::<Vec<_>>()
        )
    }

    ///
    /// Returns whether each dimension of the hypercube corresponds to a factor `m_i` of
    /// `m` (with `m_i` coprime to `m/m_i`). This is the case for the Halevi-Shoup hypercube,
    /// and very useful for the Slots-to-Coeffs transform. If this is the case, you can query
    /// the factor of `m` corresponding to some dimension by [`HypercubeStructure::factor_of_m()`].
    /// 
    pub fn is_tensor_product_compatible(&self) -> bool {
        match self.choice {
            HypercubeTypeData::CyclotomicTensorProductHypercube(_) => true,
            HypercubeTypeData::Generic => false
        }
    }

    ///
    /// Alias for [`HypercubeStructure::is_tensor_product_compatible()`].
    /// 
    pub fn is_halevi_shoup_hypercube(&self) -> bool {
        self.is_tensor_product_compatible()
    }

    ///
    /// Returns the factor `m_i` of `m` (coprime to `m/m_i`) which the `i`-th hypercube
    /// dimension corresponds to. This is only applicable if the hypercube was constructed
    /// from a (partial) factorization of `m`, i.e. [`HypercubeStructure::is_tensor_product_compatible()`]
    /// returns true. Otherwise, this function will return `None`.
    /// 
    pub fn factor_of_m(&self, dim_idx: usize) -> Option<i64> {
        assert!(dim_idx < self.dim_count());
        match &self.choice {
            HypercubeTypeData::CyclotomicTensorProductHypercube(factors_n) => Some(ZZi64.pow(factors_n[dim_idx].0, factors_n[dim_idx].1)),
            HypercubeTypeData::Generic => None
        }
    }

    ///
    /// Returns the distinguished Galois element `p`, also referred to as Frobenius automorphism.
    /// 
    pub fn p(&self) -> &GaloisGroupEl {
        &self.frobenius
    }

    ///
    /// Returns `p^e`, i.e. the `e`-th power of the Frobenius automorphism.
    /// 
    pub fn frobenius(&self, e: i64) -> GaloisGroupEl {
        self.galois_group.pow(self.p(), &int_cast(e, ZZbig, ZZi64))
    }

    ///
    /// Returns the rank `d` of the slot ring.
    /// 
    pub fn d(&self) -> usize {
        self.d
    }

    ///
    /// Returns the length `l_i` of the `i`-th hypercube dimension.
    /// 
    pub fn dim_length(&self, i: usize) -> usize {
        assert!(i < self.ls.len());
        self.ls[i]
    }

    ///
    /// Returns the generator `g_i` corresponding to the `i`-th hypercube dimension.
    /// 
    pub fn dim_generator(&self, i: usize) -> &GaloisGroupEl {
        assert!(i < self.ls.len());
        &self.gs[i]
    }

    ///
    /// Returns the order of `g_i` in the group `(Z/mZ)*`.
    /// 
    pub fn ord_generator(&self, i: usize) -> usize {
        assert!(i < self.ls.len());
        let result = self.ord_gs[i];
        debug_assert!(result % self.dim_length(i) == 0);
        return result;
    }

    ///
    /// Returns the number of dimensions in the hypercube.
    /// 
    pub fn dim_count(&self) -> usize {
        self.gs.len()
    }

    ///
    /// Alias for [`HypercubeStructure::element_count()`], which returns the
    /// number of elements in the hypercube.
    /// 
    /// When used to build a [`HypercubeIsomorphism`], this number is equal to the number 
    /// of slots the ring decomposes into, hence the name `slot_count()`.
    /// 
    /// [`HypercubeIsomorphism`]: crate::number_ring::hypercube::isomorphism::HypercubeIsomorphism
    /// 
    pub fn slot_count(&self) -> usize {
        self.element_count()
    }

    ///
    /// Returns the Galois group isomorphic to `(Z/mZ)*` that this hypercube
    /// describes.
    /// 
    pub fn galois_group(&self) -> &Subgroup<CyclotomicGaloisGroup> {
        &self.galois_group
    }

    ///
    /// Returns the number `l = prod_i l_i` of elements of `{ 0, ..., l_1 - 1 } x ... x { 0, ..., l_r - 1 }`
    /// or equivalently `(Z/mZ)*/<p>`, which is equal to the to the number of slots of 
    /// `Fp[X]/(Phi_m(X))`.
    /// 
    pub fn element_count(&self) -> usize {
        ZZi64.prod(self.ls.iter().map(|m_i| *m_i as i64)) as usize
    }

    ///
    /// Creates an iterator that yields a value for each element of `{ 0, ..., l_1 - 1 } x ... x { 0, ..., l_r - 1 }` 
    /// resp. `(Z/mZ)*/<p>`. Hence, these elements correspond to the slots of `Fp[X]/(Phi_m(X))`.
    /// 
    /// The given closure will be called on each element of `{ 0, ..., l_1 - 1 } x ... x { 0, ..., l_r - 1 }`.
    /// The returned iterator will iterate over the results of the closure.
    /// 
    pub fn hypercube_iter<'b, G, T>(&'b self, for_slot: G) -> impl ExactSizeIterator<Item = T> + use<'b, G, T>
        where G: 'b + Clone + FnMut(&[usize]) -> T,
            T: 'b
    {
        let mut it = multi_cartesian_product(
            self.ls.iter().map(|l| 0..*l),
            for_slot,
            |_, x| *x
        );
        (0..self.element_count()).map(move |_| it.next().unwrap())
    }

    ///
    /// Creates an iterator that one representative of each element of `(Z/mZ)*/<p>`, which
    /// also is in the image of this hypercube structure.
    /// 
    /// The order is compatible with [`HypercubeStructure::hypercube_iter()`].
    /// 
    pub fn element_iter<'b>(&'b self) -> impl ExactSizeIterator<Item = GaloisGroupEl> + use<'b> {
        self.hypercube_iter(|idxs| self.map_usize(idxs))
    }
}

impl Serialize for HypercubeStructure {

    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        #[derive(Serialize)]
        #[serde(rename = "HypercubeStructureData")]
        struct SerializableHypercubeStructureData<'a, G: Serialize> {
            frobenius: SerializeWithGroup<'a, &'a CyclotomicGaloisGroup>,
            d: usize,
            ls: &'a [usize],
            gs: G,
            choice: &'a HypercubeTypeData
        }

        SerializableNewtypeStruct::new("HypercubeStructure", (&self.galois_group, SerializableHypercubeStructureData {
            choice: &self.choice,
            d: self.d,
            frobenius: SerializeWithGroup::new(self.p(), self.galois_group().parent()),
            ls: &self.ls,
            gs: SerializableSeq::new_with_len(self.gs.iter().map(|g| SerializeWithGroup::new(g, self.galois_group().parent())), self.gs.len())
        })).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for HypercubeStructure {

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de>
    {
        struct DeserializeSeedHypercubeStructureData {
            galois_group: CyclotomicGaloisGroup
        }

        fn derive_single_galois_group_deserializer<'a>(deserializer: &'a DeserializeSeedHypercubeStructureData) -> DeserializeWithGroup<&'a CyclotomicGaloisGroup> {
            DeserializeWithGroup::new(&deserializer.galois_group)
        }

        fn derive_multiple_galois_group_deserializer<'de, 'a>(deserializer: &'a DeserializeSeedHypercubeStructureData) -> impl use<'a, 'de> + DeserializeSeed<'de, Value = Vec<GaloisGroupEl>> {
            DeserializeSeedSeq::new(
                std::iter::repeat(DeserializeWithGroup::new(&deserializer.galois_group)),
                Vec::new(),
                |mut current, next| { current.push(next); current }
            )
        }

        impl_deserialize_seed_for_dependent_struct!{
            pub struct HypercubeStructureData<'de> using DeserializeSeedHypercubeStructureData {
                frobenius: GaloisGroupEl: derive_single_galois_group_deserializer,
                d: usize: |_| PhantomData,
                ls: Vec<usize>: |_| PhantomData,
                gs: Vec<GaloisGroupEl>: derive_multiple_galois_group_deserializer,
                choice: HypercubeTypeData: |_| PhantomData
            }
        }

        let mut deserialized_galois_group = None;
        Ok(DeserializeSeedNewtypeStruct::new("HypercubeStructure", DeserializeSeedDependentTuple::new(
            PhantomData::<Subgroup<CyclotomicGaloisGroup>>,
            |galois_group| {
                let parent = galois_group.parent().clone();
                deserialized_galois_group = Some(galois_group);
                DeserializeSeedHypercubeStructureData { galois_group: parent }
            }
        )).deserialize(deserializer).map(|data| {
            let mut result = HypercubeStructure::new(deserialized_galois_group.take().unwrap(), data.frobenius, data.d, data.ls, data.gs);
            result.choice = data.choice;
            return result;
        }).unwrap())
    }
}

pub fn unit_group_dlog(ring: &Zn, base: ZnEl, value: ZnEl) -> Option<i64> {
    finite_field_discrete_log(
        value,
        base,
        ring
    )
}

#[test]
fn test_halevi_shoup_hypercube() {
    let galois_group = CyclotomicGaloisGroupBase::new(11 * 31).into().full_subgroup();
    let hypercube_structure = HypercubeStructure::halevi_shoup_hypercube(&galois_group, int_cast(2, ZZbig, ZZi64));
    assert_eq!(10, hypercube_structure.d());
    assert_eq!(2, hypercube_structure.dim_count());

    assert_eq!(1, hypercube_structure.dim_length(0));
    assert_eq!(30, hypercube_structure.dim_length(1));
}

#[test]
fn test_pow2_hypercube() {
    let galois_group = CyclotomicGaloisGroupBase::new(32).into().full_subgroup();
    let hypercube_structure = HypercubeStructure::default_pow2_hypercube(&galois_group, int_cast(7, ZZbig, ZZi64));
    assert_eq!(4, hypercube_structure.d());
    assert_eq!(1, hypercube_structure.dim_count());

    assert_eq!(4, hypercube_structure.dim_length(0));

    let galois_group = CyclotomicGaloisGroupBase::new(32).into().full_subgroup();
    let hypercube_structure = HypercubeStructure::default_pow2_hypercube(&galois_group, int_cast(17, ZZbig, ZZi64));
    assert_eq!(2, hypercube_structure.d());
    assert_eq!(2, hypercube_structure.dim_count());

    assert_eq!(4, hypercube_structure.dim_length(0));
    assert_eq!(2, hypercube_structure.dim_length(1));
}

#[test]
fn test_serialization() {
    for hypercube in [
        HypercubeStructure::halevi_shoup_hypercube(&CyclotomicGaloisGroupBase::new(11 * 31).into().full_subgroup(), int_cast(2, ZZbig, ZZi64)),
        HypercubeStructure::default_pow2_hypercube(&CyclotomicGaloisGroupBase::new(32).into().full_subgroup(), int_cast(7, ZZbig, ZZi64)),
        HypercubeStructure::default_pow2_hypercube(&CyclotomicGaloisGroupBase::new(32).into().full_subgroup(), int_cast(17, ZZbig, ZZi64))
    ] {
        let serializer = serde_assert::Serializer::builder().is_human_readable(true).build();
        let tokens = hypercube.serialize(&serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(true).build();
        let deserialized_hypercube = HypercubeStructure::deserialize(&mut deserializer).unwrap();

        assert!(hypercube.galois_group().get_group() == deserialized_hypercube.galois_group().get_group());
        assert_eq!(hypercube.dim_count(), deserialized_hypercube.dim_count());
        assert_eq!(hypercube.is_tensor_product_compatible(), deserialized_hypercube.is_tensor_product_compatible());
        for i in 0..hypercube.dim_count() {
            assert_eq!(hypercube.dim_length(i), deserialized_hypercube.dim_length(i));
            assert!(hypercube.galois_group().eq_el(hypercube.dim_generator(i), deserialized_hypercube.dim_generator(i)));
            assert_eq!(hypercube.ord_generator(i), deserialized_hypercube.ord_generator(i));
        }

        let serializer = serde_assert::Serializer::builder().is_human_readable(false).build();
        let tokens = hypercube.serialize(&serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(false).build();
        let deserialized_hypercube = HypercubeStructure::deserialize(&mut deserializer).unwrap();

        assert!(hypercube.galois_group().get_group() == deserialized_hypercube.galois_group().get_group());
        assert_eq!(hypercube.dim_count(), deserialized_hypercube.dim_count());
        assert_eq!(hypercube.is_tensor_product_compatible(), deserialized_hypercube.is_tensor_product_compatible());
        for i in 0..hypercube.dim_count() {
            assert_eq!(hypercube.dim_length(i), deserialized_hypercube.dim_length(i));
            assert!(hypercube.galois_group().eq_el(hypercube.dim_generator(i), deserialized_hypercube.dim_generator(i)));
            assert_eq!(hypercube.ord_generator(i), deserialized_hypercube.ord_generator(i));
        }
    }
}