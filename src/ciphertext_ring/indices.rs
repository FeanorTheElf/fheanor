
use std::fmt::{Debug, Display};
use std::marker::PhantomData;
use std::ops::{Deref, Range};

use feanor_math::integer::int_cast;
use feanor_math::ring::*;
use feanor_math::rings::zn::{ZnRing, ZnRingStore};
use feanor_math::seq::VectorView;

use crate::ZZbig;

///
/// Thin wrapper around ordered slices `[usize]`, used to store a set of indices
/// of RNS factors. In most cases, it refers to those RNS factors that should be
/// dropped from a "master RNS base" to get to the current state.
/// 
#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct RNSFactorIndexList {
    rns_factor_indices: [usize]
}

impl Deref for RNSFactorIndexList {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.rns_factor_indices
    }
}

impl Display for RNSFactorIndexList {

    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.rns_factor_indices.len() == 0 {
            return write!(f, "[]");
        } else {
            write!(f, "[{}", self.rns_factor_indices[0])?;
            for x in &self.rns_factor_indices[1..] {
                write!(f, ", {}", x)?;
            }
            return write!(f, "]");
        }
    }
}

impl RNSFactorIndexList {

    fn from_unchecked(indices: Box<[usize]>) -> Box<Self> {
        unsafe { std::mem::transmute(indices) }
    }

    fn from_ref_unchecked<'a>(indices: &'a [usize]) -> &'a Self {
        return unsafe { std::mem::transmute(indices) };
    }

    fn check_valid(indices: &[usize], rns_base_len: usize) {
        for i in indices {
            assert!(*i < rns_base_len, "all indices must be valid for an RNS base of length {}, but found {}", rns_base_len, *i);
        }
        for (i0, j0) in indices.iter().enumerate() {
            for (i1, j1) in indices.iter().enumerate() {
                assert!(i0 == i1 || j0 != j1, "all indices must be distinct, but found indices[{}] == {} == indices[{}]", i0, j0, i1);
            }
        }
    }

    pub fn from_ref<'a>(indices: &'a [usize], rns_base_len: usize) -> &'a Self {
        Self::check_valid(indices, rns_base_len);
        assert!(indices.is_sorted());
        return Self::from_ref_unchecked(indices);
    }

    pub fn from_ref_unsorted<'a>(indices: &'a mut [usize], rns_base_len: usize) -> &'a Self {
        Self::check_valid(indices, rns_base_len);
        indices.sort_unstable();
        return Self::from_ref_unchecked(indices);
    }

    pub fn from<I: IntoIterator<Item = usize>>(indices: I, rns_base_len: usize) -> Box<Self> {
        let mut indices = indices.into_iter().collect::<Vec<_>>();
        Self::check_valid(&indices, rns_base_len);
        indices.sort_unstable();
        return Self::from_unchecked(indices.into_boxed_slice());
    }

    pub fn missing_from<V1, V2, R>(new: V1, master: V2) -> Box<Self>
        where V1: VectorView<R>,
            V2: VectorView<R>,
            R: RingStore
    {
        if master.len() == 0 {
            return Self::empty();
        }
        let mut result = Vec::new();
        for i in 0..master.len() {
            if new.as_iter().all(|ring| ring.get_ring() != master.at(i).get_ring()) {
                result.push(i);
            }
        }
        return Self::from(result, master.len());
    }

    pub fn missing_from_subset<V1, V2, R>(subset: V1, master: V2) -> Result<Box<Self>, RNSFactorsNotASubset<V1, V2, R>>
        where V1: VectorView<R>,
            V2: VectorView<R>,
            R: RingStore,
            R::Type: ZnRing
    {
        let subset_len = subset.len();
        let master_len = master.len();
        let result = Self::missing_from(&subset, &master);
        if result.len() + subset_len == master_len {
            return Ok(result);
        } else {
            return Err(RNSFactorsNotASubset::new(subset, master));
        }
    }

    pub fn contains(&self, i: usize) -> bool {
        self.rns_factor_indices.binary_search(&i).is_ok()
    }

    pub fn contains_all(&self, subset: &Self) -> bool {
        subset.iter().all(|i| self.contains(*i))
    }

    ///
    /// Returns the number of indices in this set within the given range.
    /// 
    /// # Example
    /// ```
    /// # use fheanor::ciphertext_ring::indices::RNSFactorIndexList;
    /// assert_eq!(1, RNSFactorIndexList::from_ref(&[2, 5], 8).num_within(&(0..5)));
    /// ```
    /// 
    pub fn num_within(&self, range: &Range<usize>) -> usize {
        match (self.rns_factor_indices.binary_search(&range.start), self.rns_factor_indices.binary_search(&range.end)) {
            (Ok(i), Ok(j)) |
            (Ok(i), Err(j)) |
            (Err(i), Ok(j)) |
            (Err(i), Err(j)) => j - i
        }
    }

    pub fn subtract(&self, other: &Self) -> Box<Self> {
        Self::from_unchecked(self.rns_factor_indices.iter().copied().filter(|i| !other.contains(*i)).collect())
    }

    pub fn intersect(&self, other: &Self) -> Box<Self> {
        Self::from_unchecked(self.rns_factor_indices.iter().copied().filter(|i| other.contains(*i)).collect())
    }

    ///
    /// Returns the indices contained in `self` but not in `context`, however - as opposed to
    /// [`RNSFactorIndexList::subtract()`] - relative to the RNS base that has `context` already removed.
    /// This assumes that `context` is a subset of `self`.
    /// 
    /// More concretely, this returns
    /// ```text
    ///   { i - #{ j in context | j < i } | i in self \ context }
    /// ```
    /// 
    /// **Note for mathematicians**: This has nothing to do with the category-theoretical pushforward
    /// 
    /// # Example
    /// ```
    /// # use fheanor::ciphertext_ring::indices::RNSFactorIndexList;
    /// assert_eq!(&[1usize, 3, 5][..], &RNSFactorIndexList::from_ref(&[1, 2, 4, 5, 7], 8).pushforward(RNSFactorIndexList::from_ref(&[2, 5], 8)) as &[usize])
    /// ```
    /// 
    pub fn pushforward(&self, context: &Self) -> Box<Self> {
        if self.len() == 0 {
            assert!(context.len() == 0);
            return Self::empty();
        }
        let mut result = Vec::with_capacity(self.len() - context.len());
        let mut current = 0;
        let largest = self[self.len() - 1];
        assert!(context.len() == 0 || context[context.len() - 1] <= largest);

        // I guess this could be optimized, but it's fast enough
        for i in 0..=largest {
            if context.contains(i) {
                continue;
            }
            if self.contains(i) {
                result.push(current);
            }
            current += 1;
        }
        assert!(result.len() == self.len() - context.len());
        return Self::from_unchecked(result.into_boxed_slice());
    }

    ///
    /// Returns the indices of the elements that will removed when first removing `context`,
    /// and then removing `self` w.r.t. the new RNS base that already has `context` removed.
    /// In this sense, it is the counterpart to [`RNSFactorIndexList::pushforward()`].
    /// 
    /// More concretely, this returns
    /// ```text
    ///   { i | i - #{ j in context | j < i } in self } + context
    /// ```
    /// 
    /// **Note for mathematicians**: This has nothing to do with the category-theoretical pullback
    /// 
    /// # Example
    /// ```
    /// # use fheanor::ciphertext_ring::indices::RNSFactorIndexList;
    /// assert_eq!(&[1, 2, 3, 5, 6][..], &RNSFactorIndexList::from_ref(&[1, 2, 4], 6).pullback(RNSFactorIndexList::from_ref(&[2, 5], 8)) as &[usize])
    /// ```
    /// 
    pub fn pullback(&self, context: &Self) -> Box<Self> {
        let mut result = Vec::new();
        for mut i in self.iter().copied() {
            let mut added = 0..(i + 1);
            while added.start != added.end {
                let new_els = context.num_within(&added);
                added = (i + 1)..(i + new_els + 1);
                i += new_els;
            }
            result.push(i);
        }
        result.extend(context.iter().copied());
        result.sort_unstable();
        return Self::from_unchecked(result.into_boxed_slice());
    }

    pub fn union(&self, other: &Self) -> Box<Self> {
        let mut result = self.rns_factor_indices.iter().copied().chain(
            other.rns_factor_indices.iter().copied().filter(|i| !self.contains(*i)
        )).collect::<Box<[usize]>>();
        result.sort_unstable();
        return Self::from_unchecked(result);
    }

    pub fn empty() -> Box<Self> {
        Self::from_unchecked(Box::new([]))
    }

    pub fn empty_ref() -> &'static Self {
        Self::from_ref_unchecked(&[])
    }

    pub fn complement(&self, rns_base_len: usize) -> Box<Self> {
        let mut result = Vec::with_capacity(rns_base_len - self.len());
        let mut idx = 0;
        for current in 0..rns_base_len {
            debug_assert!(idx == self.len() || current <= self[idx]);
            if idx < self.len() && current == self[idx] {
                idx += 1;
            } else {
                result.push(current);
            }
        }
        debug_assert_eq!(rns_base_len, result.len() + self.len());
        return Self::from_unchecked(result.into_boxed_slice());
    }
}

impl Clone for Box<RNSFactorIndexList> {
    
    fn clone(&self) -> Self {
        RNSFactorIndexList::to_owned(&self)
    }
}

impl ToOwned for RNSFactorIndexList {
    type Owned = Box<Self>;

    fn to_owned(&self) -> Self::Owned {
        RNSFactorIndexList::from_unchecked(self.rns_factor_indices.to_owned().into_boxed_slice())
    }
}

///
/// Error returned by [`RNSFactorIndexList::missing_from_subset()`] if the 
/// given subset is not actually a subset of the superset.
/// 
pub struct RNSFactorsNotASubset<V1, V2, R>
    where V1: VectorView<R>,
        V2: VectorView<R>,
        R: RingStore,
        R::Type: ZnRing
{
    not_a_subset: V1,
    superset: V2,
    ring: PhantomData<R>
}

impl<V1, V2, R> RNSFactorsNotASubset<V1, V2, R>
    where V1: VectorView<R>,
        V2: VectorView<R>,
        R: RingStore,
        R::Type: ZnRing
{
    pub fn new(not_a_subset: V1, superset: V2) -> Self {
        Self { not_a_subset, superset, ring: PhantomData }
    }
}

impl<V1, V2, R> Debug for RNSFactorsNotASubset<V1, V2, R>
    where V1: VectorView<R>,
        V2: VectorView<R>,
        R: RingStore,
        R::Type: ZnRing
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "the set of RNS factors {:?} is not a subset of {:?}", 
            self.not_a_subset.as_iter().map(|ring| int_cast(ring.integer_ring().clone_el(ring.modulus()), ZZbig, ring.integer_ring())).collect::<Vec<_>>().iter().map(|x| ZZbig.format(x)).collect::<Vec<_>>(),
            self.superset.as_iter().map(|ring| int_cast(ring.integer_ring().clone_el(ring.modulus()), ZZbig, ring.integer_ring())).collect::<Vec<_>>().iter().map(|x| ZZbig.format(x)).collect::<Vec<_>>(),
        )
    }
}

#[cfg(test)]
use feanor_math::rings::zn::zn_64::*;

#[test]
fn test_missing_from_subset() {
    feanor_tracing::DelayedLogger::init_test();
    let master = [Zn::new(3), Zn::new(19), Zn::new(7)];
    let subset = [Zn::new(3), Zn::new(19)];
    let expected = [2];
    assert_eq!(&expected, &**RNSFactorIndexList::missing_from_subset(&subset, &master).unwrap());

    let master = [Zn::new(3), Zn::new(19), Zn::new(7)];
    let subset = [Zn::new(5), Zn::new(19)];
    assert!(RNSFactorIndexList::missing_from_subset(&subset, &master).is_err());
}

#[test]
fn test_complement() {
    feanor_tracing::DelayedLogger::init_test();
    let list = RNSFactorIndexList::from(vec![0, 2, 3, 6], 7);
    let expected = RNSFactorIndexList::from(vec![1, 4, 5], 7);
    assert_eq!(&**expected, &**list.complement(7));
}