use std::fmt::Display;
use std::ops::{Deref, Range};

use feanor_math::seq::VectorFn;

///
/// A decomposition of the numbers `0..rns_len` into ranges, which we call digits.
/// 
/// The main use case is the construction of RNS gadget vectors, which are of the
/// form
/// ```text
///   g[i] = 1 mod pj  if j in digits[i]
///   g[i] = 0 mod pj  otherwise
/// ```
/// for a list of digits `digits` and `p0, ..., p(rns_len - 1)` being the RNS factors.
/// 
/// This trait (and many other components in Fheanor) currently do not support
/// digits that are not a contiguous range of indices. More concretely, it would make
/// sense to decompose `0..6` into digits as `{0, 2, 3}, {1, 4, 5}`, but this is not
/// supported. The reason is that this allows us to take slices of data corresponding
/// to RNS factors, and get only the data corresponding to a single digit (hence avoid
/// copying the data around).
/// 
/// # Example
/// ```
/// # use feanor_math::seq::*;
/// # use fheanor::gadget_product::digits::*;
/// let digits = RNSGadgetVectorDigitIndices::from([3..7, 0..3, 7..10].clone_els());
/// assert_eq!(3, digits.len());
/// 
/// // the digits will be stored in an ordered way
/// assert_eq!(0..3, digits.at(0));
/// assert_eq!(3..7, digits.at(1));
/// assert_eq!(7..10, digits.at(2));
/// 
/// assert_eq!(10, digits.rns_base_len());
/// ```
/// 
/// # Why do we call it "digits"?
/// 
/// This comes from the beginnings of modulus-switching. Instead of the much more efficient
/// RNS gadget vector, the first idea was to use a `B`-adic decomposition of `x` as
/// ```text
///   x = x[0] + B x[1] + B^2 x[2] + ...
/// ```
/// In this case, the entries of the gadget vector where powers of `B`, hence each associated to 
/// a digit in the `B`-adic decomposition of some unspecified `x`. With an RNS gadget vector, the 
/// "digits" are now the groups of RNS factors `pi, ..., p(i + d)` according to which we decompose
/// the input. While this is not a standard naming convention, it makes sense (to me at least).
/// 
#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct RNSGadgetVectorDigitIndices {
    digit_boundaries: [usize]
}

impl RNSGadgetVectorDigitIndices {

    fn from_unchecked(digit_boundaries: Box<[usize]>) -> Box<Self> {
        unsafe { std::mem::transmute(digit_boundaries) }
    }

    ///
    /// Creates the list of digits, each containing the RNS factors whose indices are within the corresponding 
    /// range. This requires the ranges to exactly cover a contiguous interval `{ 0, 1, ..., k - 1 }`, otherwise
    /// the function will panic. 
    /// 
    pub fn from<V>(digits: V) -> Box<Self>
        where V: VectorFn<Range<usize>>
    {
        let mut result: Vec<usize> = Vec::with_capacity(digits.len());
        for _ in 0..digits.len() {
            let mut it = digits.iter().filter(|digit| digit.start == *result.last().unwrap_or(&0));
            if let Some(next) = it.next() {
                if it.next().is_some() {
                    panic!("multiple digits start at {}", result.last().unwrap_or(&0));
                }
                result.push(next.end);
            } else {
                panic!("no digit contains {}", result.last().unwrap_or(&0));
            }
        }
        return Self::from_unchecked(result.into_boxed_slice());
    }

    ///
    /// Returns the number of RNS factors in the RNS basis that these digits refer
    /// to. In other words, returns `k` such that the indices `{ 0, 1, ..., k - 1 }`
    /// are each part of exactly one of the digits.
    /// 
    pub fn rns_base_len(&self) -> usize {
        *self.digit_boundaries.last().unwrap_or(&0)
    }

    ///
    /// Computes a balanced decomposition of `0..rns_base_len` into `digits` digits, which
    /// is often the best choice for an RNS gadget vector.
    /// 
    /// # Example
    /// ```
    /// # use feanor_math::seq::*;
    /// # use fheanor::gadget_product::digits::*;
    /// let digits = RNSGadgetVectorDigitIndices::select_digits(3, 10);
    /// assert_eq!(3, digits.len());
    /// assert_eq!(0..4, digits.at(0));
    /// assert_eq!(4..7, digits.at(1));
    /// assert_eq!(7..10, digits.at(2));
    /// ```
    /// 
    pub fn select_digits(digits: usize, rns_base_len: usize) -> Box<Self> {
        assert!(digits <= rns_base_len, "the number of gadget product digits may not exceed the number of RNS factors");
        let moduli_per_small_digit = rns_base_len / digits;
        let large_digits = rns_base_len % digits;
        let small_digits = digits - large_digits;
        let mut result = Vec::with_capacity(digits);
        let mut current = 0;
        for _ in 0..large_digits {
            current += moduli_per_small_digit + 1;
            result.push(current);
        }
        for _ in 0..small_digits {
            current += moduli_per_small_digit;
            result.push(current);
        }
        return Self::from_unchecked(result.into_boxed_slice());
    }

    ///
    /// Removes the given indices from each digit, and returns the resulting
    /// list of shorter digits.
    /// 
    /// # Example
    /// ```
    /// # use feanor_math::seq::*;
    /// # use fheanor::gadget_product::digits::*;
    /// let original_digits = RNSGadgetVectorDigitIndices::from([0..3, 3..5, 5..7].clone_els());
    /// let digits = original_digits.remove_indices(RNSFactorIndexList::from_ref(&[1, 2, 5], 7));
    /// assert_eq!(3, digits.len());
    /// assert_eq!(0..1, digits.at(0));
    /// assert_eq!(1..3, digits.at(1));
    /// assert_eq!(3..4, digits.at(2));
    /// ```
    /// If all indices from a given digit are removed, the whole digit is removed.
    /// ```
    /// # use feanor_math::seq::*;
    /// # use fheanor::gadget_product::digits::*;
    /// let original_digits = RNSGadgetVectorDigitIndices::from([0..3, 3..5, 5..7].clone_els());
    /// let digits = original_digits.remove_indices(RNSFactorIndexList::from_ref(&[0, 1, 2, 5], 7));
    /// assert_eq!(2, digits.len());
    /// assert_eq!(0..2, digits.at(0));
    /// assert_eq!(2..3, digits.at(1));
    /// ```
    /// 
    pub fn remove_indices(&self, drop_rns_factors: &RNSFactorIndexList) -> Box<Self> {
        for i in drop_rns_factors.iter() {
            assert!(*i < self.rns_base_len());
        }
        let mut result = Vec::new();
        let mut current_len = 0;
        for range in self.iter() {
            let dropped_els = drop_rns_factors.num_within(&range);
            if dropped_els != range.end - range.start {
                current_len += range.end - range.start - dropped_els;
                result.push(current_len);
            }
        }
        debug_assert!(*result.last().unwrap_or(&0) == self.rns_base_len() - drop_rns_factors.len());
        return Self::from_unchecked(result.into_boxed_slice());
    }
}

impl VectorFn<Range<usize>> for RNSGadgetVectorDigitIndices {

    fn len(&self) -> usize {
        self.digit_boundaries.len()
    }

    fn at(&self, i: usize) -> Range<usize> {
        if i == 0 {
            0..self.digit_boundaries[0]
        } else {
            self.digit_boundaries[i - 1]..self.digit_boundaries[i]
        }
    }
}

impl Clone for Box<RNSGadgetVectorDigitIndices> {

    fn clone(&self) -> Self {
        RNSGadgetVectorDigitIndices::from_unchecked(self.digit_boundaries.to_owned().into_boxed_slice())
    }
}

impl ToOwned for RNSGadgetVectorDigitIndices {
    type Owned = Box<Self>;

    fn to_owned(&self) -> Self::Owned {
        RNSGadgetVectorDigitIndices::from_unchecked(self.digit_boundaries.to_owned().into_boxed_slice())
    }
}

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

    pub fn from(mut indices: Vec<usize>, rns_base_len: usize) -> Box<Self> {
        Self::check_valid(&indices, rns_base_len);
        indices.sort_unstable();
        return Self::from_unchecked(indices.into_boxed_slice());
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
    /// # use fheanor::gadget_product::digits::*;
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
    /// # use fheanor::gadget_product::digits::*;
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
    /// # use fheanor::gadget_product::digits::*;
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
