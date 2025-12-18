use std::fmt::Debug;
use std::ops::Range;

use feanor_math::seq::VectorFn;

use crate::ciphertext_ring::indices::RNSFactorIndexList;

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
/// ```rust
/// # use feanor_math::seq::*;
/// # use anonymizedhelibrary::gadget_product::digits::*;
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
    /// # use anonymizedhelibrary::gadget_product::digits::*;
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
    /// # use anonymizedhelibrary::gadget_product::digits::*;
    /// # use anonymizedhelibrary::ciphertext_ring::indices::RNSFactorIndexList;
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
    /// # use anonymizedhelibrary::gadget_product::digits::*;
    /// # use anonymizedhelibrary::ciphertext_ring::indices::RNSFactorIndexList;
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
