use feanor_math::ring::RingBase;


///
/// A ring whose elements have a "prepared multiplication"-representation, such that elements
/// in this representation can be multiplied faster than in their standard representation.
/// 
pub trait PreparedMultiplicationRing: RingBase {

    type PreparedMultiplicant;

    ///
    /// Converts an element of the ring into a `PreparedMultiplicant`, which can then be used
    /// to compute multiplications by this element faster.
    /// 
    fn prepare_multiplicant(&self, x: &Self::Element) -> Self::PreparedMultiplicant;

    ///
    /// Computes the product of two elements that have previously been "prepared" via
    /// [`PreparedMultiplicationRing::prepare_multiplicant()`].
    /// 
    fn mul_prepared(&self, lhs: &Self::Element, lhs_prep: Option<&Self::PreparedMultiplicant>, rhs: &Self::Element, rhs_prep: Option<&Self::PreparedMultiplicant>) -> Self::Element;

    ///
    /// Computes a fused-multiply-add where the factors have previously been "prepared"
    /// [`PreparedMultiplicationRing::prepare_multiplicant()`].
    /// 
    /// A fused-multiply-add refers to the operation `lhs * rhs + dst`.
    /// 
    fn fma_prepared(&self, lhs: &Self::Element, lhs_prep: Option<&Self::PreparedMultiplicant>, rhs: &Self::Element, rhs_prep: Option<&Self::PreparedMultiplicant>, mut dst: Self::Element) -> Self::Element {
        self.add_assign(&mut dst, self.mul_prepared(lhs, lhs_prep, rhs, rhs_prep));
        return dst;
    }

    ///
    /// Computes the inner product of two vectors over this ring, whose elements have previously
    /// been "prepared" via [`PreparedMultiplicationRing::prepare_multiplicant()`].
    /// 
    fn inner_product_prepared<'a, I>(&self, parts: I) -> Self::Element
        where I: IntoIterator<Item = (&'a Self::Element, Option<&'a Self::PreparedMultiplicant>, &'a Self::Element, Option<&'a Self::PreparedMultiplicant>)>,
            I::IntoIter: ExactSizeIterator,
            Self: 'a
    {
        parts.into_iter().fold(self.zero(), |current, (lhs, lhs_prep, rhs, rhs_prep)| self.add(current, self.mul_prepared(lhs, lhs_prep, rhs, rhs_prep)))
    }
}
