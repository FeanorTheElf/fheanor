use feanor_math::algorithms::convolution::PreparedConvolutionAlgorithm;
use feanor_math::ring::*;

///
/// A convolution as in [`PreparedConvolutionAlgorithm`], that can additionally be created for
/// a given ring and length. This is required in many use cases within Fheanor.
/// 
pub trait HERingConvolution<R>: PreparedConvolutionAlgorithm<R::Type>
    where R: RingStore
{
    fn ring(&self) -> &R;

    fn new(ring: R, max_log2_len: usize) -> Self;
}

#[cfg(feature = "use_hexl")]
impl HERingConvolution<feanor_math::rings::zn::zn_64::Zn> for feanor_math_hexl::conv::HEXLConvolution {

    fn new(ring: feanor_math::rings::zn::zn_64::Zn, max_log2_len: usize) -> Self {
        Self::new(ring, max_log2_len)
    }

    fn ring(&self) -> &feanor_math::rings::zn::zn_64::Zn {
        feanor_math_hexl::conv::HEXLConvolution::ring(&self)
    }
}

///
/// An object that supports computing a negacyclic NTT, i.e the evaluation of a polynomial
/// at all primitive `n`-th roots of unity, where `n` is a power of two.
/// 
pub trait HERingNegacyclicNTT<R>: PartialEq
    where R: RingStore
{
    ///
    /// Should assign to `output` the bitreversed and negacyclic NTT of `input`, i.e. the evaluation
    /// at all primitive `(2 * self.len())`-th roots of unity.
    /// 
    /// Concretely, the `i`-th element of `output` should store the evaluation of `input` (interpreted
    /// as a polynomial) at `𝝵^(bitrev(i) * 2 + 1)`.
    /// 
    fn bitreversed_negacyclic_fft_base<const INV: bool>(&self, input: &mut [El<R>], output: &mut [El<R>]);

    fn ring(&self) -> &R;

    fn len(&self) -> usize;

    fn new(ring: R, log2_rank: usize) -> Self;
}

///
/// Contains an implementation of [`HERingConvolution`] based on NTTs.
/// 
pub mod ntt_convolution;

///
/// Contains a dyn-compatible variant of [`PreparedConvolutionAlgorithm`].
/// This is useful if you want to create a ring but only know the type
/// of the convolution algorithm at runtime.
/// 
pub mod dyn_convolution;