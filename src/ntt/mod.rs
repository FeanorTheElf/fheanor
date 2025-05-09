use std::alloc::Global;

use feanor_math::algorithms::convolution::ntt::NTTConvolution;
use feanor_math::algorithms::convolution::PreparedConvolutionAlgorithm;
use feanor_math::ring::*;
use feanor_math::integer::IntegerRingStore;
use feanor_math::pid::EuclideanRingStore;
use feanor_math::rings::zn::*;

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

impl<R> HERingConvolution<R> for NTTConvolution<R, Global>
    where R: RingStore + Clone,
        R::Type: ZnRing
{
    fn new(ring: R, max_log2_len: usize) -> Self {
        assert!(ring.integer_ring().is_one(&ring.integer_ring().euclidean_rem(ring.integer_ring().clone_el(ring.modulus()), &ring.integer_ring().power_of_two(max_log2_len))));
        NTTConvolution::new_with(ring, Global)
    }

    fn ring(&self) -> &R {
        NTTConvolution::ring(self)
    }
}

#[cfg(feature = "use_hexl")]
impl HERingConvolution<zn_64::Zn> for feanor_math_hexl::conv::HEXLConvolution {

    fn new(ring: zn_64::Zn, max_log2_len: usize) -> Self {
        assert!(ring.integer_ring().is_one(&ring.integer_ring().euclidean_rem(ring.integer_ring().clone_el(ring.modulus()), &ring.integer_ring().power_of_two(max_log2_len + 1))));
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
/// Contains a dyn-compatible variant of [`PreparedConvolutionAlgorithm`].
/// This is useful if you want to create a ring but only know the type
/// of the convolution algorithm at runtime.
/// 
pub mod dyn_convolution;