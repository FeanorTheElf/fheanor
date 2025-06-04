use std::alloc::Global;

use feanor_math::algorithms::fft::*;
use feanor_math::algorithms::fft::cooley_tuckey::CooleyTuckeyFFT;
use feanor_math::algorithms::unity_root::get_prim_root_of_unity_pow2;
use feanor_math::algorithms::convolution::ntt::NTTConvolution;
use feanor_math::algorithms::convolution::ConvolutionAlgorithm;
use feanor_math::homomorphism::{CanHom, Identity};
use feanor_math::ring::*;
use feanor_math::integer::IntegerRingStore;
use feanor_math::pid::EuclideanRingStore;
use feanor_math::rings::zn::zn_64::{Zn, ZnBase, ZnFastmul, ZnFastmulBase};
use feanor_math::rings::zn::*;

///
/// A convolution as in [`ConvolutionAlgorithm`], that can additionally be created for
/// a given ring and length. This is required in many use cases within Fheanor.
/// 
pub trait HERingConvolution<R>: ConvolutionAlgorithm<R::Type>
    where R: RingStore
{
    fn ring(&self) -> RingRef<R::Type>;

    fn new(ring: R, max_log2_len: usize) -> Self;
}

impl<R> HERingConvolution<R> for NTTConvolution<R::Type, R::Type, Identity<R>>
    where R: RingStore + Clone,
        R::Type: ZnRing
{
    fn new(ring: R, max_log2_len: usize) -> Self {
        assert!(ring.integer_ring().is_one(&ring.integer_ring().euclidean_rem(ring.integer_ring().clone_el(ring.modulus()), &ring.integer_ring().power_of_two(max_log2_len))));
        NTTConvolution::new(ring)
    }

    fn ring(&self) -> RingRef<R::Type> {
        NTTConvolution::ring(self)
    }
}

impl HERingConvolution<Zn> for NTTConvolution<ZnBase, ZnFastmulBase, CanHom<ZnFastmul, Zn>> {

    fn new(ring: Zn, max_log2_len: usize) -> Self {
        assert!(ring.integer_ring().is_one(&ring.integer_ring().euclidean_rem(ring.integer_ring().clone_el(ring.modulus()), &ring.integer_ring().power_of_two(max_log2_len))));
        NTTConvolution::new_with(ring.into_can_hom(ZnFastmul::new(ring).unwrap()).ok().unwrap(), Global)
    }

    fn ring(&self) -> RingRef<ZnBase> {
        NTTConvolution::ring(self)
    }
}

#[cfg(feature = "use_hexl")]
impl HERingConvolution<zn_64::Zn> for feanor_math_hexl::conv::HEXLConvolution {

    fn new(ring: zn_64::Zn, max_log2_len: usize) -> Self {
        assert!(ring.integer_ring().is_one(&ring.integer_ring().euclidean_rem(ring.integer_ring().clone_el(ring.modulus()), &ring.integer_ring().power_of_two(max_log2_len + 1))));
        Self::new(ring, max_log2_len)
    }

    fn ring(&self) -> RingRef<feanor_math::rings::zn::zn_64::ZnBase> {
        RingRef::new(feanor_math_hexl::conv::HEXLConvolution::ring(&self).get_ring())
    }
}

///
/// An object that supports computing a negacyclic NTT, i.e the evaluation of a polynomial
/// at all primitive `m`-th roots of unity, where `m` is a power of two.
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
/// Negacyclic NTT, implemented using [`CooleyTuckeyFFT`] from `feanor-math`.
/// 
pub struct RustNegacyclicNTT<R>
    where R: RingStore,
        R::Type: ZnRing
{
    ring: R,
    fft_table: CooleyTuckeyFFT<R::Type, R::Type, Identity<R>>,
    twiddles: Vec<El<R>>,
    inv_twiddles: Vec<El<R>>,
}

impl<R> PartialEq for RustNegacyclicNTT<R> 
    where R: RingStore,
        R::Type: ZnRing
{
    fn eq(&self, other: &Self) -> bool {
        self.fft_table == other.fft_table && self.ring.eq_el(&self.twiddles[0], &other.twiddles[0])
    }
}

impl<R> HERingNegacyclicNTT<R> for RustNegacyclicNTT<R> 
    where R: RingStore + Clone,
        R::Type: ZnRing
{
    fn bitreversed_negacyclic_fft_base<const INV: bool>(&self, input: &mut [El<R>], output: &mut [El<R>]) {
        assert_eq!(self.fft_table.len(), input.len());
        assert_eq!(self.fft_table.len(), output.len());
        if INV {
            self.fft_table.unordered_inv_fft(&mut input[..], &self.ring);
            for i in 0..input.len() {
                output[i] = self.ring.mul_ref(&mut input[i], &self.twiddles[i]);
            }
        } else {
            for i in 0..input.len() {
                output[i] = self.ring.mul_ref(&mut input[i], &self.inv_twiddles[i]);
            }
            self.fft_table.unordered_fft(&mut output[..], &self.ring);
        }
    }

    fn ring(&self) -> &R {
        &self.ring
    }

    fn len(&self) -> usize {
        self.fft_table.len()
    }

    fn new(Fp: R, log2_rank: usize) -> Self {
        let rank = 1 << log2_rank;
        let mut twiddles = Vec::with_capacity(rank as usize);
        let mut inv_twiddles = Vec::with_capacity(rank as usize);

        let Fp_as_field = (&Fp).as_field().ok().unwrap();
        let root_of_unity = get_prim_root_of_unity_pow2(&Fp_as_field, log2_rank + 1).unwrap();
        let zeta = Fp_as_field.get_ring().unwrap_element(root_of_unity);

        let mut current = Fp.one();
        let mut current_inv = Fp.one();
        let zeta_inv = Fp.pow(Fp.clone_el(&zeta), 2 * rank as usize - 1);
        for _ in 0..rank {
            twiddles.push(Fp.clone_el(&current));
            inv_twiddles.push(Fp.clone_el(&current_inv));
            Fp.mul_assign_ref(&mut current, &zeta);
            Fp.mul_assign_ref(&mut current_inv, &zeta_inv);
        }

        let zeta_sqr = Fp.pow(Fp.clone_el(&zeta), 2);
        let fft_table = CooleyTuckeyFFT::new(Fp.clone(), zeta_sqr, log2_rank);

        return Self {
            ring: Fp,
            fft_table: fft_table,
            inv_twiddles: inv_twiddles,
            twiddles: twiddles
        };
    }
}

#[cfg(feature = "use_hexl")]
impl HERingNegacyclicNTT<Zn> for feanor_math_hexl::hexl::HEXLNegacyclicNTT {

    fn bitreversed_negacyclic_fft_base<const INV: bool>(&self, input: &mut [El<Zn>], output: &mut [El<Zn>]) {
        feanor_math_hexl::hexl::HEXLNegacyclicNTT::unordered_negacyclic_fft_base::<INV>(self, input, output)
    }

    fn len(&self) -> usize {
        feanor_math_hexl::hexl::HEXLNegacyclicNTT::n(self)
    }

    fn new(ring: Zn, log2_rank: usize) -> Self {
        feanor_math_hexl::hexl::HEXLNegacyclicNTT::for_zn(ring, log2_rank).unwrap()
    }

    fn ring(&self) -> &Zn {
        feanor_math_hexl::hexl::HEXLNegacyclicNTT::ring(self)
    }
}


///
/// Contains a dyn-compatible variant of [`ConvolutionAlgorithm`].
/// This is useful if you want to create a ring but only know the type
/// of the convolution algorithm at runtime.
/// 
pub mod dyn_convolution;