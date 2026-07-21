use std::alloc::Global;

use feanor_math::algorithms::fft::bluestein::BluesteinFFT;
use feanor_math::algorithms::fft::*;
use feanor_math::algorithms::fft::cooley_tuckey::*;
use feanor_math::algorithms::unity_root::*;
use feanor_math::algorithms::convolution::ntt::NTTConvolution;
use feanor_math::algorithms::convolution::ConvolutionAlgorithm;
use feanor_math::computation::no_error;
use feanor_math::homomorphism::*;
use feanor_math::ring::*;
use feanor_math::integer::{int_cast, BigIntRing, IntegerRingStore};
use feanor_math::pid::EuclideanRingStore;
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::zn::zn_64::{Zn, ZnBase, ZnFastmul, ZnFastmulBase};
use feanor_math::rings::zn::*;

///
/// A convolution as in [`ConvolutionAlgorithm`], that can additionally be created for
/// a given ring and length. This is required in many use cases within Fheanor.
/// 
pub trait FheanorConvolution<R>: ConvolutionAlgorithm<R::Type>
    where R: RingStore
{
    fn ring(&self) -> RingRef<'_, R::Type>;

    fn new(ring: R, max_log2_len: usize) -> Self;
}

impl<R> FheanorConvolution<R> for NTTConvolution<R::Type, R::Type, Identity<R>>
    where R: RingStore + Clone,
        R::Type: ZnRing
{
    fn new(ring: R, max_log2_len: usize) -> Self {
        assert!(ring.integer_ring().is_one(&ring.integer_ring().euclidean_rem(ring.integer_ring().clone_el(ring.modulus()), &ring.integer_ring().power_of_two(max_log2_len))));
        NTTConvolution::new(ring)
    }

    fn ring(&self) -> RingRef<'_, R::Type> {
        NTTConvolution::ring(self)
    }
}

impl FheanorConvolution<Zn> for NTTConvolution<ZnBase, ZnFastmulBase, CanHom<ZnFastmul, Zn>> {

    fn new(ring: Zn, max_log2_len: usize) -> Self {
        assert!(ring.integer_ring().is_one(&ring.integer_ring().euclidean_rem(ring.integer_ring().clone_el(ring.modulus()), &ring.integer_ring().power_of_two(max_log2_len))));
        NTTConvolution::new_with_hom(ring.into_can_hom(ZnFastmul::new(ring).unwrap()).ok().unwrap(), Global)
    }

    fn ring(&self) -> RingRef<'_, ZnBase> {
        NTTConvolution::ring(self)
    }
}

#[cfg(feature = "use_hexl")]
impl FheanorConvolution<zn_64::Zn> for feanor_math_hexl::conv::HEXLConvolution {

    fn new(ring: zn_64::Zn, max_log2_len: usize) -> Self {
        assert!(ring.integer_ring().is_one(&ring.integer_ring().euclidean_rem(ring.integer_ring().clone_el(ring.modulus()), &ring.integer_ring().power_of_two(max_log2_len + 1))));
        Self::new(ring, max_log2_len)
    }

    fn ring(&self) -> RingRef<'_, feanor_math::rings::zn::zn_64::ZnBase> {
        RingRef::new(feanor_math_hexl::conv::HEXLConvolution::ring(&self).get_ring())
    }
}

///
/// An object that supports computing a negacyclic NTT, i.e the evaluation of a polynomial
/// at all primitive `m`-th roots of unity, where `m` is a power of two.
/// 
pub trait FheanorNegacyclicNTT<R>: PartialEq + Send + Sync
    where R: RingStore
{
    ///
    /// Should assign to `output` the bitreversed and negacyclic NTT of `input`, i.e. the evaluation
    /// at all primitive `(2 * self.len())`-th roots of unity.
    /// 
    /// Concretely, the `i`-th element of `output` should store the evaluation of `input` (interpreted
    /// as a polynomial) at `𝝵^(bitrev(i) * 2 + 1)`.
    /// 
    /// The implementation may overwrite the values of input with arbitrary (but safe) values.
    /// 
    fn bitreversed_negacyclic_fft_base<const INV: bool>(&self, input: &mut [El<R>], output: &mut [El<R>]);

    fn ring(&self) -> RingRef<'_, R::Type>;

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

impl<R> RustNegacyclicNTT<R> 
    where R: RingStore + Clone,
        R::Type: ZnRing
{
    ///
    /// Creates a new negacyclic NTT, using the given primitive
    /// `m`-th root of unity.
    /// 
    /// Concretely, when computing the NTT, the `i`-th element of the output will
    /// store the evaluation of input (interpreted as a polynomial) at `zeta^-(bitrev(i) * 2 + 1)`.
    /// Note that the `-` in the exponent is standard convention for the DFT.
    /// 
    pub fn new_with_root_of_unity(Fp: R, zeta: El<R>, log2_rank: usize) -> Self {
        assert!(is_prim_root_of_unity_pow2(&Fp, &zeta, log2_rank + 1));
        let rank = 1 << log2_rank;
        let mut twiddles = Vec::with_capacity(rank as usize);
        let mut inv_twiddles = Vec::with_capacity(rank as usize);

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

impl<R> FheanorNegacyclicNTT<R> for RustNegacyclicNTT<R> 
    where R: RingStore + Clone + Send + Sync,
        El<R>: Send + Sync,
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

    fn ring(&self) -> RingRef<'_, R::Type> {
        RingRef::new(self.ring.get_ring())
    }

    fn len(&self) -> usize {
        self.fft_table.len()
    }

    fn new(Fp: R, log2_rank: usize) -> Self {
        let zeta = get_prim_root_of_unity_zn(&Fp, 1 << (log2_rank + 1)).unwrap();
        return Self::new_with_root_of_unity(Fp, zeta, log2_rank);
    }
}

#[cfg(feature = "use_hexl")]
impl FheanorNegacyclicNTT<Zn> for feanor_math_hexl::hexl::HEXLNegacyclicNTT {

    fn bitreversed_negacyclic_fft_base<const INV: bool>(&self, input: &mut [El<Zn>], output: &mut [El<Zn>]) {
        feanor_math_hexl::hexl::HEXLNegacyclicNTT::unordered_negacyclic_fft_base::<INV>(self, input, output)
    }

    fn len(&self) -> usize {
        feanor_math_hexl::hexl::HEXLNegacyclicNTT::n(self)
    }

    fn new(ring: Zn, log2_rank: usize) -> Self {
        feanor_math_hexl::hexl::HEXLNegacyclicNTT::for_zn(ring, log2_rank).unwrap()
    }

    fn ring(&self) -> RingRef<'_, ZnBase> {
        RingRef::new(feanor_math_hexl::hexl::HEXLNegacyclicNTT::ring(self).get_ring())
    }
}

///
/// An object that supports computing an arbitrary-length NTT, i.e the evaluation
/// of a polynomial at all `m`-th roots of unity, for an arbitrary `m` which usually 
/// is not a power of two.
/// 
pub trait FheanorGeneralNTT<R>: PartialEq
    where R: RingStore
{
    ///
    /// Should assign to `output` the NTT of `input`, i.e. the evaluation
    /// at all `self.len()`-th roots of unity.
    /// 
    /// Concretely, the `i`-th element of `output` should store the evaluation
    /// of `input` (interpreted as a polynomial) at `𝝵^-i`.
    /// Note that the `-` in the exponent is standard convention for the DFT.
    /// 
    /// The implementation may overwrite the values of input with arbitrary (but safe) values.
    /// 
    fn fft_base<const INV: bool>(&self, input: &mut [El<R>], output: &mut [El<R>]);

    fn ring(&self) -> RingRef<'_, R::Type>;

    fn len(&self) -> usize;

    fn new(ring: R, m: usize) -> Self;
}

impl<R_main, R_twiddle> FheanorGeneralNTT<R_main> for BluesteinFFT<R_main::Type, R_twiddle, CanHom<RingValue<R_twiddle>, R_main>>
    where R_main: RingStore + Clone,
        R_twiddle: ZnRing + FromModulusCreateableZnRing + Clone,
        R_main::Type: FiniteRing + CanHomFrom<R_twiddle>
{
    fn fft_base<const INV: bool>(&self, input: &mut [El<R_main>], output: &mut [El<R_main>]) {
        assert_eq!(input.len(), FheanorGeneralNTT::len(self));
        assert_eq!(output.len(), FheanorGeneralNTT::len(self));
        if INV {
            <BluesteinFFT<_, _, _> as FFTAlgorithm<R_main::Type>>::inv_fft(&self, &mut *input, FheanorGeneralNTT::ring(self));
        } else {
            <BluesteinFFT<_, _, _> as FFTAlgorithm<R_main::Type>>::fft(&self, &mut *input, FheanorGeneralNTT::ring(self));
        }
        for i in 0..input.len() {
            output[i] = FheanorGeneralNTT::ring(self).clone_el(&input[i]);
        }
    }

    fn ring(&self) -> RingRef<'_, R_main::Type> {
        unimplemented!()
    }

    fn len(&self) -> usize {
        <BluesteinFFT<_, _, _> as FFTAlgorithm<R_main::Type>>::len(self)
    }

    fn new(ring: R_main, m: usize) -> Self {
        let p = ring.characteristic(BigIntRing::RING).unwrap();
        let twiddle_ring = RingValue::from(R_twiddle::from_modulus(|ZZ| Ok(int_cast(p, RingRef::new(ZZ), BigIntRing::RING))).unwrap_or_else(no_error));
        return BluesteinFFT::for_zn_with_hom(ring.into_can_hom(twiddle_ring).ok().unwrap(), m, Global).unwrap()
    }
}

///
/// Contains a dyn-compatible variant of [`ConvolutionAlgorithm`].
/// This is useful if you want to create a ring but only know the type
/// of the convolution algorithm at runtime.
/// 
pub mod dyn_convolution;

#[cfg(test)]
use std::array::from_fn;
#[cfg(test)]
use feanor_math::assert_el_eq;

#[test]
fn test_negacyclic_ntt() {
    feanor_tracing::DelayedLogger::init_test();
    let Fp = Zn::new(17).as_field().ok().unwrap();
    let zeta = Fp.int_hom().map(3);
    let ntt = RustNegacyclicNTT::new_with_root_of_unity(Fp, zeta, 3);

    let original = from_fn(|i| if i == 1 { Fp.one() } else { Fp.zero() });
    let mut input: [_; 8] = original;
    let mut output: [_; 8] = from_fn(|_| Fp.zero());
    let expected: [_; 8] = from_fn(|i| Fp.pow(zeta, 16 - (bitreverse(i, 3) * 2 + 1)));

    ntt.bitreversed_negacyclic_fft_base::<false>(&mut input, &mut output);

    for i in 0..8 {
        assert_el_eq!(&Fp, &expected[i], &output[i]);
    }
    
    ntt.bitreversed_negacyclic_fft_base::<true>(&mut output, &mut input);

    for i in 0..8 {
        assert_el_eq!(&Fp, &original[i], &input[i]);
    }
}
