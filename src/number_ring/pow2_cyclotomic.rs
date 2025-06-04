use std::alloc::Allocator;
use std::alloc::Global;
use std::marker::PhantomData;

use tracing::instrument;

use feanor_math::algorithms::fft::cooley_tuckey::bitreverse;
use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::*;
use feanor_math::homomorphism::*;
use feanor_math::integer::*;
use feanor_math::rings::poly::*;
use feanor_math::rings::zn::zn_64;
use feanor_math::seq::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::Zn;

use crate::cyclotomic::*;
use crate::ntt::HERingNegacyclicNTT;
use crate::DefaultNegacyclicNTT;
use crate::ZZi64;

use super::{HECyclotomicNumberRing, HECyclotomicNumberRingMod, HENumberRing, HENumberRingMod};

pub struct Pow2CyclotomicNumberRing<N = DefaultNegacyclicNTT> {
    log2_m: usize,
    ntt: PhantomData<N>
}

impl Pow2CyclotomicNumberRing {

    pub fn new(m: usize) -> Self {
        Self::new_with(m)
    }
}

impl<N> Pow2CyclotomicNumberRing<N> {

    pub fn new_with(m: usize) -> Self {
        assert!(m > 2);
        let log2_m = StaticRing::<i64>::RING.abs_log2_floor(&(m as i64)).unwrap();
        assert_eq!(m, 1 << log2_m);
        Self {
            log2_m: log2_m,
            ntt: PhantomData
        }
    }
}

impl<N> Clone for Pow2CyclotomicNumberRing<N> {
    fn clone(&self) -> Self {
        Self::new_with(1 << self.log2_m)
    }
}

impl<N> PartialEq for Pow2CyclotomicNumberRing<N> {

    fn eq(&self, other: &Self) -> bool {
        self.log2_m == other.log2_m
    }
}

impl<N> HENumberRing for Pow2CyclotomicNumberRing<N>
    where N: Send + Sync + HERingNegacyclicNTT<zn_64::Zn>
{
    type Decomposed = Pow2CyclotomicDecomposedNumberRing<N, Global>;

    fn product_expansion_factor(&self) -> f64 {
        (1 << (self.log2_m - 1)) as f64
    }

    fn can_to_inf_norm_expansion_factor(&self) -> f64 {
        1. / ((1 << (self.log2_m - 1)) as f64).sqrt()
    }

    fn inf_to_can_norm_expansion_factor(&self) -> f64 {
        // the l2-norm of the coefficients of `x` is at most `sqrt(m) |x|_inf`, and
        // in the power-of-two case, the canonical embedding is a scaled isometry by `sqrt(m)`
        (1 << (self.log2_m - 1)) as f64
    }

    fn mod_p(&self, Fp: zn_64::Zn) -> Self::Decomposed {
        return Pow2CyclotomicDecomposedNumberRing {
            ntt: N::new(Fp, self.log2_m - 1),
            allocator: Global
        };
    }

    fn mod_p_required_root_of_unity(&self) -> usize {
        return 1 << self.log2_m;
    }
    
    fn generating_poly<P>(&self, poly_ring: P) -> El<P>
        where P: RingStore,
            P::Type: PolyRing,
            <<P::Type as RingExtension>::BaseRing as RingStore>::Type: IntegerRing
    {
        poly_ring.add(poly_ring.pow(poly_ring.indeterminate(), 1 << (self.log2_m - 1)), poly_ring.one())
    }

    fn rank(&self) -> usize {
        1 << (self.log2_m - 1)
    }
}

impl<N> HECyclotomicNumberRing for Pow2CyclotomicNumberRing<N>
    where N: Send + Sync + HERingNegacyclicNTT<zn_64::Zn>
{
    fn m(&self) -> usize {
        1 << self.log2_m
    }
}

pub struct Pow2CyclotomicDecomposedNumberRing<N, A> 
    where N: HERingNegacyclicNTT<zn_64::Zn>,
        A: Allocator
{
    ntt: N,
    allocator: A
}

impl<N, A> HECyclotomicNumberRingMod for Pow2CyclotomicDecomposedNumberRing<N, A> 
    where N: Send + Sync + HERingNegacyclicNTT<zn_64::Zn>,
        A: Send + Sync + Allocator
{
    fn m(&self) -> usize {
        2 * self.ntt.len()
    }

    fn permute_galois_action<V1, V2>(&self, src: V1, mut dst: V2, galois_element: CyclotomicGaloisGroupEl)
        where V1: VectorView<zn_64::ZnEl>,
            V2: SwappableVectorViewMut<zn_64::ZnEl>
    {
        assert_eq!(self.rank(), src.len());
        assert_eq!(self.rank(), dst.len());

        let galois_group = self.galois_group();
        let galois_group_ring = galois_group.underlying_ring();
        let galois_element = galois_group.to_ring_el(galois_element);
        let bitlength = StaticRing::<i64>::RING.abs_log2_ceil(&(self.rank() as i64)).unwrap();
        debug_assert_eq!(1 << bitlength, self.rank());
        let hom = galois_group_ring.can_hom(&ZZi64).unwrap();

        // the elements of src resp. dst follow an order derived from the bitreversing order of the underlying FFT
        let index_to_galois_el = |i: usize| hom.map(2 * bitreverse(i, bitlength) as i64 + 1);
        let galois_el_to_index = |s: El<Zn>| bitreverse((galois_group_ring.smallest_positive_lift(s) as usize - 1) / 2, bitlength);

        for i in 0..self.rank() {
            *dst.at_mut(i) = *src.at(galois_el_to_index(galois_group_ring.mul(galois_element, index_to_galois_el(i))));
        }
    }
}

impl<N, A> PartialEq for Pow2CyclotomicDecomposedNumberRing<N, A> 
    where N: HERingNegacyclicNTT<zn_64::Zn>,
        A: Allocator
{
    fn eq(&self, other: &Self) -> bool {
        self.ntt == other.ntt
    }
}

impl<N, A> HENumberRingMod for Pow2CyclotomicDecomposedNumberRing<N, A> 
    where N: Send + Sync + HERingNegacyclicNTT<zn_64::Zn>,
        A: Send + Sync + Allocator
{
    #[instrument(skip_all)]
    fn mult_basis_to_small_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<zn_64::ZnEl>
    {
        let mut input = Vec::with_capacity_in(data.len(), &self.allocator);
        let mut output = Vec::with_capacity_in(data.len(), &self.allocator);
        for x in data.as_iter() {
            input.push(self.ntt.ring().clone_el(x));
        }
        output.resize_with(data.len(), || self.ntt.ring().zero());
        self.ntt.bitreversed_negacyclic_fft_base::<true>(&mut input[..], &mut output[..]);
        for (i, x) in output.into_iter().enumerate() {
            *data.at_mut(i) = x;
        }
    }

    #[instrument(skip_all)]
    fn small_basis_to_mult_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<zn_64::ZnEl>
    {
        let mut input = Vec::with_capacity_in(data.len(), &self.allocator);
        let mut output = Vec::with_capacity_in(data.len(), &self.allocator);
        for x in data.as_iter() {
            input.push(self.ntt.ring().clone_el(x));
        }
        output.resize_with(data.len(), || self.ntt.ring().zero());
        self.ntt.bitreversed_negacyclic_fft_base::<false>(&mut input[..], &mut output[..]);
        for (i, x) in output.into_iter().enumerate() {
            *data.at_mut(i) = x;
        }
    }

    fn coeff_basis_to_small_basis<V>(&self, _data: V) {}

    fn small_basis_to_coeff_basis<V>(&self, _data: V) {}

    fn rank(&self) -> usize {
        self.ntt.len()
    }

    fn base_ring(&self) -> &zn_64::Zn {
        self.ntt.ring()
    }
}

#[cfg(test)]
use crate::ciphertext_ring::double_rns_ring;
#[cfg(test)]
use crate::ciphertext_ring::single_rns_ring;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::number_ring::quotient;
#[cfg(test)]
use feanor_math::rings::zn::zn_rns;
#[cfg(test)]
use feanor_math::rings::extension::FreeAlgebraStore;

#[test]
fn test_pow2_cyclotomic_double_rns_ring() {
    double_rns_ring::test_with_number_ring(Pow2CyclotomicNumberRing::new(8));
    double_rns_ring::test_with_number_ring(Pow2CyclotomicNumberRing::new(16));
}

#[test]
fn test_pow2_cyclotomic_single_rns_ring() {
    single_rns_ring::test_with_number_ring(Pow2CyclotomicNumberRing::new(8));
    single_rns_ring::test_with_number_ring(Pow2CyclotomicNumberRing::new(16));
}

#[test]
fn test_pow2_cyclotomic_decomposition_ring() {
    quotient::test_with_number_ring(Pow2CyclotomicNumberRing::new(8));
    quotient::test_with_number_ring(Pow2CyclotomicNumberRing::new(16));
}

#[test]
fn test_permute_galois_automorphism() {
    let rns_base = zn_rns::Zn::new(vec![Zn::new(17), Zn::new(97)], BigIntRing::RING);
    let R = double_rns_ring::DoubleRNSRingBase::new_with(Pow2CyclotomicNumberRing::new(16), rns_base, Global);
    assert_el_eq!(R, R.pow(R.canonical_gen(), 3), R.get_ring().apply_galois_action(&R.canonical_gen(), R.get_ring().galois_group().from_representative(3)));
    assert_el_eq!(R, R.pow(R.canonical_gen(), 6), R.get_ring().apply_galois_action(&R.pow(R.canonical_gen(), 2), R.get_ring().galois_group().from_representative(3)));
}

#[bench]
fn bench_permute_galois_action(bencher: &mut test::Bencher) {
    let number_ring = Pow2CyclotomicNumberRing::new(1 << 15);
    let Fp = Zn::new(65537);
    let number_ring_mod_p = number_ring.mod_p(Fp);
    let input = (0..(1 << 14)).map(|i| Fp.int_hom().map(i)).collect::<Vec<_>>();
    let mut output = (0..(1 << 14)).map(|_| Fp.zero()).collect::<Vec<_>>();
    bencher.iter(|| {
        number_ring_mod_p.permute_galois_action(std::hint::black_box(&input), &mut output, number_ring.galois_group().from_representative(5));
        assert_el_eq!(&Fp, &input[1 << 12], &output[0]);
        assert_el_eq!(&Fp, &input[(1 << 13) + (1 << 12) + (1 << 11)], &output[1 << 13]);
    });
}