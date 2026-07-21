use std::alloc::Allocator;
use std::alloc::Global;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::marker::PhantomData;

use feanor_math::algorithms::fft::cooley_tuckey::bitreverse;
use tracing::instrument;

use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::*;
use feanor_math::integer::*;
use feanor_math::rings::poly::*;
use feanor_math::rings::zn::zn_64;
use feanor_math::seq::*;

use crate::FheanorAllocator;
use crate::ntt::FheanorNegacyclicNTT;
use crate::number_ring::galois::*;
use crate::number_ring::*;
use crate::DefaultNegacyclicNTT;

pub struct Pow2CyclotomicNumberRing<N = DefaultNegacyclicNTT> {
    log2_m: usize,
    galois_group: CyclotomicGaloisGroup,
    ntt: PhantomData<N>
}

impl Pow2CyclotomicNumberRing {

    pub fn new(m: u64) -> Self {
        Self::new_with_ntt(m)
    }
}

impl<N> Pow2CyclotomicNumberRing<N>
    where N: FheanorNegacyclicNTT<zn_64::Zn>
{
    pub fn new_with_ntt(m: u64) -> Self {
        assert!(m > 2);
        let log2_m = StaticRing::<i64>::RING.abs_log2_floor(&(m as i64)).unwrap();
        assert_eq!(m, 1 << log2_m);
        Self {
            log2_m: log2_m,
            galois_group: CyclotomicGaloisGroupBase::new(m as u64),
            ntt: PhantomData
        }
    }

    pub fn m(&self) -> u64 {
        self.galois_group.m()
    }
}

impl<N> Debug for Pow2CyclotomicNumberRing<N>
    where N: FheanorNegacyclicNTT<zn_64::Zn>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Z[𝝵_{}]", self.m())
    }
}

impl<N> Clone for Pow2CyclotomicNumberRing<N>
    where N: FheanorNegacyclicNTT<zn_64::Zn>
{    
    fn clone(&self) -> Self {
        Self::new_with_ntt(1 << self.log2_m)
    }
}

impl<N> PartialEq for Pow2CyclotomicNumberRing<N> {

    fn eq(&self, other: &Self) -> bool {
        self.log2_m == other.log2_m
    }
}

impl<N> NumberRingDescriptor for Pow2CyclotomicNumberRing<N>
    where N: FheanorNegacyclicNTT<zn_64::Zn>
{
    type NumberRingQuotientBases = Pow2CyclotomicNumberRingQuotientBases<N, Global>;

    fn small_basis_product_expansion_factor(&self) -> f64 {
        self.rank() as f64
    }

    fn coeff_basis_product_expansion_factor(&self) -> f64 {
        self.small_basis_product_expansion_factor()
    }

    fn galois_group(&self) -> &CyclotomicGaloisGroup {
        &self.galois_group
    }

    fn bases_mod_p(&self, Fp: zn_64::Zn) -> Self::NumberRingQuotientBases {
        return Pow2CyclotomicNumberRingQuotientBases {
            ntt: N::new(Fp, self.log2_m - 1),
            galois_group: self.galois_group.clone(),
            allocator: Global,
            log2_m: self.log2_m
        };
    }

    fn mod_p_required_root_of_unity(&self) -> u64 {
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

pub struct Pow2CyclotomicNumberRingQuotientBases<N, A> 
    where N: FheanorNegacyclicNTT<zn_64::Zn>,
        A: FheanorAllocator
{
    log2_m: usize,
    ntt: N,
    galois_group: CyclotomicGaloisGroup,
    allocator: A
}

impl<N, A> PartialEq for Pow2CyclotomicNumberRingQuotientBases<N, A> 
    where N: FheanorNegacyclicNTT<zn_64::Zn>,
        A: FheanorAllocator
{
    fn eq(&self, other: &Self) -> bool {
        self.ntt == other.ntt
    }
}

impl<N, A> NumberRingQuotientBases for Pow2CyclotomicNumberRingQuotientBases<N, A> 
    where N: FheanorNegacyclicNTT<zn_64::Zn>,
        A: FheanorAllocator
{
    fn galois_group(&self) -> &CyclotomicGaloisGroup {
        &self.galois_group
    }

    #[instrument(skip_all)]
    fn permute_galois_action<V1, V2>(&self, src: V1, mut dst: V2, galois_element: &GaloisGroupEl)
        where V1: VectorView<zn_64::ZnEl>,
            V2: SwappableVectorViewMut<zn_64::ZnEl>
    {
        assert_eq!(self.rank(), src.len());
        assert_eq!(self.rank(), dst.len());

        let galois_el_repr = self.galois_group().representative(galois_element) as usize;

        // the elements of src resp. dst follow an order derived from the bitreversing order of the underlying FFT
        let index_to_galois_el = |i: usize| 2 * bitreverse(i, self.log2_m - 1) + 1;
        let galois_el_to_index = |s: usize| bitreverse((s - 1) / 2, self.log2_m - 1);

        for i in 0..self.rank() {
            // explicitly perform the reduction here, as we know that the modulus is a power of two,
            // which makes the reduction cheaper than done by the implementation of Zn
            *dst.at_mut(i) = *src.at(galois_el_to_index((galois_el_repr * index_to_galois_el(i)) % (1 << self.log2_m)));
        }
    }

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
        RingValue::from_ref(self.ntt.ring().into())
    }
}

#[cfg(test)]
use crate::ciphertext_ring::double_rns_ring;
#[cfg(test)]
use crate::ciphertext_ring::single_rns_ring;
#[cfg(test)]
use crate::number_ring::quotient_by_int;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::extension::FreeAlgebraStore;
#[cfg(test)]
use feanor_math::rings::zn::*;
#[cfg(test)]
use feanor_math::homomorphism::*;

#[test]
fn test_pow2_cyclotomic_double_rns_ring() {
    feanor_tracing::DelayedLogger::init_test();
    double_rns_ring::test_with_number_ring(Pow2CyclotomicNumberRing::<DefaultNegacyclicNTT>::new(8));
    double_rns_ring::test_with_number_ring(Pow2CyclotomicNumberRing::<DefaultNegacyclicNTT>::new(16));
}

#[test]
fn test_pow2_cyclotomic_single_rns_ring() {
    feanor_tracing::DelayedLogger::init_test();
    single_rns_ring::test_with_number_ring(Pow2CyclotomicNumberRing::<DefaultNegacyclicNTT>::new(8));
    single_rns_ring::test_with_number_ring(Pow2CyclotomicNumberRing::<DefaultNegacyclicNTT>::new(16));
}

#[test]
fn test_pow2_cyclotomic_number_ring_quotient() {
    feanor_tracing::DelayedLogger::init_test();
    quotient_by_int::test_with_number_ring(Pow2CyclotomicNumberRing::<DefaultNegacyclicNTT>::new(8));
    quotient_by_int::test_with_number_ring(Pow2CyclotomicNumberRing::<DefaultNegacyclicNTT>::new(16));
}

#[test]
fn test_permute_galois_automorphism() {
    feanor_tracing::DelayedLogger::init_test();
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(16);
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let R = double_rns_ring::DoubleRNSRingBase::new_with_alloc(number_ring, rns_base, Global);
    assert_el_eq!(R, R.pow(R.canonical_gen(), 3), R.get_ring().apply_galois_action(&R.canonical_gen(), &R.acting_galois_group().from_representative(3)));
    assert_el_eq!(R, R.pow(R.canonical_gen(), 6), R.get_ring().apply_galois_action(&R.pow(R.canonical_gen(), 2), &R.acting_galois_group().from_representative(3)));
}

#[bench]
fn bench_permute_galois_action(bencher: &mut test::Bencher) {
    feanor_tracing::DelayedLogger::init_test();
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(1 << 15);
    let Fp = zn_64::Zn::new(65537);
    let number_ring_mod_p = number_ring.bases_mod_p(Fp);
    let input = (0..(1 << 14)).map(|i| Fp.int_hom().map(i)).collect::<Vec<_>>();
    let mut output = (0..(1 << 14)).map(|_| Fp.zero()).collect::<Vec<_>>();
    bencher.iter(|| {
        number_ring_mod_p.permute_galois_action(std::hint::black_box(&input), &mut output, &number_ring.galois_group().from_representative(5));
        assert_el_eq!(&Fp, &input[1 << 12], &output[0]);
        assert_el_eq!(&Fp, &input[(1 << 13) + (1 << 12) + (1 << 11)], &output[1 << 13]);
    });
}