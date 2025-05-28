use std::alloc::Global;
use std::cmp::min;

use dense_poly::DensePolyRing;
use feanor_math::algorithms::convolution::*;
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::IntegerRingStore;
use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::*;
use feanor_math::rings::poly::*;
use sparse_poly::SparsePolyRing;
use tracing::instrument;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum SmallCoeff {
    Zero = 0, One = 1, NegOne = -1
}

struct SparsePolyReducer<R>
    where R: RingStore
{
    degree: usize,
    stride: usize,
    coefficients: Vec<SmallCoeff>,
    ring: R
}

impl<R> SparsePolyReducer<R>
    where R: RingStore
{
    #[instrument(skip_all)]
    fn new<P>(poly_ring: P, poly: &El<P>, ring: R, stride: usize) -> Self
        where P: RingStore,
            P::Type: PolyRing,
            <P::Type as RingExtension>::BaseRing: RingStore<Type = R::Type>
    {
        assert!(poly_ring.base_ring().get_ring() == ring.get_ring());
        assert!(stride > 0);
        assert!(!poly_ring.is_zero(poly));
        assert!(poly_ring.base_ring().is_one(poly_ring.lc(poly).unwrap()));
        let coefficients = (0..poly_ring.degree(poly).unwrap()).map(|i| {
            let c = poly_ring.coefficient_at(poly, i);
            if poly_ring.base_ring().is_zero(c) {
                SmallCoeff::Zero
            } else if poly_ring.base_ring().is_one(c) {
                SmallCoeff::NegOne
            } else {
                assert!(poly_ring.base_ring().is_neg_one(c));
                SmallCoeff::One
            }
        }).collect::<Vec<_>>();
        return Self {
            degree: poly_ring.degree(poly).unwrap() * stride,
            stride: stride,
            coefficients: coefficients,
            ring: ring
        };
    }

    #[instrument(skip_all)]
    fn remainder(&self, data: &mut [El<R>]) {
        let mut start_pos_it = (self.degree..data.len()).step_by(self.stride).rev();
        if let Some(i) = start_pos_it.next() {
            let stride = data.len() - i;
            let (base, reduce) = data[(i - self.degree)..].split_at_mut(self.degree);
            for j in 0..self.coefficients.len() {
                match self.coefficients[j] {
                    SmallCoeff::Zero => {},
                    SmallCoeff::One => for k in 0..stride {
                        self.ring.add_assign_ref(&mut base[k + j * self.stride], &reduce[k]);
                    },
                    SmallCoeff::NegOne => for k in 0..stride {
                        self.ring.sub_assign_ref(&mut base[k + j * self.stride], &reduce[k]);
                    }
                }
            }
        }
        for i in start_pos_it {
            let (base, reduce) = data[(i - self.degree)..].split_at_mut(self.degree);
            for j in 0..self.coefficients.len() {
                match self.coefficients[j] {
                    SmallCoeff::Zero => {},
                    SmallCoeff::One => for k in 0..self.stride {
                        self.ring.add_assign_ref(&mut base[k + j * self.stride], &reduce[k]);
                    },
                    SmallCoeff::NegOne => for k in 0..self.stride {
                        self.ring.sub_assign_ref(&mut base[k + j * self.stride], &reduce[k]);
                    }
                }
            }
        }
    }
}

struct BarettPolyReducer<R, C>
    where R: RingStore,
        C: ConvolutionAlgorithm<R::Type>
{
    /// degree of polynomial to reduce
    f_deg: usize,
    /// degree of modulus `q`
    q_deg: usize,
    neg_Xn_over_q: Vec<El<R>>,
    q: Vec<El<R>>,
    ring: R,
    convolution: C
}

impl<R, C> BarettPolyReducer<R, C>
    where R: RingStore,
        C: ConvolutionAlgorithm<R::Type>
{
    #[instrument(skip_all)]
    fn new<P>(poly_ring: P, poly: &El<P>, ring: R, f_deg: usize, convolution: C) -> Self
        where P: RingStore,
            P::Type: PolyRing,
            <P::Type as RingExtension>::BaseRing: RingStore<Type = R::Type>
    {
        assert!(poly_ring.base_ring().get_ring() == ring.get_ring());
        let q_deg = poly_ring.degree(poly).unwrap();
        assert!(f_deg >= q_deg);
        let q = (0..=q_deg).map(|i| ring.clone_el(poly_ring.coefficient_at(poly, i))).collect::<Vec<_>>();
        let Xn_over_q = poly_ring.div_rem_monic(poly_ring.from_terms([(ring.one(), f_deg)]), poly).0;
        assert_eq!(f_deg - q_deg, poly_ring.degree(&Xn_over_q).unwrap());
        let neg_Xn_over_q = (0..=(f_deg - q_deg)).map(|i| ring.negate(ring.clone_el(poly_ring.coefficient_at(&Xn_over_q, i)))).collect::<Vec<_>>();
        return Self {
            f_deg: f_deg,
            q_deg: q_deg,
            neg_Xn_over_q: neg_Xn_over_q,
            q: q,
            ring: ring,
            convolution: convolution
        };
    }

    #[instrument(skip_all)]
    fn remainder(&self, data: &mut [El<R>]) {
        assert!(data.len() >= self.f_deg + 2);
        assert!(self.ring.is_zero(&data[self.f_deg + 1]));
        let mut quotient = Vec::with_capacity_in(2 * (self.f_deg - self.q_deg + 1), Global);
        quotient.resize_with(2 * (self.f_deg - self.q_deg + 1), || self.ring.zero());
        self.convolution.compute_convolution(&data[self.q_deg..=self.f_deg], &self.neg_Xn_over_q, &mut quotient, &self.ring);
        let quotient = &quotient[(self.f_deg - self.q_deg)..(2 * (self.f_deg - self.q_deg) + 1)];
        let quotient_prep = self.convolution.prepare_convolution_operand(&quotient, None, &self.ring);
        let step = 1 << StaticRing::<i64>::RING.abs_log2_ceil(&((self.f_deg - self.q_deg + 1) as i64)).unwrap();
        for i in (0..=self.q_deg).step_by(step) {
            self.convolution.compute_convolution_prepared(
                &self.q[i..min(self.q.len(), i + step)], 
                None,
                &quotient, 
                Some(&quotient_prep),
                &mut data[i..min(self.f_deg + 2, i + 2 * step)], 
                &self.ring
            );
        }
    }
}

///
/// Precomputed data to speed up polynomial division by a fixed cyclotomic polynomial.
/// 
/// Used by [`crate::ciphertext_ring::single_rns_ring::SingleRNSRing`].
/// 
pub struct CyclotomicPolyReducer<R, C>
    where R: RingStore + Clone,
        C: ConvolutionAlgorithm<R::Type>
{
    sparse_reducers: Vec<SparsePolyReducer<R>>,
    final_reducer: Option<BarettPolyReducer<R, C>>
}

impl<R, C> CyclotomicPolyReducer<R, C>
    where R: RingStore + Clone,
        C: ConvolutionAlgorithm<R::Type>
{
    #[instrument(skip_all)]
    pub fn new(ring: R, n: i64, convolution: C) -> Self {
        let factorization = factor(StaticRing::<i64>::RING, n);
        let poly_ring = SparsePolyRing::new(StaticRing::<i32>::RING, "X");
        let ring_poly_ring = DensePolyRing::new(&ring, "X");
        let hom = ring_poly_ring.lifted_hom(&poly_ring, ring.int_hom());

        if factorization.len() == 1 {
            let (p, e) = factorization[0];
            return Self {
                sparse_reducers: vec![SparsePolyReducer::new(&ring_poly_ring, &hom.map(cyclotomic_polynomial(&poly_ring, p as usize)), ring.clone(), StaticRing::<i64>::RING.pow(p, e - 1) as usize)],
                final_reducer: None
            };
        }

        let mut sparse_reducers = Vec::new();
        let mut current_n = 1;
        let mut current_stride = n;
        for i in 0..factorization.len() {
            let cyclotomic_poly = cyclotomic_polynomial(&poly_ring, current_n as usize);
            sparse_reducers.push(SparsePolyReducer::new(&ring_poly_ring, &hom.map(cyclotomic_poly), ring.clone(), current_stride as usize));
            let (p, _e) = factorization[i];
            current_n *= p;
            current_stride /= p;
        }

        let cyclotomic_poly = cyclotomic_polynomial(&poly_ring, n as usize);
        let final_reducer = BarettPolyReducer::new(&ring_poly_ring, &hom.map(cyclotomic_poly), ring.clone(), sparse_reducers.last().unwrap().degree - 1, convolution);

        return Self {
            sparse_reducers: sparse_reducers,
            final_reducer: Some(final_reducer)
        };
    }

    #[instrument(skip_all)]
    pub fn remainder(&self, data: &mut [El<R>]) {
        let mut current_len = data.len();
        for reducer in &self.sparse_reducers {
            reducer.remainder(&mut data[..current_len]);
            current_len = reducer.degree;
        }
        if let Some(final_reducer) = &self.final_reducer {
            data[current_len] = final_reducer.ring.zero();
            final_reducer.remainder(&mut data[..(current_len + 1)]);
        }
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::*;
#[cfg(test)]
use feanor_math::rings::zn::*;
#[cfg(test)]
use feanor_math::algorithms::convolution::ntt::NTTConvolution;

#[test]
fn test_sparse_poly_remainder() {
    let poly_ring = DensePolyRing::new(StaticRing::<i64>::RING, "X");
    let poly = cyclotomic_polynomial(&poly_ring, 5);
    let reducer = SparsePolyReducer::new(&poly_ring, &poly, StaticRing::<i64>::RING, 3);
    let mut data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
    let expected = [4, 5, 6, 10, -9, -9, -6, -6, -6, -3, -3, -3];

    reducer.remainder(&mut data);

    assert_eq!(&expected, &data[..12]);

    let poly_ring = DensePolyRing::new(StaticRing::<i64>::RING, "X");
    let poly = poly_ring.sub(poly_ring.indeterminate(), poly_ring.one());
    let reducer = SparsePolyReducer::new(&poly_ring, &poly, StaticRing::<i64>::RING, 13);
    let mut data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25];
    let expected = [15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 13];

    reducer.remainder(&mut data);

    assert_eq!(&expected, &data[..13]);
}

#[test]
fn test_barett_poly_remainder() {
    let ring = Zn::new(65537).as_field().ok().unwrap();
    let convolution = NTTConvolution::new(ring.clone());
    let poly_ring = DensePolyRing::new(ring.clone(), "X");
    let poly = cyclotomic_polynomial(&poly_ring, 4 * 5 * 7);
    let reducer = BarettPolyReducer::new(&poly_ring, &poly, ring.clone(), 200, convolution);
    let expected = poly_ring.div_rem_monic(poly_ring.from_terms((1..=201).enumerate().map(|(i, x)| (ring.int_hom().map(x), i))), &poly).1;

    let mut actual = (1..=201).chain([0].into_iter()).map(|x| ring.int_hom().map(x)).collect::<Vec<_>>();
    reducer.remainder(&mut actual);

    for i in 0..48 {
        assert_el_eq!(&ring, poly_ring.coefficient_at(&expected, i), &actual[i]);
    }

    let poly = poly_ring.add(cyclotomic_polynomial(&poly_ring, 25), cyclotomic_polynomial(&poly_ring, 23 * 5));
    let convolution = NTTConvolution::new(ring.clone());
    let reducer = BarettPolyReducer::new(&poly_ring, &poly, &ring, 150, convolution);
    let expected = poly_ring.div_rem_monic(poly_ring.from_terms((1..=151).enumerate().map(|(i, x)| (ring.int_hom().map(x), i))), &poly).1;

    let mut actual = (1..=151).chain([0].into_iter()).map(|x| ring.int_hom().map(x)).collect::<Vec<_>>();
    reducer.remainder(&mut actual);

    for i in 0..48 {
        assert_el_eq!(&ring, poly_ring.coefficient_at(&expected, i), &actual[i]);
    }
}

#[test]
fn test_cyclotomic_poly_remainder() {
    let ring = Zn::new(65537).as_field().ok().unwrap();
    let convolution = NTTConvolution::new(ring.clone());
    let poly_ring = DensePolyRing::new(ring.clone(), "X");
    let reducer = CyclotomicPolyReducer::new(ring.clone(), 3, convolution);
    let expected = [ring.zero(), ring.zero()];

    let mut actual = [ring.one(), ring.one(), ring.one()];
    reducer.remainder(&mut actual);

    for i in 0..2 {
        assert_el_eq!(&ring, &expected[i], &actual[i]);
    }

    let convolution = NTTConvolution::new(ring.clone());
    let poly = cyclotomic_polynomial(&poly_ring, 5);
    let reducer = CyclotomicPolyReducer::new(ring.clone(), 5, convolution);
    let expected = poly_ring.div_rem_monic(poly_ring.from_terms((1..6).enumerate().map(|(i, x)| (ring.int_hom().map(x), i))), &poly).1;

    let mut actual = (1..6).map(|x| ring.int_hom().map(x)).collect::<Vec<_>>();
    reducer.remainder(&mut actual);

    for i in 0..4 {
        assert_el_eq!(&ring, poly_ring.coefficient_at(&expected, i), &actual[i]);
    }

    let poly = cyclotomic_polynomial(&poly_ring, 4 * 5 * 7);
    let convolution = NTTConvolution::new(ring.clone());
    let reducer = CyclotomicPolyReducer::new(ring.clone(), 4 * 5 * 7, convolution);
    let expected = poly_ring.div_rem_monic(poly_ring.from_terms((1..200).enumerate().map(|(i, x)| (ring.int_hom().map(x), i))), &poly).1;

    let mut actual = (1..200).map(|x| ring.int_hom().map(x)).collect::<Vec<_>>();
    reducer.remainder(&mut actual);

    for i in 0..48 {
        assert_el_eq!(&ring, poly_ring.coefficient_at(&expected, i), &actual[i]);
    }
}