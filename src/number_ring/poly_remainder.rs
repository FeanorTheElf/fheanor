use std::alloc::Global;

use dense_poly::DensePolyRing;
use feanor_math::algorithms::convolution::*;
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::*;
use feanor_math::rings::poly::*;
use sparse_poly::SparsePolyRing;
use tracing::instrument;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum SmallCoeff {
    One = 1,
    NegOne = -1,
}

#[derive(Clone)]
struct SparsePolyReducer<R>
where
    R: RingStore,
{
    degree: usize,
    stride: usize,
    /// the nonzero coefficients of `-(poly - X^deg(poly))`, as pairs `(index, coefficient)`
    coefficients: Vec<(usize, SmallCoeff)>,
    ring: R,
}

impl<R> SparsePolyReducer<R>
where
    R: RingStore,
{
    #[instrument(skip_all)]
    fn new<P>(poly_ring: P, poly: &El<P>, ring: R, stride: usize) -> Self
    where
        P: RingStore,
        P::Type: PolyRing,
        <P::Type as RingExtension>::BaseRing: RingStore<Type = R::Type>,
    {
        assert!(poly_ring.base_ring().get_ring() == ring.get_ring());
        assert!(stride > 0);
        assert!(!poly_ring.is_zero(poly));
        assert!(poly_ring.base_ring().is_one(poly_ring.lc(poly).unwrap()));
        let coefficients = (0..poly_ring.degree(poly).unwrap())
            .filter_map(|i| {
                let c = poly_ring.coefficient_at(poly, i);
                if poly_ring.base_ring().is_zero(c) {
                    None
                } else if poly_ring.base_ring().is_one(c) {
                    Some((i, SmallCoeff::NegOne))
                } else {
                    assert!(poly_ring.base_ring().is_neg_one(c));
                    Some((i, SmallCoeff::One))
                }
            })
            .collect::<Vec<_>>();
        return Self {
            degree: poly_ring.degree(poly).unwrap() * stride,
            stride,
            coefficients,
            ring,
        };
    }

    #[instrument(skip_all)]
    fn remainder(&self, data: &mut [El<R>]) {
        // we reduce blocks of `stride` coefficients at once; the first (topmost) block
        // might be shorter, if `data.len() - degree` is not divisible by `stride`
        let mut block_len = (data.len().saturating_sub(self.degree)) % self.stride;
        if block_len == 0 {
            block_len = self.stride;
        }
        let mut end = data.len();
        while end > self.degree {
            let i = end - block_len;
            let (base, reduce) = data[(i - self.degree)..end].split_at_mut(self.degree);
            for (j, c) in &self.coefficients {
                let base = &mut base[(j * self.stride)..(j * self.stride + block_len)];
                match c {
                    SmallCoeff::One => {
                        for k in 0..block_len {
                            self.ring.add_assign_ref(&mut base[k], &reduce[k]);
                        }
                    }
                    SmallCoeff::NegOne => {
                        for k in 0..block_len {
                            self.ring.sub_assign_ref(&mut base[k], &reduce[k]);
                        }
                    }
                }
            }
            end = i;
            block_len = self.stride;
        }
    }
}

pub struct BarettPolyReducer<R, C>
where
    R: RingStore,
    C: ConvolutionAlgorithm<R::Type>,
{
    /// degree of polynomial to reduce
    f_deg: usize,
    /// degree of modulus `q`
    q_deg: usize,
    /// `-floor(X^f_deg / q)`, of degree `f_deg - q_deg` (or `0` if `f_deg < q_deg`)
    neg_mu: Vec<El<R>>,
    neg_mu_prep: C::PreparedConvolutionOperand,
    q: Vec<El<R>>,
    q_prep: C::PreparedConvolutionOperand,
    ring: R,
    convolution: C,
}

impl<R, C> BarettPolyReducer<R, C>
where
    R: RingStore,
    C: ConvolutionAlgorithm<R::Type>,
{
    #[instrument(skip_all)]
    pub fn new(poly_ring: DensePolyRing<R>, poly: &El<DensePolyRing<R>>, f_deg: usize, convolution: C) -> Self {
        assert!(poly_ring.base_ring().is_one(poly_ring.lc(poly).unwrap()));
        let q_deg = poly_ring.degree(poly).unwrap();
        let ring = poly_ring.base_ring();

        let quo_deg = f_deg.checked_sub(q_deg);
        let mu_deg = quo_deg.unwrap_or(0);

        let q = (0..(q_deg + 1))
            .map(|i| ring.clone_el(poly_ring.coefficient_at(poly, i)))
            .collect::<Vec<_>>();
        let q_prep = convolution.prepare_convolution_operand(&q, Some(quo_deg.unwrap_or(0) + q_deg + 1), &ring);

        let mu = poly_ring
            .div_rem_monic(poly_ring.from_terms([(ring.one(), f_deg.max(q_deg))]), poly)
            .0;
        assert_eq!(mu_deg, poly_ring.degree(&mu).unwrap());
        let neg_mu = (0..(mu_deg + 1))
            .map(|i| ring.negate(ring.clone_el(poly_ring.coefficient_at(&mu, i))))
            .collect::<Vec<_>>();
        let neg_mu_prep = convolution.prepare_convolution_operand(&neg_mu, Some(2 * mu_deg + 1), &ring);

        return Self {
            f_deg,
            q_deg,
            neg_mu,
            neg_mu_prep,
            q,
            q_prep,
            ring: poly_ring.into().into_base_ring(),
            convolution,
        };
    }

    pub fn base_ring(&self) -> &R { &self.ring }

    pub fn convolution(&self) -> &C { &self.convolution }

    pub fn modulus_deg(&self) -> usize { self.q_deg }

    pub fn modulus_coefficients(&self) -> &[El<R>] { &self.q }

    pub fn modulus<P>(&self, poly_ring: P) -> El<P>
    where
        P: RingStore,
        P::Type: PolyRing,
        <P::Type as RingExtension>::BaseRing: RingStore<Type = R::Type>,
    {
        assert!(self.ring.get_ring() == poly_ring.base_ring().get_ring());
        poly_ring.from_terms(self.q.iter().enumerate().map(|(i, c)| (self.ring.clone_el(c), i)))
    }

    #[instrument(skip_all)]
    pub fn remainder(&self, data: &mut [El<R>]) {
        assert!(data.len() >= self.f_deg + 2);

        let f_deg = self.f_deg;
        let q_deg = self.q_deg;
        if let Some(quo_deg) = f_deg.checked_sub(q_deg) {
            assert!(self.ring.is_zero(&data[self.f_deg + 1]));

            let mut scaled_quotient = Vec::with_capacity_in(2 * quo_deg + 2, Global);
            scaled_quotient.resize_with(2 * quo_deg + 2, || self.ring.zero());
            self.convolution.compute_convolution_prepared(
                &data[q_deg..(f_deg + 1)],
                None,
                &self.neg_mu,
                Some(&self.neg_mu_prep),
                &mut scaled_quotient,
                &self.ring,
            );

            let quotient = &scaled_quotient[quo_deg..(2 * quo_deg + 1)];
            self.convolution.compute_convolution_prepared(
                &quotient,
                None,
                &self.q,
                Some(&self.q_prep),
                data,
                &self.ring,
            );
        }
    }
}

impl<R, C> Clone for BarettPolyReducer<R, C>
where
    R: RingStore + Clone,
    C: ConvolutionAlgorithm<R::Type> + Clone,
{
    fn clone(&self) -> Self {
        let f_deg = self.f_deg;
        let q_deg = self.q_deg;
        let quo_deg = f_deg.checked_sub(q_deg);
        let mu_deg = quo_deg.unwrap_or(0);
        Self {
            convolution: self.convolution.clone(),
            f_deg: self.f_deg,
            neg_mu: self.neg_mu.iter().map(|x| self.ring.clone_el(x)).collect(),
            neg_mu_prep: self.convolution.prepare_convolution_operand(
                &self.neg_mu,
                Some(2 * mu_deg + 1),
                &self.ring,
            ),
            q: self.q.iter().map(|x| self.ring.clone_el(x)).collect(),
            q_deg: self.q_deg,
            q_prep: self.convolution.prepare_convolution_operand(
                &self.q,
                Some(quo_deg.unwrap_or(0) + q_deg + 1),
                &self.ring,
            ),
            ring: self.ring.clone(),
        }
    }
}

/// Precomputed data to speed up polynomial division by a fixed cyclotomic polynomial.
pub struct CyclotomicPolyReducer<R, C = KaratsubaAlgorithm>
where
    R: RingStore + Clone,
    C: ConvolutionAlgorithm<R::Type>,
{
    sparse_reducers: Vec<SparsePolyReducer<R>>,
    final_reducer: BarettPolyReducer<R, C>,
}

impl<R, C> CyclotomicPolyReducer<R, C>
where
    R: RingStore + Clone,
    C: ConvolutionAlgorithm<R::Type>,
{
    #[instrument(skip_all)]
    pub fn new(ring: R, m: u64, convolution: C) -> Self {
        let factorization = factor(StaticRing::<i64>::RING, m as i64);
        let poly_ring = SparsePolyRing::new(StaticRing::<i32>::RING, "X");
        let ring_poly_ring = DensePolyRing::new(ring.clone(), "X");
        let hom = ring_poly_ring.lifted_hom(&poly_ring, ring.int_hom());

        if factorization.len() == 1 {
            let (p, e) = factorization[0];
            let trivial_poly = ring_poly_ring.indeterminate();
            return Self {
                sparse_reducers: vec![SparsePolyReducer::new(
                    &ring_poly_ring,
                    &hom.map(cyclotomic_polynomial(&poly_ring, p as usize)),
                    ring.clone(),
                    StaticRing::<i64>::RING.pow(p, e - 1) as usize,
                )],
                final_reducer: BarettPolyReducer::new(ring_poly_ring, &trivial_poly, 0, convolution),
            };
        }

        // `SparsePolyReducer` only supports coefficients in `{-1, 0, 1}`, which is not
        // the case for all cyclotomic polynomials (e.g. `Phi_105` has a coefficient `-2`)
        let is_flat = |poly: &El<SparsePolyRing<StaticRing<i32>>>| poly_ring.terms(poly).all(|(c, _)| c.abs() <= 1);

        // we reduce modulo `Phi_n(X^(m / n))` for `n = 1, p1, p1 p2, ...`, which are all
        // multiples of `Phi_m`, and very sparse as long as `n` has few prime factors
        let mut sparse_reducers = Vec::new();
        let mut current_n = 1;
        let mut current_stride = m as usize;
        let mut all_flat = true;
        for i in 0..factorization.len() {
            let cyclotomic_poly = cyclotomic_polynomial(&poly_ring, current_n);
            if !is_flat(&cyclotomic_poly) {
                all_flat = false;
                break;
            }
            sparse_reducers.push(SparsePolyReducer::new(
                &ring_poly_ring,
                &hom.map(cyclotomic_poly),
                ring.clone(),
                current_stride,
            ));
            let (p, _e) = factorization[i];
            current_n *= p as usize;
            current_stride /= p as usize;
        }

        let cyclotomic_poly = cyclotomic_polynomial(&poly_ring, m as usize);
        if all_flat && is_flat(&cyclotomic_poly) {
            sparse_reducers.push(SparsePolyReducer::new(
                &ring_poly_ring,
                &hom.map(cyclotomic_poly),
                ring.clone(),
                1,
            ));
            let trivial_poly = ring_poly_ring.indeterminate();
            return Self {
                sparse_reducers,
                final_reducer: BarettPolyReducer::new(ring_poly_ring, &trivial_poly, 0, convolution),
            };
        }

        let cyclotomic_poly = hom.map(cyclotomic_poly);
        let final_reducer = BarettPolyReducer::new(
            ring_poly_ring,
            &cyclotomic_poly,
            sparse_reducers.last().unwrap().degree - 1,
            convolution,
        );

        return Self {
            sparse_reducers,
            final_reducer,
        };
    }

    #[instrument(skip_all)]
    pub fn remainder(&self, data: &mut [El<R>]) {
        let mut current_len = data.len();
        for reducer in &self.sparse_reducers {
            if reducer.degree < data.len() {
                reducer.remainder(&mut data[..current_len]);
                current_len = reducer.degree;
            }
        }
        data[current_len] = self.final_reducer.ring.zero();
        self.final_reducer.remainder(&mut data[..(current_len + 1)]);
    }

    pub fn base_ring(&self) -> &R { self.final_reducer.base_ring() }

    pub fn convolution(&self) -> &C { self.final_reducer.convolution() }
}

impl<R, C> Clone for CyclotomicPolyReducer<R, C>
where
    R: RingStore + Clone,
    C: ConvolutionAlgorithm<R::Type> + Clone,
{
    fn clone(&self) -> Self {
        Self {
            sparse_reducers: self.sparse_reducers.clone(),
            final_reducer: self.final_reducer.clone(),
        }
    }
}

#[cfg(test)]
mod test {
    use feanor_math::algorithms::convolution::ntt::NTTConvolution;
    use feanor_math::assert_el_eq;
    use feanor_math::rings::zn::zn_64::*;
    use feanor_math::rings::zn::*;

    use super::*;

    #[test]
    fn test_sparse_poly_remainder() {
        feanor_tracing::DelayedLogger::init_test();
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
        let mut data = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        ];
        let expected = [15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 13];

        reducer.remainder(&mut data);

        assert_eq!(&expected, &data[..13]);
    }

    #[test]
    fn test_barett_poly_remainder() {
        feanor_tracing::DelayedLogger::init_test();
        let ring = Zn::new(65537).as_field().ok().unwrap();
        let convolution = NTTConvolution::new(ring.clone());
        let poly_ring = DensePolyRing::new(ring.clone(), "X");
        let poly = cyclotomic_polynomial(&poly_ring, 4 * 5 * 7);
        let reducer = BarettPolyReducer::new(poly_ring.clone(), &poly, 200, convolution);
        let expected = poly_ring
            .div_rem_monic(
                poly_ring.from_terms((1..=201).enumerate().map(|(i, x)| (ring.int_hom().map(x), i))),
                &poly,
            )
            .1;

        let mut actual = (1..=201)
            .chain([0].into_iter())
            .map(|x| ring.int_hom().map(x))
            .collect::<Vec<_>>();
        reducer.remainder(&mut actual);

        for i in 0..48 {
            assert_el_eq!(&ring, poly_ring.coefficient_at(&expected, i), &actual[i]);
        }

        let poly = poly_ring.add(
            cyclotomic_polynomial(&poly_ring, 25),
            cyclotomic_polynomial(&poly_ring, 23 * 5),
        );
        let convolution = NTTConvolution::new(ring.clone());
        let reducer = BarettPolyReducer::new(poly_ring.clone(), &poly, 150, convolution);
        let expected = poly_ring
            .div_rem_monic(
                poly_ring.from_terms((1..=151).enumerate().map(|(i, x)| (ring.int_hom().map(x), i))),
                &poly,
            )
            .1;

        let mut actual = (1..=151)
            .chain([0].into_iter())
            .map(|x| ring.int_hom().map(x))
            .collect::<Vec<_>>();
        reducer.remainder(&mut actual);

        for i in 0..48 {
            assert_el_eq!(&ring, poly_ring.coefficient_at(&expected, i), &actual[i]);
        }
    }

    #[test]
    fn test_cyclotomic_poly_remainder() {
        feanor_tracing::DelayedLogger::init_test();
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
        let expected = poly_ring
            .div_rem_monic(
                poly_ring.from_terms((1..6).enumerate().map(|(i, x)| (ring.int_hom().map(x), i))),
                &poly,
            )
            .1;

        let mut actual = (1..6).map(|x| ring.int_hom().map(x)).collect::<Vec<_>>();
        reducer.remainder(&mut actual);

        for i in 0..4 {
            assert_el_eq!(&ring, poly_ring.coefficient_at(&expected, i), &actual[i]);
        }

        let poly = cyclotomic_polynomial(&poly_ring, 4 * 5 * 7);
        let convolution = NTTConvolution::new(ring.clone());
        let reducer = CyclotomicPolyReducer::new(ring.clone(), 4 * 5 * 7, convolution);
        let expected = poly_ring
            .div_rem_monic(
                poly_ring.from_terms((1..200).enumerate().map(|(i, x)| (ring.int_hom().map(x), i))),
                &poly,
            )
            .1;

        let mut actual = (1..200).map(|x| ring.int_hom().map(x)).collect::<Vec<_>>();
        reducer.remainder(&mut actual);

        for i in 0..48 {
            assert_el_eq!(&ring, poly_ring.coefficient_at(&expected, i), &actual[i]);
        }
    }
}
