use std::alloc::{Allocator, Global};
use std::ptr::Alignment;
use std::sync::Arc;

use feanor_math::algorithms::fft::bluestein::BluesteinFFT;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::algorithms::unity_root::{get_prim_root_of_unity, get_prim_root_of_unity_pow2};
use feanor_math::algorithms::fft::*;
use feanor_math::integer::*;
use feanor_math::rings::poly::*;
use feanor_math::divisibility::*;
use feanor_math::primitive_int::*;
use feanor_math::ring::*;
use feanor_math::homomorphism::*;
use feanor_math::rings::poly::sparse_poly::SparsePolyRing;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::rings::zn::*;
use feanor_mempool::dynsize::DynLayoutMempool;
use feanor_mempool::AllocArc;
use feanor_math::seq::*;

use crate::euler_phi_squarefree;
use crate::cyclotomic::*;
use super::{HECyclotomicNumberRing, HECyclotomicNumberRingMod, HENumberRing, HENumberRingMod};

///
/// Represents `Z[𝝵_m]` for a squarefree `m`.
/// 
pub struct OddSquarefreeCyclotomicNumberRing {
    m_factorization_squarefree: Vec<i64>,
}

impl OddSquarefreeCyclotomicNumberRing {

    pub fn new(m: usize) -> Self {
        assert!(m > 1);
        let factorization = factor(StaticRing::<i64>::RING, m as i64);
        // while most of the arithmetic still works with non-squarefree m, our statements about the geometry
        // of the number ring as lattice don't hold anymore (currently this refers to the `norm1_to_norm2_expansion_factor`
        // functions)
        for (_, e) in &factorization {
            assert!(*e == 1, "m = {} is not squarefree", m);
        }
        Self {
            m_factorization_squarefree: factorization.iter().map(|(p, _)| *p).collect(),
        }
    }

    ///
    /// Returns a bound on
    /// ```text
    ///   sup_(x in R \ {0}) | x |_can / | x |'_inf
    /// ```
    /// where `| . |'_inf` is similar to `| . |_inf`, but takes the inf-norm w.r.t.
    /// the powerful basis representation. The powerful basis is given by the monomials
    /// `X^(m i1 / p1 + ... + m ir / pr)` for `0 <= ik < phi(pk) = pk - 1`, and `m = p1 ... pr` is
    /// squarefree with prime factors `p1, ..., pr`.
    /// 
    /// To compare, the standard inf norm `| . |_inf` is the inf-norm w.r.t. the
    /// coefficient basis representation, which is just given by the monomials `X^i`
    /// for `0 <= i < phi(m)`. It has the disadvantage that it is not compatible with
    /// the tensor-product factorization
    /// ```text
    ///   Q[X]/(Phi_m) = Q[X]/(Phi_p1) ⊗ ... ⊗ Q[X]/(Phi_pr)
    /// ```
    /// 
    pub fn powful_inf_to_can_norm_expansion_factor(&self) -> f64 {
        let rank = euler_phi_squarefree(&self.m_factorization_squarefree);
        // a simple estimate; it holds, as for any `x` with `|x|_inf <= b`, the coefficients
        // under the canonical embedding are clearly `<= nb` in absolute value, thus the canonical
        // norm is at most `m sqrt(m)`
        (rank as f64).powi(3).sqrt()
    }

    ///
    /// Returns a bound on
    /// ```text
    ///   sup_(x in R \ {0}) | x |'_inf / | x |_can
    /// ```
    /// For the distinction of standard inf-norm and powerful inf-norm, see
    /// the doc of [`OddSquarefreeCyclotomicNumberRing::powful_inf_to_can_norm_expansion_factor()`].
    /// 
    pub fn can_to_powful_inf_norm_expansion_factor(&self) -> f64 {
        // if `m = p` is a prime, we can give an explicit inverse to the matrix
        // `A = ( zeta^(ij) )` where `i in (Z/pZ)*` and `j in { 0, ..., p - 2 }` by
        // `A^-1 = ( zeta^(ij) - zeta^j ) / p` with `i in { 0, ..., p - 2 }` and `j in (Z/pZ)*`.
        // This clearly shows that in this case, then expansion factor is at most 
        // `(p - 1) | zeta^(ij) - zeta^j | / p < 2`. By the tensor product compatibility of
        // the powerful inf-norm, we thus get this bound
        2f64.powi(self.m_factorization_squarefree.len() as i32)
    }

    ///
    /// Returns a bound on
    /// ```text
    ///   sup_(x in R \ {0}) | x |_inf / | x |'_inf
    /// ```
    /// For the distinction of standard inf-norm and powerful inf-norm, see
    /// the doc of [`OddSquarefreeCyclotomicNumberRing::powful_inf_to_can_norm_expansion_factor()`].
    /// 
    pub fn powful_inf_to_inf_norm_expansion_factor(&self) -> f64 {
        // TODO: Fix
        // conjecture: this is `<= m`; I have no proof currently, but note the following:
        // If the powerful-basis indices `m_1 i_1 / p_1 + ... + m_r i_r / p_r` were distributed
        // at random, about `m / phi(m)` of them would have to be "reduced", i.e. fall
        // into `{ phi(m), ..., m - 1 }` modulo `m`. Each of them contributes to the inf-operator
        // norm, up to the maximal coefficient of `Phi_m`. This maximal coefficient seems
        // to behave as `m^(1/r)`, and `m / phi(m) ~ m^((r - 1)/r)`
        let rank = euler_phi_squarefree(&self.m_factorization_squarefree);
        return rank as f64;
    }
}

impl Clone for OddSquarefreeCyclotomicNumberRing {
    fn clone(&self) -> Self {
        Self {
            m_factorization_squarefree: self.m_factorization_squarefree.clone()
        }
    }
}

impl PartialEq for OddSquarefreeCyclotomicNumberRing {

    fn eq(&self, other: &Self) -> bool {
        self.m_factorization_squarefree == other.m_factorization_squarefree
    }
}

impl HENumberRing for OddSquarefreeCyclotomicNumberRing {

    type Decomposed = OddSquarefreeCyclotomicDecomposedNumberRing<BluesteinFFT<ZnBase, ZnFastmulBase, CanHom<ZnFastmul, Zn>, AllocArc<DynLayoutMempool<Global>>>, AllocArc<DynLayoutMempool<Global>>>;

    fn can_to_inf_norm_expansion_factor(&self) -> f64 {
        self.powful_inf_to_inf_norm_expansion_factor() * self.can_to_powful_inf_norm_expansion_factor()
    }

    fn inf_to_can_norm_expansion_factor(&self) -> f64 {
        let rank = euler_phi_squarefree(&self.m_factorization_squarefree);
        // a simple estimate; it holds, as for any `x` with `|x|_inf <= b`, the coefficients
        // under the canonical embedding are clearly `<= nb` in absolute value, thus the canonical
        // norm is at most `m sqrt(m)`
        (rank as f64).powi(3).sqrt()
    }

    fn mod_p(&self, Fp: Zn) -> Self::Decomposed {
        let n_factorization = &self.m_factorization_squarefree;
        let m = n_factorization.iter().copied().product::<i64>();

        let allocator = AllocArc(Arc::new(DynLayoutMempool::new(Alignment::of::<u64>())));
        let Fp_as_field = (&Fp).as_field().ok().unwrap();
        let Fp_fastmul = ZnFastmul::new(Fp).unwrap();
        let zeta = get_prim_root_of_unity(&Fp_as_field, 2 * m as usize).unwrap();
        let zeta = Fp_as_field.get_ring().unwrap_element(zeta);

        let log2_help_len = StaticRing::<i64>::RING.abs_log2_ceil(&(2 * m).try_into().unwrap()).unwrap();
        let zeta_help_len = get_prim_root_of_unity_pow2(&Fp_as_field, log2_help_len).unwrap();
        let zeta_help_len = Fp_as_field.get_ring().unwrap_element(zeta_help_len);
        
        let fft_table = BluesteinFFT::new_with_hom(
            Fp.into_can_hom(Fp_fastmul).ok().unwrap(),
            Fp_fastmul.coerce(&Fp, zeta),
            Fp_fastmul.coerce(&Fp, zeta_help_len),
            m.try_into().unwrap(),
            log2_help_len,
            allocator
        );

        return OddSquarefreeCyclotomicDecomposedNumberRing::create_squarefree(
            fft_table, 
            Fp, 
            &self.m_factorization_squarefree, 
            AllocArc(Arc::new(DynLayoutMempool::new(Alignment::of::<u64>())))
        );
    }

    fn mod_p_required_root_of_unity(&self) -> usize {
        let m = <_ as HECyclotomicNumberRing>::m(self);
        return m << StaticRing::<i64>::RING.abs_log2_ceil(&(2 * m).try_into().unwrap()).unwrap();
    }

    fn generating_poly<P>(&self, poly_ring: P) -> El<P>
        where P: RingStore,
            P::Type: PolyRing + DivisibilityRing,
            <<P::Type as RingExtension>::BaseRing as RingStore>::Type: IntegerRing
    {
        cyclotomic_polynomial(&poly_ring, <_ as HECyclotomicNumberRing>::m(self) as usize)
    }

    fn rank(&self) -> usize {
        euler_phi_squarefree(&self.m_factorization_squarefree) as usize
    }
}

impl HECyclotomicNumberRing for OddSquarefreeCyclotomicNumberRing {

    fn m(&self) -> usize {
        self.m_factorization_squarefree.iter().copied().product::<i64>() as usize
    }
}

pub struct OddSquarefreeCyclotomicDecomposedNumberRing<F, A = Global> 
    where F: FFTAlgorithm<ZnBase> + PartialEq,
        A: Allocator + Clone
{
    ring: Zn,
    fft_table: F,
    /// contains `usize::MAX` whenenver the fft output index corresponds to a non-primitive root of unity, and an index otherwise
    fft_output_indices_to_indices: Vec<usize>,
    zeta_pow_rank: Vec<(usize, ZnEl)>,
    rank: usize,
    allocator: A
}

impl<F, A> PartialEq for OddSquarefreeCyclotomicDecomposedNumberRing<F, A> 
    where F: FFTAlgorithm<ZnBase> + PartialEq,
        A: Allocator + Clone
{
    fn eq(&self, other: &Self) -> bool {
        self.ring.get_ring() == other.ring.get_ring() && self.fft_table == other.fft_table
    }
}

impl<F, A> OddSquarefreeCyclotomicDecomposedNumberRing<F, A> 
    where F: FFTAlgorithm<ZnBase> + PartialEq,
        A: Allocator + Clone
{
    fn create_squarefree(fft_table: F, Fp: Zn, n_factorization: &[i64], allocator: A) -> Self {
        let m = n_factorization.iter().copied().product::<i64>();
        let rank = euler_phi_squarefree(&n_factorization) as usize;

        let Fp_as_field = (&Fp).as_field().ok().unwrap();
        let poly_ring = SparsePolyRing::new(Fp_as_field.clone(), "X");
        let cyclotomic_poly = cyclotomic_polynomial(&poly_ring, m as usize);
        assert_eq!(poly_ring.degree(&cyclotomic_poly).unwrap(), rank);
        let mut zeta_pow_rank = Vec::new();
        for (a, i) in poly_ring.terms(&cyclotomic_poly) {
            if i != rank {
                zeta_pow_rank.push((i, Fp.negate(Fp_as_field.get_ring().unwrap_element(Fp_as_field.clone_el(a)))));
            }
        }
        zeta_pow_rank.sort_unstable_by_key(|(i, _)| *i);

        let fft_output_indices_to_indices = (0..fft_table.len()).scan(0, |state, i| {
            let power = fft_table.unordered_fft_permutation(i);
            if n_factorization.iter().all(|p| power as i64 % *p != 0) {
                *state += 1;
                return Some(*state - 1);
            } else {
                return Some(usize::MAX);
            }
        }).collect::<Vec<_>>();

        return Self { ring: Fp, fft_table, zeta_pow_rank, rank, allocator, fft_output_indices_to_indices };
    }

    ///
    /// Computing this "generalized FFT" requires evaluating a polynomial at all primitive
    /// `m`-th roots of unity. However, the base FFT will compute the evaluation at all `m`-th
    /// roots of unity. This function gives an iterator over the index pairs `(i, j)`, where `i` 
    /// is an index into the vector of evaluations, and `j` is an index into the output of the base 
    /// FFT.
    /// 
    fn fft_output_indices<'a>(&'a self) -> impl Iterator<Item = (usize, usize)> + 'a {
        self.fft_output_indices_to_indices.iter().enumerate().filter_map(|(i, j)| if *j == usize::MAX { None } else { Some((*j, i)) })
    }

    pub fn allocator(&self) -> &A {
        &self.allocator
    }
}

impl<F, A> HENumberRingMod for OddSquarefreeCyclotomicDecomposedNumberRing<F, A> 
    where F: Send + Sync + FFTAlgorithm<ZnBase> + PartialEq,
        A: Send + Sync + Allocator + Clone
{
    fn mult_basis_to_small_basis<V>(&self, mut data: V)
        where V: VectorViewMut<ZnEl>
    {
        let ring = self.base_ring();
        let mut tmp = Vec::with_capacity_in(self.fft_table.len(), &self.allocator);
        tmp.extend((0..self.fft_table.len()).map(|_| ring.zero()));
        for (i, j) in self.fft_output_indices() {
            tmp[j] = ring.clone_el(data.at(i));
        }

        self.fft_table.unordered_inv_fft(&mut tmp[..], ring);

        for i in (self.rank()..self.fft_table.len()).rev() {
            let factor = ring.clone_el(&tmp[i]);
            for (j, c) in self.zeta_pow_rank.iter() {
                let mut add = ring.clone_el(&factor);
                ring.mul_assign_ref(&mut add, c);
                ring.add_assign(&mut tmp[i - self.rank() + *j], add);
            }
        }

        for i in 0..self.rank() {
            *data.at_mut(i) = ring.clone_el(&tmp[i]);
        }
    }

    fn small_basis_to_mult_basis<V>(&self, mut data: V)
        where V: VectorViewMut<ZnEl>
    {
        let ring = self.base_ring();
        let mut tmp = Vec::with_capacity_in(self.fft_table.len(), self.allocator.clone());
        tmp.extend((0..self.fft_table.len()).map(|_| ring.zero()));
        for i in 0..self.rank() {
            tmp[i] = ring.clone_el(data.at(i));
        }

        self.fft_table.unordered_fft(&mut tmp[..], ring);

        for (i, j) in self.fft_output_indices() {
            *data.at_mut(i) = ring.clone_el(&tmp[j]); 
        }
    }

    fn coeff_basis_to_small_basis<V>(&self, _data: V)
        where V: VectorViewMut<ZnEl>
    {}

    fn small_basis_to_coeff_basis<V>(&self, _data: V)
        where V: VectorViewMut<ZnEl>
    {}

    fn rank(&self) -> usize {
        self.rank
    }

    fn base_ring(&self) -> &Zn {
        &self.ring
    }
}

impl<F, A> HECyclotomicNumberRingMod for OddSquarefreeCyclotomicDecomposedNumberRing<F, A> 
    where F: Send + Sync + FFTAlgorithm<ZnBase> + PartialEq,
        A: Send + Sync + Allocator + Clone
{
    fn m(&self) -> usize {
        self.fft_table.len()
    }

    fn permute_galois_action<V1, V2>(&self, src: V1, mut dst: V2, galois_element: CyclotomicGaloisGroupEl)
        where V1: VectorView<ZnEl>,
            V2: SwappableVectorViewMut<ZnEl>
    {
        assert_eq!(self.rank(), src.len());
        assert_eq!(self.rank(), dst.len());
        let ring = self.base_ring();
        let galois_group = self.galois_group();
        let index_ring = galois_group.underlying_ring();
        let hom = index_ring.can_hom(&StaticRing::<i64>::RING).unwrap();
        
        for (j, i) in self.fft_output_indices() {
            *dst.at_mut(j) = ring.clone_el(src.at(self.fft_output_indices_to_indices[self.fft_table.unordered_fft_permutation_inv(
                index_ring.smallest_positive_lift(index_ring.mul(galois_group.to_ring_el(galois_element), hom.map(self.fft_table.unordered_fft_permutation(i) as i64))) as usize
            )]));
        }
    }
}