use std::alloc::{Allocator, Global};
use std::fmt::{Debug, Formatter};
use std::ptr::Alignment;
use std::sync::Arc;

use feanor_math::algorithms::fft::bluestein::BluesteinFFT;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::algorithms::unity_root::{get_prim_root_of_unity, get_prim_root_of_unity_pow2};
use feanor_math::algorithms::fft::*;
use feanor_math::integer::*;
use feanor_math::iters::multi_cartesian_product;
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
use tracing::instrument;

use crate::{ZZi64, euler_phi, euler_phi_squarefree};
use crate::number_ring::galois::*;
use crate::number_ring::*;

///
/// Represents `Z[𝝵_m]` for an odd and squarefree `m`.
/// 
pub struct OddSquarefreeCyclotomicNumberRing {
    m_factorization_squarefree: Vec<i64>,
    galois_group: CyclotomicGaloisGroup,
    powinf_to_coeffinf_expansion: f64,
    coeffinf_to_powinf_expansion: f64
}

impl OddSquarefreeCyclotomicNumberRing {

    pub fn new(m: usize) -> Self {
        assert!(m > 1);
        let factorization = factor(StaticRing::<i64>::RING, m as i64);
        // while most of the arithmetic still works with non-squarefree m, our statements about the geometry
        // of the number ring as lattice don't hold anymore (currently this refers to the `norm1_to_norm2_expansion_factor`
        // functions)
        
        // why do we only support odd m? Because Bluestein FFT currently does not accept even lengths
        for (_, e) in &factorization {
            assert!(*e == 1, "m = {} is not squarefree", m);
        }

        Self {
            m_factorization_squarefree: factorization.iter().map(|(p, _)| *p).collect(),
            galois_group: CyclotomicGaloisGroupBase::new(m as u64),
            powinf_to_coeffinf_expansion: compute_powinf_to_coeffinf_expansion(m as i64),
            coeffinf_to_powinf_expansion: compute_coeffinf_to_powinf_expansion(m as i64)
        }
    }

    pub fn m(&self) -> u64 {
        self.galois_group.m()
    }

    ///
    /// Returns a bound on
    /// ```text
    ///   sup_(x in R \ {0}) | x |_caninf / | x |_coeffinf
    /// ```
    /// where `| x |_caninf := max_σ |σx|` is the canonical infinity norm and
    /// `| x |_coeffinf` is the infinity norm w.r.t. the coefficient basis representation.
    /// Here `σ` ranges through all embeddings `R -> C`.
    /// 
    pub fn coeffinf_to_caninf_expansion(&self) -> f64 {
        // every entry of the conversion matrix is bounded by 1 in 
        // absolute value
        self.rank() as f64
    }

    ///
    /// Returns a bound on
    /// ```text
    ///   sup_(x in R \ {0}) | x |_powinf / | x |_caninf
    /// ```
    /// where `| x |_caninf := max_σ |σx|` is the canonical infinity norm and
    /// `| x |_powinf` is the infinity norm w.r.t. the powerful basis representation.
    /// Here `σ` ranges through all embeddings `R -> C`.
    /// 
    /// Note that the powerful basis means the tensor product of the coefficient
    /// bases of all prime-power cyclotomic subfields. This is sometimes, but not
    /// necessarily, the "small basis" as given by [`CompositeCyclotomicNumberRing`].
    /// 
    /// [`CompositeCyclotomicNumberRing`]: crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing
    /// 
    pub fn caninf_to_powinf_expansion(&self) -> f64 {
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
    ///   sup_(x in R \ {0}) | x |_coeffinf / | x |_powinf
    /// ```
    /// where `| x |_powinf` is the infinity norm w.r.t. the powerful
    /// basis representation and `| x |_coeffinf` is the infinity norm w.r.t.
    /// the coefficient basis representation.
    /// 
    /// Note that the powerful basis means the tensor product of the coefficient
    /// bases of all prime-power cyclotomic subfields. This is sometimes, but not
    /// necessarily, the "small basis" as given by [`CompositeCyclotomicNumberRing`].
    /// 
    /// [`CompositeCyclotomicNumberRing`]: crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing
    /// 
    pub fn powinf_to_coeffinf_expansion(&self) -> f64 {
        self.powinf_to_coeffinf_expansion
    }

    ///
    /// Returns a bound on
    /// ```text
    ///   sup_(x in R \ {0}) |x|_powinf / |x|_coeffinf
    /// ```
    /// where `| x |_powinf` is the infinity norm w.r.t. the powerful
    /// basis representation and `| x |_coeffinf` is the infinity norm w.r.t.
    /// the coefficient basis representation.
    /// 
    /// Note that the powerful basis means the tensor product of the coefficient
    /// bases of all prime-power cyclotomic subfields. This is sometimes, but not
    /// necessarily, the "small basis" as given by [`CompositeCyclotomicNumberRing`].
    /// 
    /// [`CompositeCyclotomicNumberRing`]: crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing
    /// 
    pub fn coeffinf_to_powinf_expansion(&self) -> f64 {
        self.coeffinf_to_powinf_expansion
    }

    ///
    /// Returns a bound on
    /// ```text
    ///   sup_(x, y in R \ {0}) | xy |_powinf / (|x|_powinf |y|_powinf)
    /// ```
    /// where `|x|_powinf` is the infinity norm w.r.t. the powerful
    /// basis representation.
    /// 
    /// Note that the powerful basis means the tensor product of the coefficient
    /// bases of all prime-power cyclotomic subfields. This is sometimes, but not
    /// necessarily, the "small basis" as given by [`CompositeCyclotomicNumberRing`].
    /// 
    /// [`CompositeCyclotomicNumberRing`]: crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing
    /// 
    pub fn powinf_basis_product_expansion_factor(&self) -> f64 {
        self.m() as f64 * 2f64.powi(self.m_factorization_squarefree.len() as i32)
    }
}

///
/// Computes the linf operator norm of the powerful basis-to-coefficient basis
/// conversion function, i.e. the linear map
/// ```text
///   < X^(i1 * m/m1 + ... + ir * m/mr) | ij < phi(mj) > -> < 1, X, ..., X^(phi(m) - 1) >
///                            f                         ->          f mod Phi_m
/// ```
/// 
#[instrument(skip_all)]
pub fn compute_powinf_to_coeffinf_expansion(m: i64) -> f64 {
    let factorization = factor(ZZi64, m);
    let factorization_rings = factorization.iter().map(|(p, e)| Zn::new(ZZi64.pow(*p, *e) as u64)).collect::<Vec<_>>();
    let ZZX = SparsePolyRing::new(ZZi64, "X");
    let Phi_m = cyclotomic_polynomial(&ZZX, m as usize);
    let phi_m = ZZX.degree(&Phi_m).unwrap();
    let is_powerful_basis_monomial = |i: usize| {
        factorization_rings.iter().zip(factorization.iter()).all(|(ring, (p, e))| 
            ring.smallest_positive_lift(ring.checked_div(&ring.int_hom().map(i as i32), &ring.int_hom().map((m / *ring.modulus()).try_into().unwrap())).unwrap()) < ZZi64.pow(*p, e - 1) * (p - 1)
        )
    };
    let mut row_accumulated: Vec<i64> = (0..phi_m).map(|_| 0).collect::<Vec<_>>();
    let mut current = ZZX.negate(ZZX.clone_el(&Phi_m));
    ZZX.truncate_monomials(&mut current, row_accumulated.len());
    for i in 0..phi_m {
        if is_powerful_basis_monomial(i) {
            row_accumulated[i] += 1;
        }
    }
    for i in phi_m..(m as usize) {
        if is_powerful_basis_monomial(i) {
            for (c, j) in ZZX.terms(&current) {
                row_accumulated[j] = row_accumulated[j].checked_add(c.abs()).unwrap();
            }
        }
        ZZX.mul_assign_monomial(&mut current, 1);
        if ZZX.degree(&current).unwrap_or(0) == phi_m {
            current = ZZX.inclusion().fma_map(&Phi_m, &-ZZX.lc(&current).unwrap(), current)
        }
        assert!(ZZX.degree(&current).unwrap_or(0) < phi_m);
    }
    return *row_accumulated.iter().max().unwrap() as f64;
}

///
/// Computes the linf operator norm of the coefficient basis-to-powerful basis
/// conversion function, i.e. the inverse if the bijective linear map
/// ```text
///   < X^(i1 * m/m1 + ... + ir * m/mr) | ij < phi(mj) > -> < 1, X, ..., X^(phi(m) - 1) >
///                            f                         ->          f mod Phi_m
/// ```
/// 
#[instrument(skip_all)]
pub fn compute_coeffinf_to_powinf_expansion(m: i64) -> f64 {
    let factorization = factor(ZZi64, m);
    let factorization_rings = factorization.iter().map(|(p, e)| Zn::new(ZZi64.pow(*p, *e) as u64)).collect::<Vec<_>>();
    let phi_m = euler_phi(&factorization);
    let ZZX = SparsePolyRing::new(ZZi64, "X");
    let cyclotomic_polys = factorization.iter().map(|(p, e)| cyclotomic_polynomial(&ZZX, ZZi64.pow(*p, *e) as usize)).collect::<Vec<_>>();
    let mut row_accumulated: Vec<i64> = (0..phi_m).map(|_| 0).collect::<Vec<_>>();
    for i in 0..phi_m {
        let tensor_indices = factorization_rings.iter().map(|ring| ring.smallest_positive_lift(ring.checked_div(&ring.int_hom().map(i as i32), &ring.int_hom().map((m / *ring.modulus()).try_into().unwrap())).unwrap()));
        let tensor_polys = tensor_indices.enumerate().map(|(j, power)| ZZX.div_rem_monic(ZZX.from_terms([(1, power as usize)]), &cyclotomic_polys[j]).1).collect::<Vec<_>>();
        let tensor_polys_terms = tensor_polys.iter().map(|f| ZZX.terms(f).collect::<Vec<_>>()).collect::<Vec<_>>();
        for (k, coeff) in multi_cartesian_product(tensor_polys_terms.iter().map(|terms| terms.iter()), |terms| (
            terms.iter().map(|(_, pow)| pow).zip(factorization.iter()).fold(0, |current, (next, (p, e))| current * ZZi64.pow(*p, e - 1) as usize * (p - 1) as usize + next),
            ZZi64.prod(terms.iter().map(|(coeff, _)| coeff.abs()))
        ), |_, x| *x) {
            row_accumulated[k] = row_accumulated[k].checked_add(coeff).unwrap();
        }
    }
    return *row_accumulated.iter().max().unwrap() as f64;
}

impl Debug for OddSquarefreeCyclotomicNumberRing {

    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Z[𝝵_{}]", self.m())
    }
}

impl Clone for OddSquarefreeCyclotomicNumberRing {
    fn clone(&self) -> Self {
        Self {
            m_factorization_squarefree: self.m_factorization_squarefree.clone(),
            galois_group: self.galois_group.clone(),
            powinf_to_coeffinf_expansion: self.powinf_to_coeffinf_expansion,
            coeffinf_to_powinf_expansion: self.coeffinf_to_powinf_expansion
        }
    }
}

impl PartialEq for OddSquarefreeCyclotomicNumberRing {

    fn eq(&self, other: &Self) -> bool {
        self.m_factorization_squarefree == other.m_factorization_squarefree
    }
}

impl AbstractNumberRing for OddSquarefreeCyclotomicNumberRing {

    type NumberRingQuotientBases = OddSquarefreeCyclotomicDecomposedNumberRing<BluesteinFFT<ZnBase, ZnFastmulBase, CanHom<ZnFastmul, Zn>, AllocArc<DynLayoutMempool<Global>>>, AllocArc<DynLayoutMempool<Global>>>;

    fn small_basis_product_expansion_factor(&self) -> f64 {
        self.coeffinf_to_powinf_expansion() * self.coeffinf_to_powinf_expansion() * self.powinf_basis_product_expansion_factor() * self.powinf_to_coeffinf_expansion()
    }

    fn coeff_basis_product_expansion_factor(&self) -> f64 {
        self.small_basis_product_expansion_factor()
    }

    fn bases_mod_p(&self, Fp: Zn) -> Self::NumberRingQuotientBases {
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
            self.galois_group.clone(),
            AllocArc(Arc::new(DynLayoutMempool::new(Alignment::of::<u64>())))
        );
    }

    fn mod_p_required_root_of_unity(&self) -> u64 {
        return self.m() << StaticRing::<i64>::RING.abs_log2_ceil(&(2 * self.m()).try_into().unwrap()).unwrap();
    }

    fn generating_poly<P>(&self, poly_ring: P) -> El<P>
        where P: RingStore,
            P::Type: PolyRing + DivisibilityRing,
            <<P::Type as RingExtension>::BaseRing as RingStore>::Type: IntegerRing
    {
        cyclotomic_polynomial(&poly_ring, self.m() as usize)
    }

    fn rank(&self) -> usize {
        euler_phi_squarefree(&self.m_factorization_squarefree) as usize
    }

    fn galois_group(&self) -> &CyclotomicGaloisGroup {
        &self.galois_group
    }
}

pub struct OddSquarefreeCyclotomicDecomposedNumberRing<F, A = Global> 
    where F: FFTAlgorithm<ZnBase> + PartialEq,
        A: Allocator + Clone
{
    galois_group: CyclotomicGaloisGroup,
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
    fn create_squarefree(fft_table: F, Fp: Zn, n_factorization: &[i64], galois_group: CyclotomicGaloisGroup, allocator: A) -> Self {
        let m = galois_group.m();
        assert_eq!(m as i64, n_factorization.iter().copied().product::<i64>());
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

        return Self { galois_group: galois_group, ring: Fp, fft_table, zeta_pow_rank, rank, allocator, fft_output_indices_to_indices };
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

impl<F, A> NumberRingQuotientBases for OddSquarefreeCyclotomicDecomposedNumberRing<F, A> 
    where F: FFTAlgorithm<ZnBase> + PartialEq,
        A: Allocator + Clone
{
    fn galois_group(&self) -> &CyclotomicGaloisGroup {
        &self.galois_group
    }

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

    fn permute_galois_action<V1, V2>(&self, src: V1, mut dst: V2, galois_element: &GaloisGroupEl)
        where V1: VectorView<ZnEl>,
            V2: SwappableVectorViewMut<ZnEl>
    {
        assert_eq!(self.rank(), src.len());
        assert_eq!(self.rank(), dst.len());
        let ring = self.base_ring();
        let galois_group = &self.galois_group;
        let index_ring = galois_group.underlying_ring();
        let hom = index_ring.can_hom(&StaticRing::<i64>::RING).unwrap();
        
        for (j, i) in self.fft_output_indices() {
            *dst.at_mut(j) = ring.clone_el(src.at(self.fft_output_indices_to_indices[self.fft_table.unordered_fft_permutation_inv(
                index_ring.smallest_positive_lift(index_ring.mul(*galois_group.as_ring_el(galois_element), hom.map(self.fft_table.unordered_fft_permutation(i) as i64))) as usize
            )]));
        }
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::ciphertext_ring::double_rns_ring;
#[cfg(test)]
use crate::ciphertext_ring::single_rns_ring;
#[cfg(test)]
use crate::number_ring::quotient_by_int;
#[cfg(test)]
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
#[cfg(test)]
use crate::ring_literal;

#[test]
fn test_odd_cyclotomic_double_rns_ring() {
    double_rns_ring::test_with_number_ring(OddSquarefreeCyclotomicNumberRing::new(5));
    double_rns_ring::test_with_number_ring(OddSquarefreeCyclotomicNumberRing::new(7));
}

#[test]
fn test_odd_cyclotomic_single_rns_ring() {
    single_rns_ring::test_with_number_ring(OddSquarefreeCyclotomicNumberRing::new(5));
    single_rns_ring::test_with_number_ring(OddSquarefreeCyclotomicNumberRing::new(7));
}

#[test]
fn test_odd_cyclotomic_decomposition_ring() {
    quotient_by_int::test_with_number_ring(OddSquarefreeCyclotomicNumberRing::new(5));
    quotient_by_int::test_with_number_ring(OddSquarefreeCyclotomicNumberRing::new(7));
}

#[test]
fn test_permute_galois_automorphism() {
    let Fp = zn_64::Zn::new(257);
    let R = NumberRingQuotientByIntBase::new(OddSquarefreeCyclotomicNumberRing::new(7), Fp);
    let gal_el = |x: i64| R.acting_galois_group().from_representative(x);

    assert_el_eq!(R, ring_literal(&R, &[0, 0, 1, 0, 0, 0]), R.apply_galois_action(&ring_literal(&R, &[0, 1, 0, 0, 0, 0]), &gal_el(2)));
    assert_el_eq!(R, ring_literal(&R, &[0, 0, 0, 1, 0, 0]), R.apply_galois_action(&ring_literal(&R, &[0, 1, 0, 0, 0, 0]), &gal_el(3)));
    assert_el_eq!(R, ring_literal(&R, &[0, 0, 0, 0, 1, 0]), R.apply_galois_action(&ring_literal(&R, &[0, 0, 1, 0, 0, 0]), &gal_el(2)));
    assert_el_eq!(R, ring_literal(&R, &[-1, -1, -1, -1, -1, -1]), R.apply_galois_action(&ring_literal(&R, &[0, 0, 1, 0, 0, 0]), &gal_el(3)));
}

#[test]
fn test_compute_powinf_to_coeffinf_expansion() {
    assert_eq!(1., compute_powinf_to_coeffinf_expansion(17));
    assert_eq!(8., compute_powinf_to_coeffinf_expansion(17 * 5));
    assert_eq!(52., compute_powinf_to_coeffinf_expansion(13 * 3 * 7));
}

#[test]
fn test_compute_coeffinf_to_powinf_expansion() {
    assert_eq!(1., compute_coeffinf_to_powinf_expansion(17));
    assert_eq!(4., compute_coeffinf_to_powinf_expansion(17 * 5));
    assert_eq!(7., compute_coeffinf_to_powinf_expansion(13 * 3 * 7));
}