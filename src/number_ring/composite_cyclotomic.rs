use std::alloc::{Allocator, Global};
use std::fmt::{Debug, Formatter};

use feanor_math::algorithms::convolution::STANDARD_CONVOLUTION;
use feanor_math::algorithms::eea::{signed_eea, signed_gcd, signed_lcm};
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::algorithms::int_factor::factor;
use feanor_math::integer::*;
use feanor_math::rings::poly::*;
use feanor_math::divisibility::*;
use feanor_math::primitive_int::*;
use feanor_math::ring::*;
use feanor_math::homomorphism::*;
use feanor_math::rings::poly::sparse_poly::SparsePolyRing;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::rings::zn::*;
use feanor_math::seq::subvector::SubvectorView;
use feanor_math::seq::*;
use tracing::instrument;

use crate::number_ring::galois::*;
use crate::number_ring::general_cyclotomic::*;
use crate::ZZi64;
use crate::number_ring::*;
use crate::number_ring::poly_remainder::CyclotomicPolyReducer;

///
/// Represents `Z[𝝵_m]` for an odd, squarefree `m`, but uses of the tensor decomposition
/// `Z[𝝵_m] = Z[𝝵_m1] ⊗ Z[𝝵_m2]` for various computational tasks (where `m = m1 * m2`
/// is a factorization into coprime factors).
/// 
pub struct CompositeCyclotomicNumberRing<L: AbstractNumberRing = OddSquarefreeCyclotomicNumberRing, R: AbstractNumberRing = OddSquarefreeCyclotomicNumberRing> {
    left_factor: L,
    right_factor: R,
    joint_galois_group: CyclotomicGaloisGroup,
    powinf_to_coeffinf_expansion: f64,
    coeffinf_to_powinf_expansion: f64
}

impl CompositeCyclotomicNumberRing {

    pub fn new(m1: usize, m2: usize) -> Self {
        Self::new_with_factors(OddSquarefreeCyclotomicNumberRing::new(m1), OddSquarefreeCyclotomicNumberRing::new(m2))
    }
}

impl<L: AbstractNumberRing, R: AbstractNumberRing> CompositeCyclotomicNumberRing<L, R> {

    pub fn new_with_factors(left: L, right: R) -> Self {
        let m1 = left.galois_group().m();
        let m2 = right.galois_group().m();
        assert!(m1 > 1);
        assert!(m2 > 1);
        assert!(signed_gcd(m1 as i64, m2 as i64, StaticRing::<i64>::RING) == 1);
        Self {
            joint_galois_group: CyclotomicGaloisGroupBase::new(m1 * m2),
            left_factor: left,
            right_factor: right,
            powinf_to_coeffinf_expansion: compute_powinf_to_coeffinf_expansion(m1 as i64 * m2 as i64),
            coeffinf_to_powinf_expansion: compute_coeffinf_to_powinf_expansion(m1 as i64 * m2 as i64)
        }
    }

    pub fn m1(&self) -> u64 {
        self.left_factor.galois_group().m()
    }

    pub fn m2(&self) -> u64 {
        self.right_factor.galois_group().m()
    }

    pub fn m(&self) -> u64 {
        self.m1() * self.m2()
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
    /// bases of all prime-power cyclotomic subfields. This is not always the
    /// same as the small basis! (it is if both `left` and `right` are prime
    /// power cyclotomics)
    /// 
    fn powinf_basis_product_expansion_factor(&self) -> f64 {
        self.m() as f64 * 2f64.powi(factor(ZZi64, self.m() as i64).len() as i32)
    }
}

impl<L: AbstractNumberRing, R: AbstractNumberRing> Clone for CompositeCyclotomicNumberRing<L, R> {
    
    fn clone(&self) -> Self {
        Self {
            joint_galois_group: self.joint_galois_group.clone(),
            left_factor: self.left_factor.clone(),
            right_factor: self.right_factor.clone(),
            powinf_to_coeffinf_expansion: self.powinf_to_coeffinf_expansion,
            coeffinf_to_powinf_expansion: self.coeffinf_to_powinf_expansion
        }
    }
}

impl<L: AbstractNumberRing + Debug, R: AbstractNumberRing + Debug> Debug for CompositeCyclotomicNumberRing<L, R> {
    
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} ⊗ {:?}", self.left_factor, self.right_factor)
    }
}

impl<L: AbstractNumberRing, R: AbstractNumberRing> PartialEq for CompositeCyclotomicNumberRing<L, R> {

    fn eq(&self, other: &Self) -> bool {
        self.left_factor == other.left_factor && self.right_factor == other.right_factor
    }
}

impl<L: AbstractNumberRing, R: AbstractNumberRing> AbstractNumberRing for CompositeCyclotomicNumberRing<L, R> {

    type NumberRingQuotientBases = CompositeCyclotomicNumberRingQuotientBases<L::NumberRingQuotientBases, R::NumberRingQuotientBases>;

    fn small_basis_product_expansion_factor(&self) -> f64 {
        // We use the tensor-product compatibility of the tensor product.
        // Write `|x|` for the linf norm of `x` when represented in the small basis.
        // Let `L` and `R` be the left resp. right tensor product factor of this number
        // ring. Then `L` has a small basis `e_1, ..., e_l`. Every element of `L ⊗ R`
        // has a unique representation as `sum_i e_i ⊗ a_i` for elements `a_i` in `R`.
        // We have
        // ```text
        //   |(sum_i e_i ⊗ a_i)(sum_j e_j ⊗ a'_j)| <= sum_(i,j) |e_i e_j ⊗ a_i a'_j|
        //     =  sum_(i, j) |e_i e_j| |a_i a'_j|
        //     <= sum_(i, j) f_L f_R |a_i| |a'_j|
        //     = f_L f_R (sum_i |a_i|)(sum_j |a'_j|)
        //     = f_L f_R |sum_i e_i ⊗ a_i| |sum_j e_j ⊗ a_j|
        // ```
        self.left_factor.small_basis_product_expansion_factor() * self.right_factor.small_basis_product_expansion_factor()
    }

    fn coeff_basis_product_expansion_factor(&self) -> f64 {
        // see the argument in general_cyclotomic
        self.coeffinf_to_powinf_expansion * self.coeffinf_to_powinf_expansion * self.powinf_basis_product_expansion_factor() * self.powinf_to_coeffinf_expansion
    }

    fn bases_mod_p(&self, Fp: Zn) -> Self::NumberRingQuotientBases {
        let r1 = self.left_factor.rank() as i64;
        let r2 = self.right_factor.rank() as i64;
        let m1 = self.left_factor.galois_group().m() as i64;
        let m2 = self.right_factor.galois_group().m() as i64;
        let m = m1 * m2;

        let poly_ring = SparsePolyRing::new(StaticRing::<i64>::RING, "X");
        let poly_ring = &poly_ring;
        let Phi_m1 = self.left_factor.generating_poly(&poly_ring);
        let Phi_m2 = self.right_factor.generating_poly(&poly_ring);
        let hom = Fp.can_hom(Fp.integer_ring()).unwrap().compose(Fp.integer_ring().can_hom(poly_ring.base_ring()).unwrap());
        let hom_ref = &hom;

        let (s, t, d) = signed_eea(m1, m2, StaticRing::<i64>::RING);
        assert_eq!(1, d);

        // the main task is to create a sparse representation of the matrix that
        // represent the conversion from coefficient basis to the tensor product of the
        // coefficient bases; everything else is done by `SquarefreeCyclotomicNumberRing::mod_p()`

        // it turns out to be no problem to store this matrix, using a sparse representation;
        // however, the reverse transform matrix has columns that often have close to `m`
        // nonzero entries (instead of just `m1` resp. `m2`), and can thus take
        // significant time and space; hence, we instead use the cyclotomic poly reducer
        let mut coeff_to_tensorcoeff_conversion_matrix = (0..(r1 * r2)).map(|_| Vec::new()).collect::<Vec<_>>();

        for i in 0..(r1 * r2) {

            let i1 = ((t * i % m1) + m1) % m1;
            let i2 = ((s * i % m2) + m2) % m2;
            debug_assert_eq!(i, (i1 * m / m1 + i2 * m / m2) % m);

            let X1_power_reduced = poly_ring.div_rem_monic(poly_ring.pow(poly_ring.indeterminate(), i1 as usize), &Phi_m1).1;
            let X2_power_reduced = poly_ring.div_rem_monic(poly_ring.pow(poly_ring.indeterminate(), i2 as usize), &Phi_m2).1;

            coeff_to_tensorcoeff_conversion_matrix[i as usize] = poly_ring.terms(&X1_power_reduced).flat_map(|(c1, j1)| poly_ring.terms(&X2_power_reduced).map(move |(c2, j2)| 
                (j1 + j2 * r1 as usize, hom_ref.map(poly_ring.base_ring().mul_ref(c1, c2))
            ))).collect::<Vec<_>>();
        }

        let cyclotomic_poly_reducer = CyclotomicPolyReducer::new(Fp, m as u64, STANDARD_CONVOLUTION);

        CompositeCyclotomicNumberRingQuotientBases {
            coeff_to_tensorcoeff_conversion_matrix: coeff_to_tensorcoeff_conversion_matrix,
            cyclotomic_poly_reducer: cyclotomic_poly_reducer,
            left_factor: self.left_factor.bases_mod_p(Fp.clone()),
            right_factor: self.right_factor.bases_mod_p(Fp),
            allocator: Global,
            joint_galois_group: self.joint_galois_group.clone()
        }
    }

    fn mod_p_required_root_of_unity(&self) -> u64 {
        signed_lcm(self.left_factor.mod_p_required_root_of_unity().try_into().unwrap(), self.right_factor.mod_p_required_root_of_unity().try_into().unwrap(), StaticRing::<i64>::RING).try_into().unwrap()
    }

    fn generating_poly<P>(&self, poly_ring: P) -> El<P>
        where P: RingStore,
            P::Type: PolyRing + DivisibilityRing,
            <<P::Type as RingExtension>::BaseRing as RingStore>::Type: IntegerRing
    {
        cyclotomic_polynomial(&poly_ring, self.m() as usize)
    }

    fn rank(&self) -> usize {
        self.left_factor.rank() * self.right_factor.rank()
    }

    fn galois_group(&self) -> &CyclotomicGaloisGroup {
        &self.joint_galois_group
    }
}

///
/// The [`NumberRingQuotientBases`] for [`CompositeCyclotomicNumberRing`].
/// 
/// The small basis is given by 
/// ```text
///   e1 ⊗ e1',           e2 ⊗ e1',           e3 ⊗ e1',           ...,  e(m1 - 1) ⊗ e1',
///   e1 ⊗ e2',           e2 ⊗ e2',           e3 ⊗ e2',           ...,  e(m1 - 1) ⊗ e2',
///   ...
///   e1 ⊗ e(m2 - 1)',    e2 ⊗ e(m2 - 1)',    e3 ⊗ e(m2 - 1)',    ...,  e(m1 - 1) ⊗ e(m2 - 1)'
/// ```
/// where `e1, ..., e(m1 - 1)` and `e1', ..., e(m2 - 1)'` are the small bases of
/// `left` and `right`, respectively.
/// 
/// In particular, this is the powerful basis if `m1` and `m2` are prime, and
/// `left` and `right` use the coefficient basis as small basis.
/// Otherwise, it is somewhere between coefficient and powerful basis.
/// 
pub struct CompositeCyclotomicNumberRingQuotientBases<L, R, A = Global> 
    where L: NumberRingQuotientBases,
        R: NumberRingQuotientBases,
        A: Allocator + Clone
{
    allocator: A,
    left_factor: L,
    right_factor: R,
    // the `i`-th entry is none if the `i`-th small basis vector equals the `i`-th coeff basis vector,
    // and otherwise, it contains the coeff basis representation of the `i`-th small basis vector
    coeff_to_tensorcoeff_conversion_matrix: Vec<Vec<(usize, ZnEl)>>,
    cyclotomic_poly_reducer: CyclotomicPolyReducer<Zn>,
    joint_galois_group: CyclotomicGaloisGroup
}

impl<L, R, A> PartialEq for CompositeCyclotomicNumberRingQuotientBases<L, R, A> 
    where L: NumberRingQuotientBases,
        R: NumberRingQuotientBases,
        A: Allocator + Clone
{
    fn eq(&self, other: &Self) -> bool {
        self.left_factor == other.left_factor && self.right_factor == other.right_factor
    }
}

impl<L, R, A> NumberRingQuotientBases for CompositeCyclotomicNumberRingQuotientBases<L, R, A> 
    where L: NumberRingQuotientBases,
        R: NumberRingQuotientBases,
        A: Allocator + Clone 
{
    fn galois_group(&self) -> &CyclotomicGaloisGroup {
        &self.joint_galois_group
    }

    #[instrument(skip_all)]
    fn small_basis_to_mult_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<ZnEl>
    {
        for i in 0..self.right_factor.rank() {
            self.left_factor.small_basis_to_mult_basis(SubvectorView::new(&mut data).restrict((i * self.left_factor.rank())..((i + 1) * self.left_factor.rank())));
        }
        for j in 0..self.left_factor.rank() {
            self.right_factor.small_basis_to_mult_basis(SubvectorView::new(&mut data).restrict(j..).step_by_view(self.left_factor.rank()));
        }
    }

    #[instrument(skip_all)]
    fn mult_basis_to_small_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<ZnEl>
    {
        for j in 0..self.left_factor.rank() {
            self.right_factor.mult_basis_to_small_basis(SubvectorView::new(&mut data).restrict(j..).step_by_view(self.left_factor.rank()));
        }
        for i in 0..self.right_factor.rank() {
            self.left_factor.mult_basis_to_small_basis(SubvectorView::new(&mut data).restrict((i * self.left_factor.rank())..((i + 1) * self.left_factor.rank())));
        }
    }

    #[instrument(skip_all)]
    fn coeff_basis_to_small_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<ZnEl>
    {
        let mut result = Vec::with_capacity_in(self.rank(), &self.allocator);
        result.resize_with(self.rank(), || self.base_ring().zero());
        for i in 0..self.rank() {
            for (j, c) in &self.coeff_to_tensorcoeff_conversion_matrix[i] {
                self.base_ring().add_assign(&mut result[*j], self.base_ring().mul_ref(data.at(i), c));
            }
        }
        for (i, c) in result.drain(..).enumerate() {
            *data.at_mut(i) = c;
        }

        for j in 0..self.left_factor.rank() {
            self.right_factor.coeff_basis_to_small_basis(SubvectorView::new(&mut data).restrict(j..).step_by_view(self.left_factor.rank()));
        }
        for i in 0..self.right_factor.rank() {
            self.left_factor.coeff_basis_to_small_basis(SubvectorView::new(&mut data).restrict((i * self.left_factor.rank())..((i + 1) * self.left_factor.rank())));
        }
    }

    #[instrument(skip_all)]
    fn small_basis_to_coeff_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<ZnEl>
    {
        for j in 0..self.left_factor.rank() {
            self.right_factor.small_basis_to_coeff_basis(SubvectorView::new(&mut data).restrict(j..).step_by_view(self.left_factor.rank()));
        }
        for i in 0..self.right_factor.rank() {
            self.left_factor.small_basis_to_coeff_basis(SubvectorView::new(&mut data).restrict((i * self.left_factor.rank())..((i + 1) * self.left_factor.rank())));
        }

        let r1 = self.left_factor.rank();
        let r2 = self.right_factor.rank();
        let m1 = self.left_factor.galois_group().m() as usize;
        let m2 = self.right_factor.galois_group().m() as usize;
        let m = m1 * m2;

        let mut result = Vec::with_capacity_in(m, &self.allocator);
        result.resize_with(m, || self.base_ring().zero());
        
        for i2 in 0..r2 {
            for i1 in 0..r1 {
                let mut target_idx = i1 * m2 + i2 * m1;
                if target_idx >= m {
                    target_idx -= m;
                }
                result[target_idx] = *data.at(i1 + i2 * r1);
            }
        }
        self.cyclotomic_poly_reducer.remainder(&mut result);
        for (i, c) in result.into_iter().take(r1 * r2).enumerate() {
            *data.at_mut(i) = c;
        }
    }

    fn rank(&self) -> usize {
        self.left_factor.rank() * self.right_factor.rank()
    }

    fn base_ring(&self) -> &Zn {
        self.left_factor.base_ring()
    }

    fn permute_galois_action<V1, V2>(&self, src: V1, mut dst: V2, galois_element: &GaloisGroupEl)
        where V1: VectorView<ZnEl>,
            V2: SwappableVectorViewMut<ZnEl>
    {
        let ring_factor1 = self.left_factor.galois_group();
        let ring_factor2 = self.right_factor.galois_group();
        let galois_group = &self.joint_galois_group;
        let g1 = ring_factor1.from_representative(galois_group.representative(galois_element) as i64);
        let g2 = ring_factor2.from_representative(galois_group.representative(galois_element) as i64);
        let mut tmp = Vec::with_capacity_in(self.rank(), &self.allocator);
        tmp.resize_with(self.rank(), || self.base_ring().zero());
        for i in 0..self.right_factor.rank() {
            self.left_factor.permute_galois_action(
                SubvectorView::new(&src).restrict((i * self.left_factor.rank())..((i + 1) * self.left_factor.rank())), 
                &mut tmp[(i * self.left_factor.rank())..((i + 1) * self.left_factor.rank())], 
                &g1
            );
        }
        for j in 0..self.left_factor.rank() {
            self.right_factor.permute_galois_action(
                SubvectorView::new(&tmp[..]).restrict(j..).step_by_view(self.left_factor.rank()), 
                SubvectorView::new(&mut dst).restrict(j..).step_by_view(self.left_factor.rank()), 
                &g2
            );
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
use crate::ring_literal;
#[cfg(test)]
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
#[cfg(test)]
use crate::ntt::RustNegacyclicNTT;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;

#[test]
fn test_odd_cyclotomic_double_rns_ring() {
    double_rns_ring::test_with_number_ring(CompositeCyclotomicNumberRing::new(3, 5));
    double_rns_ring::test_with_number_ring(CompositeCyclotomicNumberRing::new(3, 7));
    double_rns_ring::test_with_number_ring(CompositeCyclotomicNumberRing::new_with_factors(OddSquarefreeCyclotomicNumberRing::new(3), Pow2CyclotomicNumberRing::<RustNegacyclicNTT<_>>::new(8)));
}

#[test]
fn test_odd_cyclotomic_single_rns_ring() {
    single_rns_ring::test_with_number_ring(CompositeCyclotomicNumberRing::new(3, 5));
    single_rns_ring::test_with_number_ring(CompositeCyclotomicNumberRing::new(3, 7));
    single_rns_ring::test_with_number_ring(CompositeCyclotomicNumberRing::new_with_factors(OddSquarefreeCyclotomicNumberRing::new(3), Pow2CyclotomicNumberRing::<RustNegacyclicNTT<_>>::new(8)));
}

#[test]
fn test_odd_cyclotomic_decomposition_ring() {
    quotient_by_int::test_with_number_ring(CompositeCyclotomicNumberRing::new(3, 5));
    quotient_by_int::test_with_number_ring(CompositeCyclotomicNumberRing::new(3, 7));
    quotient_by_int::test_with_number_ring(CompositeCyclotomicNumberRing::new_with_factors(OddSquarefreeCyclotomicNumberRing::new(3), Pow2CyclotomicNumberRing::<RustNegacyclicNTT<_>>::new(8)));
}

#[test]
fn test_small_coeff_basis_conversion() {
    let ring = zn_64::Zn::new(241);
    let number_ring = CompositeCyclotomicNumberRing::new(3, 5);
    let decomposition = number_ring.bases_mod_p(ring);

    let arr_create = |data: [i32; 8]| std::array::from_fn::<_, 8, _>(|i| ring.int_hom().map(data[i]));
    let assert_arr_eq = |fst: [zn_64::ZnEl; 8], snd: [zn_64::ZnEl; 8]| assert!(
        fst.iter().zip(snd.iter()).all(|(x, y)| ring.eq_el(x, y)),
        "expected {:?} = {:?}",
        std::array::from_fn::<_, 8, _>(|i| ring.format(&fst[i])),
        std::array::from_fn::<_, 8, _>(|i| ring.format(&snd[i]))
    );

    let original = arr_create([1, 0, 0, 0, 0, 0, 0, 0]);
    let expected = arr_create([1, 0, 0, 0, 0, 0, 0, 0]);
    let mut actual = original;
    decomposition.coeff_basis_to_small_basis(&mut actual);
    assert_arr_eq(expected, actual);
    decomposition.small_basis_to_coeff_basis(&mut actual);
    assert_arr_eq(original, actual);
    
    // 𝝵_15 = 𝝵_3^-1 ⊗ 𝝵_5^2 = (-1 - 𝝵_3) ⊗ 𝝵_5^2
    let original = arr_create([0, 1, 0, 0, 0, 0, 0, 0]);
    let expected = arr_create([0, 0, 0, 0, 240, 240, 0, 0]);
    let mut actual = original;
    decomposition.coeff_basis_to_small_basis(&mut actual);
    assert_arr_eq(expected, actual);
    decomposition.small_basis_to_coeff_basis(&mut actual);
    assert_arr_eq(original, actual);

    let original = arr_create([0, 0, 240, 0, 0, 0, 0, 0]);
    let expected = arr_create([0, 1, 0, 1, 0, 1, 0, 1]);
    let mut actual = original;
    decomposition.coeff_basis_to_small_basis(&mut actual);
    assert_arr_eq(expected, actual);
    decomposition.small_basis_to_coeff_basis(&mut actual);
    assert_arr_eq(original, actual);

    let original = arr_create([0, 0, 0, 1, 0, 0, 0, 0]);
    let expected = arr_create([0, 0, 1, 0, 0, 0, 0, 0]);
    let mut actual = original;
    decomposition.coeff_basis_to_small_basis(&mut actual);
    assert_arr_eq(expected, actual);
    decomposition.small_basis_to_coeff_basis(&mut actual);
    assert_arr_eq(original, actual);

    let original = arr_create([0, 0, 0, 0, 0, 1, 0, 0]);
    let expected = arr_create([0, 1, 0, 0, 0, 0, 0, 0]);
    let mut actual = original;
    decomposition.coeff_basis_to_small_basis(&mut actual);
    assert_arr_eq(expected, actual);
    decomposition.small_basis_to_coeff_basis(&mut actual);
    assert_arr_eq(original, actual);

    let number_ring = CompositeCyclotomicNumberRing::new_with_factors(OddSquarefreeCyclotomicNumberRing::new(3), Pow2CyclotomicNumberRing::<RustNegacyclicNTT<_>>::new(8));
    let decomposition = number_ring.bases_mod_p(ring);
    let original = arr_create([-1, 0, 0, 0, 1, 0, 0, 0]);
    let expected = arr_create([0, 1, 0, 0, 0, 0, 0, 0]);
    let mut actual = original;
    decomposition.coeff_basis_to_small_basis(&mut actual);
    assert_arr_eq(expected, actual);
    decomposition.small_basis_to_coeff_basis(&mut actual);
    assert_arr_eq(original, actual);
}

#[test]
fn test_permute_galois_automorphism() {
    let Fp = zn_64::Zn::new(257);
    let R = NumberRingQuotientByIntBase::new(CompositeCyclotomicNumberRing::new(5, 3), Fp);
    let gal_el = |x: i64| R.number_ring().galois_group().from_representative(x);

    assert_el_eq!(R, ring_literal(&R, &[0, 0, 1, 0, 0, 0, 0, 0]), R.apply_galois_action(&ring_literal(&R, &[0, 1, 0, 0, 0, 0, 0, 0]), &gal_el(2)));
    assert_el_eq!(R, ring_literal(&R, &[0, 0, 0, 0, 1, 0, 0, 0]), R.apply_galois_action(&ring_literal(&R, &[0, 1, 0, 0, 0, 0, 0, 0]), &gal_el(4)));
    assert_el_eq!(R, ring_literal(&R, &[-1, 1, 0, -1, 1, -1, 0, 1]), R.apply_galois_action(&ring_literal(&R, &[0, 1, 0, 0, 0, 0, 0, 0]), &gal_el(8)));
    assert_el_eq!(R, ring_literal(&R, &[-1, 1, 0, -1, 1, -1, 0, 1]), R.apply_galois_action(&ring_literal(&R, &[0, 0, 0, 0, 1, 0, 0, 0]), &gal_el(2)));
}