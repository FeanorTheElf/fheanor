use std::alloc::{Allocator, Global};

use feanor_math::algorithms::fft::bluestein::BluesteinFFT;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::algorithms::eea::{signed_eea, signed_gcd};
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::algorithms::fft::*;
use feanor_math::algorithms::eea::signed_lcm;
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
use feanor_math::seq::subvector::SubvectorView;
use tracing::instrument;
use feanor_math::seq::*;

use crate::number_ring::general_cyclotomic::*;
use crate::cyclotomic::*;
use super::{HECyclotomicNumberRing, HECyclotomicNumberRingMod, HENumberRing, HENumberRingMod};

///
/// Represents `Z[𝝵_m]` for an odd, squarefree `m`, but uses of the tensor decomposition
/// `Z[𝝵_m] = Z[𝝵_n1] ⊗ Z[𝝵_n2]` for various computational tasks (where `m = m1 * m2`
/// is a factorization into coprime factors).
/// 
#[derive(Clone)]
pub struct CompositeCyclotomicNumberRing {
    tensor_factor1: OddSquarefreeCyclotomicNumberRing,
    tensor_factor2: OddSquarefreeCyclotomicNumberRing
}

impl CompositeCyclotomicNumberRing {

    pub fn new(m1: usize, m2: usize) -> Self {
        assert!(m1 > 1);
        assert!(m2 > 1);
        assert!(signed_gcd(m1 as i64, m2 as i64, StaticRing::<i64>::RING) == 1);
        Self {
            tensor_factor1: OddSquarefreeCyclotomicNumberRing::new(m1),
            tensor_factor2: OddSquarefreeCyclotomicNumberRing::new(m2)
        }
    }
}

impl PartialEq for CompositeCyclotomicNumberRing {

    fn eq(&self, other: &Self) -> bool {
        self.tensor_factor1 == other.tensor_factor1 && self.tensor_factor2 == other.tensor_factor2
    }
}

impl HECyclotomicNumberRing for CompositeCyclotomicNumberRing {

    fn m(&self) -> usize {
        <_ as HECyclotomicNumberRing>::m(&self.tensor_factor1) * <_ as HECyclotomicNumberRing>::m(&self.tensor_factor2)
    }
}

impl HENumberRing for CompositeCyclotomicNumberRing {

    type Decomposed = CompositeCyclotomicDecomposedNumberRing<BluesteinFFT<ZnBase, ZnFastmulBase, CanHom<ZnFastmul, Zn>, AllocArc<DynLayoutMempool<Global>>>, AllocArc<DynLayoutMempool<Global>>>;

    fn mod_p(&self, Fp: Zn) -> Self::Decomposed {
        let m1 = self.tensor_factor1.m() as i64;
        let m2 = self.tensor_factor2.m() as i64;
        let m = m1 * m2;
        let r1 = <_ as HENumberRing>::rank(&self.tensor_factor1) as i64;
        let r2 = <_ as HENumberRing>::rank(&self.tensor_factor2) as i64;

        let poly_ring = SparsePolyRing::new(StaticRing::<i64>::RING, "X");
        let poly_ring = &poly_ring;
        let Phi_m1 = self.tensor_factor1.generating_poly(&poly_ring);
        let Phi_m2 = self.tensor_factor2.generating_poly(&poly_ring);
        let hom = Fp.can_hom(Fp.integer_ring()).unwrap().compose(Fp.integer_ring().can_hom(poly_ring.base_ring()).unwrap());
        let hom_ref = &hom;

        let (s, t, d) = signed_eea(m1, m2, StaticRing::<i64>::RING);
        assert_eq!(1, d);

        // the main task is to create a sparse representation of the two matrices that
        // represent the conversion from powerful basis to coefficient basis and back;
        // everything else is done by `SquarefreeCyclotomicNumberRing::mod_p()`

        let mut small_to_coeff_conversion_matrix = (0..(r1 * r2)).map(|_| Vec::new()).collect::<Vec<_>>();
        let mut coeff_to_small_conversion_matrix = (0..(r1 * r2)).map(|_| Vec::new()).collect::<Vec<_>>();

        let dense_poly_ring = DensePolyRing::new(poly_ring.base_ring(), "X");
        let Phi_n_sparse = cyclotomic_polynomial(&poly_ring, m as usize);
        let Phi_m = dense_poly_ring.can_hom(&poly_ring).unwrap().map_ref(&Phi_n_sparse);
        let mut X_pow_i = None;
        for i in 0..(m1 * m2) {

            let i1 = ((t * i % m1) + m1) % m1;
            let i2 = ((s * i % m2) + m2) % m2;
            debug_assert_eq!(i, (i1 * m / m1 + i2 * m / m2) % m);

            if i < r1 * r2 {
                let X1_power_reduced = poly_ring.div_rem_monic(poly_ring.pow(poly_ring.indeterminate(), i1 as usize), &Phi_m1).1;
                let X2_power_reduced = poly_ring.div_rem_monic(poly_ring.pow(poly_ring.indeterminate(), i2 as usize), &Phi_m2).1;
                
                coeff_to_small_conversion_matrix[i as usize] = poly_ring.terms(&X1_power_reduced).flat_map(|(c1, j1)| poly_ring.terms(&X2_power_reduced).map(move |(c2, j2)| 
                    (j1 + j2 * r1 as usize, hom_ref.map(poly_ring.base_ring().mul_ref(c1, c2))
                ))).collect::<Vec<_>>();
            }
            
            if i1 < r1 && i2 < r2 {
                if let Some(X_pow_i) = &X_pow_i {
                    small_to_coeff_conversion_matrix[(i2 * r1 + i1) as usize] = dense_poly_ring.terms(X_pow_i).map(|(c, i)| {
                        assert!(i < (r1 * r2) as usize);
                        (i, hom_ref.map_ref(c))
                    }).collect::<Vec<_>>();
                } else {
                    small_to_coeff_conversion_matrix[(i2 * r1 + i1) as usize] = vec![(i as usize, hom_ref.codomain().one())];
                }
            }

            if i == (r1 * r2) - 1 {
                X_pow_i = Some(dense_poly_ring.from_terms([(dense_poly_ring.base_ring().one(), (r1 * r2 - 1) as usize)]));
            }
            if let Some(X_pow_i) = &mut X_pow_i {
                dense_poly_ring.mul_assign_monomial(X_pow_i, 1);
                let lc = dense_poly_ring.coefficient_at(X_pow_i, (r1 * r2) as usize);
                // *X_pow_i = dense_poly_ring.div_rem_monic(std::mem::replace(X_pow_i, dense_poly_ring.zero()), &Phi_m).1;
                if dense_poly_ring.base_ring().is_zero(&lc) {
                    // do nothing
                } else if dense_poly_ring.base_ring().is_one(&lc) {
                    dense_poly_ring.get_ring().add_assign_from_terms(X_pow_i, dense_poly_ring.terms(&Phi_m).map(|(c, i)| (dense_poly_ring.base_ring().negate(dense_poly_ring.base_ring().clone_el(c)), i)));
                } else if dense_poly_ring.base_ring().is_neg_one(&lc) {
                    dense_poly_ring.get_ring().add_assign_from_terms(X_pow_i, dense_poly_ring.terms(&Phi_m).map(|(c, i)| (dense_poly_ring.base_ring().clone_el(c), i)));
                } else {
                    let lc = dense_poly_ring.base_ring().clone_el(lc);
                    dense_poly_ring.get_ring().add_assign_from_terms(X_pow_i, dense_poly_ring.terms(&Phi_m).map(|(c, i)| (dense_poly_ring.base_ring().negate(dense_poly_ring.base_ring().mul_ref(c, &lc)), i)));
                }
            }
        }

        CompositeCyclotomicDecomposedNumberRing {
            small_to_coeff_conversion_matrix: small_to_coeff_conversion_matrix,
            coeff_to_small_conversion_matrix: coeff_to_small_conversion_matrix,
            tensor_factor1: self.tensor_factor1.mod_p(Fp.clone()),
            tensor_factor2: self.tensor_factor2.mod_p(Fp)
        }
    }

    fn mod_p_required_root_of_unity(&self) -> usize {
        signed_lcm(self.tensor_factor1.mod_p_required_root_of_unity().try_into().unwrap(), self.tensor_factor2.mod_p_required_root_of_unity().try_into().unwrap(), StaticRing::<i64>::RING).try_into().unwrap()
    }

    fn inf_to_can_norm_expansion_factor(&self) -> f64 {
        return <_ as HENumberRing>::inf_to_can_norm_expansion_factor(&self.tensor_factor1) * <_ as HENumberRing>::inf_to_can_norm_expansion_factor(&self.tensor_factor2);
    }

    fn can_to_inf_norm_expansion_factor(&self) -> f64 {
        return <_ as HENumberRing>::can_to_inf_norm_expansion_factor(&self.tensor_factor1) * <_ as HENumberRing>::can_to_inf_norm_expansion_factor(&self.tensor_factor2);
    }

    fn generating_poly<P>(&self, poly_ring: P) -> El<P>
        where P: RingStore,
            P::Type: PolyRing + DivisibilityRing,
            <<P::Type as RingExtension>::BaseRing as RingStore>::Type: IntegerRing
    {
        cyclotomic_polynomial(&poly_ring, <_ as HECyclotomicNumberRing>::m(self) as usize)
    }

    fn rank(&self) -> usize {
        <_ as HENumberRing>::rank(&self.tensor_factor1) * <_ as HENumberRing>::rank(&self.tensor_factor2)
    }
}

///
/// The small basis is given by 
/// ```text
///   1 ⊗ 1,            𝝵1 ⊗ 1,            𝝵1^2 ⊗ 1,           ...,  𝝵1^(m1 - 1) ⊗ 1,
///   1 ⊗ 𝝵2,           𝝵1 ⊗ 𝝵2,           𝝵1^2 ⊗ 𝝵2,          ...,  𝝵1^(m1 - 1) ⊗ 𝝵2,
///   ...
///   1 ⊗ 𝝵2^(m2 - 1),  𝝵1 ⊗ 𝝵2^(m2 - 1),  𝝵1^2 ⊗ 𝝵2^(m2 - 1), ...,  𝝵1^(m1 - 1) ⊗ 𝝵2^(m2 - 1)
/// ```
/// 
pub struct CompositeCyclotomicDecomposedNumberRing<F, A = Global> 
    where F: FFTAlgorithm<ZnBase> + PartialEq,
        A: Allocator + Clone
{
    tensor_factor1: OddSquarefreeCyclotomicDecomposedNumberRing<F, A>,
    tensor_factor2: OddSquarefreeCyclotomicDecomposedNumberRing<F, A>,
    // the `i`-th entry is none if the `i`-th small basis vector equals the `i`-th coeff basis vector,
    // and otherwise, it contains the coeff basis representation of the `i`-th small basis vector
    small_to_coeff_conversion_matrix: Vec<Vec<(usize, ZnEl)>>,
    // same as `small_to_coeff_conversion_matrix` but with small and coeff basis swapped
    coeff_to_small_conversion_matrix: Vec<Vec<(usize, ZnEl)>>
}

impl<F, A> PartialEq for CompositeCyclotomicDecomposedNumberRing<F, A> 
    where F: FFTAlgorithm<ZnBase> + PartialEq,
        A: Allocator + Clone
{
    fn eq(&self, other: &Self) -> bool {
        self.tensor_factor1 == other.tensor_factor1 && self.tensor_factor2 == other.tensor_factor2
    }
}

impl<F, A> HENumberRingMod for CompositeCyclotomicDecomposedNumberRing<F, A> 
    where F: Send + Sync + FFTAlgorithm<ZnBase> + PartialEq,
        A: Send + Sync + Allocator + Clone
{
    #[instrument(skip_all)]
    fn small_basis_to_mult_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<ZnEl>
    {
        for i in 0..self.tensor_factor2.rank() {
            self.tensor_factor1.small_basis_to_mult_basis(SubvectorView::new(&mut data).restrict((i * self.tensor_factor1.rank())..((i + 1) * self.tensor_factor1.rank())));
        }
        for j in 0..self.tensor_factor1.rank() {
            self.tensor_factor2.small_basis_to_mult_basis(SubvectorView::new(&mut data).restrict(j..).step_by_view(self.tensor_factor1.rank()));
        }
    }

    #[instrument(skip_all)]
    fn mult_basis_to_small_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<ZnEl>
    {
        for j in 0..self.tensor_factor1.rank() {
            self.tensor_factor2.mult_basis_to_small_basis(SubvectorView::new(&mut data).restrict(j..).step_by_view(self.tensor_factor1.rank()));
        }
        for i in 0..self.tensor_factor2.rank() {
            self.tensor_factor1.mult_basis_to_small_basis(SubvectorView::new(&mut data).restrict((i * self.tensor_factor1.rank())..((i + 1) * self.tensor_factor1.rank())));
        }
    }

    #[instrument(skip_all)]
    fn coeff_basis_to_small_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<ZnEl>
    {
        let mut result = Vec::with_capacity_in(self.rank(), self.tensor_factor1.allocator());
        result.resize_with(self.rank(), || self.base_ring().zero());
        for i in 0..self.rank() {
            for (j, c) in &self.coeff_to_small_conversion_matrix[i] {
                self.base_ring().add_assign(&mut result[*j], self.base_ring().mul_ref(data.at(i), c));
            }
        }
        for (i, c) in result.drain(..).enumerate() {
            *data.at_mut(i) = c;
        }
    }

    #[instrument(skip_all)]
    fn small_basis_to_coeff_basis<V>(&self, mut data: V)
        where V: SwappableVectorViewMut<ZnEl>
    {
        let mut result = Vec::with_capacity_in(self.rank(), self.tensor_factor1.allocator());
        result.resize_with(self.rank(), || self.base_ring().zero());
        for i in 0..self.rank() {
            for (j, c) in &self.small_to_coeff_conversion_matrix[i] {
                self.base_ring().add_assign(&mut result[*j], self.base_ring().mul_ref(data.at(i), c));
            }
        }
        for (i, c) in result.drain(..).enumerate() {
            *data.at_mut(i) = c;
        }
    }

    fn rank(&self) -> usize {
        self.tensor_factor1.rank() * self.tensor_factor2.rank()
    }

    fn base_ring(&self) -> &Zn {
        self.tensor_factor1.base_ring()
    }
}

impl<F, A> HECyclotomicNumberRingMod for CompositeCyclotomicDecomposedNumberRing<F, A> 
    where F: Send + Sync + FFTAlgorithm<ZnBase> + PartialEq,
        A: Send + Sync + Allocator + Clone
{
    fn m(&self) -> usize {
        self.tensor_factor1.m() * self.tensor_factor2.m()
    }

    fn permute_galois_action<V1, V2>(&self, src: V1, mut dst: V2, galois_element: CyclotomicGaloisGroupEl)
        where V1: VectorView<ZnEl>,
            V2: SwappableVectorViewMut<ZnEl>
    {
        let index_ring = self.galois_group();
        let ring_factor1 = self.tensor_factor1.galois_group();
        let ring_factor2 = self.tensor_factor2.galois_group();

        let g1 = ring_factor1.from_representative(index_ring.representative(galois_element) as i64);
        let g2 = ring_factor2.from_representative(index_ring.representative(galois_element) as i64);
        let mut tmp = Vec::with_capacity_in(self.rank(), self.tensor_factor1.allocator());
        tmp.resize_with(self.rank(), || self.base_ring().zero());
        for i in 0..self.tensor_factor2.rank() {
            self.tensor_factor1.permute_galois_action(
                SubvectorView::new(&src).restrict((i * self.tensor_factor1.rank())..((i + 1) * self.tensor_factor1.rank())), 
                &mut tmp[(i * self.tensor_factor1.rank())..((i + 1) * self.tensor_factor1.rank())], 
                g1
            );
        }
        for j in 0..self.tensor_factor1.rank() {
            self.tensor_factor2.permute_galois_action(
                SubvectorView::new(&tmp[..]).restrict(j..).step_by_view(self.tensor_factor1.rank()), 
                SubvectorView::new(&mut dst).restrict(j..).step_by_view(self.tensor_factor1.rank()), 
                g2
            );
        }
    }
}
