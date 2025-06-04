
use feanor_math::algorithms::linsolve::LinSolveRingStore;
use feanor_math::homomorphism::*;
use feanor_math::matrix::OwnedMatrix;
use feanor_math::ring::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::primitive_int::*;
use feanor_math::seq::VectorFn;
use matmul::MatmulTransform;
use tracing::instrument;

use crate::number_ring::hypercube::structure::HypercubeStructure;
use crate::number_ring::hypercube::isomorphism::*;
use crate::number_ring::*;
use crate::cyclotomic::*;
use crate::lintransform::*;

#[instrument(skip_all)]
fn dwt1d_matrix(H: &HypercubeStructure, slot_ring: &SlotRingOver<Zn>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOver<Zn>>) -> OwnedMatrix<El<SlotRingOver<Zn>>> {
    assert!(H.is_tensor_product_compatible());

    let Gal = H.galois_group();
    let ZZ_to_Zn = Gal.underlying_ring().can_hom(&StaticRing::<i64>::RING).unwrap();

    OwnedMatrix::from_fn(H.dim_length(dim_index), H.dim_length(dim_index), |i, j| {
        let exponent = Gal.underlying_ring().prod([
            Gal.to_ring_el(H.map_1d(dim_index, -(i as i64))),
            ZZ_to_Zn.map(j as i64),
            ZZ_to_Zn.map(H.m() as i64 / H.factor_of_m(dim_index).unwrap())
        ]);
        return slot_ring.clone_el(&*zeta_powertable.get_power(Gal.underlying_ring().smallest_lift(exponent)));
    })
}

///
/// Interprets each hypercolumn along the `i = dim_index`-th dimension as a vector of 
/// length `l_i`, and computes the discrete weighted transform along this vector, 
/// i.e. the evaluation at the primitive roots of unity `𝝵^(m/m_i * j)` for `j` coprime
/// to `m_i`. This assumes that `l_i = phi(m_i)`, i.e. the hypercube dimension is good.
/// 
#[instrument(skip_all)]
fn dwt1d<'a, NumberRing>(H: &DefaultHypercube<NumberRing>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOver<Zn>>) -> Vec<MatmulTransform<NumberRing>>
    where NumberRing: HECyclotomicNumberRing + Clone
{
    if H.hypercube().dim_length(dim_index) == 1{
        Vec::new()
    } else {
        // multiplication with the matrix `A(i, j) = 𝝵^(j * shift_element(-i))` if we consider an element as multiple vectors along the `dim_index`-th dimension
        let A = dwt1d_matrix(H.hypercube(), H.slot_ring(), dim_index, zeta_powertable);
    
        vec![MatmulTransform::matmul1d(
            H, 
            dim_index, 
            |i, j, _idxs| H.slot_ring().clone_el(A.at(i, j))
        )]
    }
}

///
/// Inverse to [`dwt1d()`].
/// 
#[instrument(skip_all)]
fn dwt1d_inv<'a, NumberRing>(H: &DefaultHypercube<NumberRing>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOver<Zn>>) -> Vec<MatmulTransform<NumberRing>>
    where NumberRing: HECyclotomicNumberRing + Clone
{
    if H.hypercube().dim_length(dim_index) == 1{
        Vec::new()
    } else {
        let mut A = dwt1d_matrix(H.hypercube(), H.slot_ring(), dim_index, zeta_powertable);
        let mut rhs = OwnedMatrix::identity(H.hypercube().dim_length(dim_index), H.hypercube().dim_length(dim_index), H.slot_ring());
        let mut sol = OwnedMatrix::zero(H.hypercube().dim_length(dim_index), H.hypercube().dim_length(dim_index), H.slot_ring());
        <_ as LinSolveRingStore>::solve_right(H.slot_ring(), A.data_mut(), rhs.data_mut(), sol.data_mut()).assert_solved();

        // multiplication with the matrix `A(i, j) = 𝝵^(j * shift_element(-i))` if we consider an element as multiple vectors along the `dim_index`-th dimension
        vec![MatmulTransform::matmul1d(
            H, 
            dim_index, 
            |i, j, _idxs| H.slot_ring().clone_el(sol.at(i, j))
        )]
    }
}

/// 
/// Computes the first step in the <https://ia.cr/2014/873>-style linear transform for fat bootstrapping with composite moduli.
/// 
/// In this step, for each hypercolumn along the first hypercube dimension, the coefficients of each slot of
/// (w.r.t. the power-of-`𝝵` basis of each slot) are moved to the coefficients of a `d l_1 = phi(m_1)` degree
/// polynomial, stored w.r.t. "along" the hypercolumn.
/// Formally, this is the map
/// ```text
///   𝝵^j e_(i_1, ..., i_r)  ->  X1^(j * l_1 + i_1) e_(*, i_2, ..., i_r)
///       for j < d, i_1 < l_1, ..., i_r < l_r
/// ```
/// where
/// ```text
///   e_(*, i_2, ..., i_r) = sum_(i_1) e_(i_1, ..., i_r)
/// ```
/// 
/// This requires that the underlying hypercube structure is a Halevi-Shoup hypercube structure, and that `d l_1 = phi(m_1)`.
/// 
#[instrument(skip_all)]
fn slots_to_powcoeffs_fat_fst_step<NumberRing>(H: &DefaultHypercube<NumberRing>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOver<Zn>>) -> OwnedMatrix<El<Zn>>
    where NumberRing: HECyclotomicNumberRing + Clone
{
    let Gal = H.galois_group();
    let ZZ_to_Gal = Gal.underlying_ring().can_hom(&StaticRing::<i64>::RING).unwrap();

    OwnedMatrix::from_fn(H.hypercube().dim_length(dim_index) * H.slot_ring().rank(), H.hypercube().dim_length(dim_index) * H.slot_ring().rank(), |row_idx, col_idx| {
        let i = row_idx / H.slot_ring().rank();
        let k = row_idx % H.slot_ring().rank();
        let j = col_idx / H.slot_ring().rank();
        let l = col_idx % H.slot_ring().rank(); 
        // the "work" that is left to do is to write `X1 e_U(*)` w.r.t. the basis `𝝵^k e_U(i)`;
        // however, this is exactly `X1 = sum_i X^(m/m1) e_U(i) = sum_i 𝝵^(shift_element(-i) * m/m1) e_U(i)`
        let exponent = Gal.underlying_ring().prod([
            Gal.to_ring_el(H.hypercube().map_1d(0, -(i as i64))), 
            ZZ_to_Gal.map(H.ring().m() as i64 / H.hypercube().factor_of_m(0).unwrap()),
            ZZ_to_Gal.map((j + l * H.hypercube().dim_length(0)) as i64)
        ]);
        return H.slot_ring().wrt_canonical_basis(&*zeta_powertable.get_power(Gal.underlying_ring().smallest_positive_lift(exponent))).at(k);
    })
}

///
/// Computes the <https://ia.cr/2014/873>-style linear transform for fat bootstrapping with composite moduli.
/// 
/// If for the linear transform input, the slot `(i_1, ..., i_r)` contains `sum_j a_(j, i_1, ..., i_r) 𝝵^j`, this
/// this transform "puts" `a_(j, i_1, ..., i_r)` into the powerful-basis coefficient of `X1^(j * l_1 + i_1) X2^i_2 ... Xr^i_r`.
/// Formally, this is the `Z/p^eZ`-linear map that maps
/// ```text
///   𝝵^j e_(i_1, ..., i_r)  ->  X1^(j * l_1 + i_1) X2^i_2 ... Xr^i_r = X^(j * l_1 * m/m_1 + i_1 * m/m_1 + i_2 * m/m_2 + ... + i_r * m/m_r)
///       for j < d, i_1 < l_1, ..., i_r < l_r
/// ```
/// Here `e_(i_1, ..., i_r)` denotes the `(i_1, ..., i_r)`-th slot unit vector.
/// 
/// This requires that the underlying hypercube structure is a Halevi-Shoup hypercube structure, and that `d l_1 = phi(m_1)`.
/// 
#[instrument(skip_all)]
pub fn slots_to_powcoeffs_fat<NumberRing>(H: &DefaultHypercube<NumberRing>) -> Vec<MatmulTransform<NumberRing>>
    where NumberRing: HECyclotomicNumberRing + Clone
{
    assert!(H.hypercube().is_tensor_product_compatible());

    assert!(H.ring().m() % 2 != 0);
    assert!(H.hypercube().is_tensor_product_compatible());

    let mut result = Vec::new();
    let zeta_powertable = PowerTable::new(H.slot_ring(), H.slot_ring().canonical_gen(), H.ring().m() as usize);

    let fst_step_matrix = slots_to_powcoeffs_fat_fst_step(H, 0, &zeta_powertable);
    result.push(MatmulTransform::blockmatmul1d(
        H,
        0,
        |(i, k), (j, l), _idxs| H.slot_ring().base_ring().clone_el(fst_step_matrix.at(i * H.slot_ring().rank() + k, j * H.slot_ring().rank() + l))
    ));

    for i in 1..H.hypercube().dim_count() {
        result.extend(dwt1d(H, i, &zeta_powertable));
    }

    return result;
}

///
/// Inverse <https://ia.cr/2014/873>-style linear transform, i.e. the inverse of [`slots_to_powcoeffs_fat()`].
/// 
/// In other words, this moves the powerful-basis coefficient of `X1^(j * l_1 + i1) X2^i_2 ... Xr^i_r`
/// to the coefficient of `𝝵^j` within the slot `(i_1, ..., i_r)`.
/// Formally, this is the `Z/p^eZ`-linear map that maps
/// ```text
///   X1^(j * l_1 + i_1) X2^i_2 ... Xr^i_r  ->  𝝵^j e_(i_1, ..., i_r)
///       for j < d, i_1 < l_1, ..., i_r < l_r
/// ```
/// Here `e_(i_1, ..., i_r)` denotes the `(i_1, ..., i_r)`-th slot unit vector.
/// 
/// This requires that the underlying hypercube structure is a Halevi-Shoup hypercube structure, and that `d l_1 = phi(m_1)`.
/// 
#[instrument(skip_all)]
pub fn powcoeffs_to_slots_fat<NumberRing>(H: &DefaultHypercube<NumberRing>) -> Vec<MatmulTransform<NumberRing>>
    where NumberRing: HECyclotomicNumberRing + Clone
{
    assert!(H.ring().m() % 2 != 0);
    assert!(H.hypercube().is_tensor_product_compatible());

    let mut result = Vec::new();
    let zeta_powertable = PowerTable::new(H.slot_ring(), H.slot_ring().canonical_gen(), H.ring().m() as usize);

    for i in (1..H.hypercube().dim_count()).rev() {
        result.extend(dwt1d_inv(H, i, &zeta_powertable));
    }

    let mut A = slots_to_powcoeffs_fat_fst_step(H, 0, &zeta_powertable);

    let mut rhs = OwnedMatrix::identity(H.hypercube().dim_length(0) * H.slot_ring().rank(), H.hypercube().dim_length(0) * H.slot_ring().rank(), H.slot_ring().base_ring());
    let mut sol = OwnedMatrix::zero(H.hypercube().dim_length(0) * H.slot_ring().rank(), H.hypercube().dim_length(0) * H.slot_ring().rank(), H.slot_ring().base_ring());
    <_ as LinSolveRingStore>::solve_right(H.slot_ring().base_ring(), A.data_mut(), rhs.data_mut(), sol.data_mut()).assert_solved();

    result.push(MatmulTransform::blockmatmul1d(
        H,
        0,
        |(i, k), (j, l), _idxs| H.slot_ring().base_ring().clone_el(sol.at(i * H.slot_ring().rank() + k, j * H.slot_ring().rank() + l))
    ));

    return result;
}

///
/// Computes the <https://ia.cr/2014/873>-style linear transform for thin bootstrapping with composite moduli.
/// 
/// If for the linear transform input, the slot `(i_1, ..., i_r)` contains a scalar `a_(i_1, ..., i_r)`, this
/// transform "puts" `a_(i_1, ..., i_r)` into the powerful-basis coefficient of `X1^i_1 ... Xr^i_r`. If the slot
/// doesn't contain a scalar, the behavior is unspecified.
/// 
#[instrument(skip_all)]
pub fn slots_to_powcoeffs_thin<NumberRing>(H: &DefaultHypercube<NumberRing>) -> Vec<MatmulTransform<NumberRing>>
    where NumberRing: HECyclotomicNumberRing + Clone
{
    assert!(H.ring().m() % 2 != 0);
    assert!(H.hypercube().is_tensor_product_compatible());

    let zeta_powertable = PowerTable::new(H.slot_ring(), H.slot_ring().canonical_gen(), H.ring().m() as usize);
    let mut result = Vec::new();

    for i in 0..H.hypercube().dim_count() {
        result.extend(dwt1d(H, i, &zeta_powertable));
    }
    return result;
}

///
/// Conceptually, this is the inverse of [`slots_to_powcoeffs_thin()`].
/// 
/// It does move the value from the powerful-basis coefficients `X1^i_1 ... Xr^i_r` for `i_1 < phi(m_1)/d` and
/// `i_2 < phi(m_2), ..., i_r < phi(m_r)` to the slot `(i_1, ..., i_r)`; However, values corresponding to other 
/// powerful-basis coefficients are discarded, i.e. mapped to zero. In particular this transform does not have
/// full rank, and cannot be the mathematical inverse of [`slots_to_powcoeffs_thin()`].
/// 
#[instrument(skip_all)]
pub fn powcoeffs_to_slots_thin<NumberRing>(H: &DefaultHypercube<NumberRing>) -> Vec<MatmulTransform<NumberRing>>
    where NumberRing: HECyclotomicNumberRing + Clone
{
    let mut result = powcoeffs_to_slots_fat(H);
    let discard_unused = MatmulTransform::blockmatmul0d(
        H, 
        |i, j, _idxs| if j == 0 && i == 0 { H.slot_ring().base_ring().one() } else { H.slot_ring().base_ring().zero() }
    );
    let last_step = result.last_mut().unwrap();
    *last_step = discard_unused.compose(last_step, H);
    return result;
}

#[cfg(test)]
use crate::ring_literal;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::number_ring::quotient::*;
#[cfg(test)]
use crate::number_ring::composite_cyclotomic::CompositeCyclotomicNumberRing;

#[test]
fn test_slots_to_powcoeffs_thin() {
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(5 * 7), 11);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);

    // first test very simple case
    let mut current = ring_literal(&ring, &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    for transform in slots_to_powcoeffs_thin(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let expected = ring.sum([0, 5, 7, 12, 14, 19, 21, 26].into_iter().map(|k| ring.pow(ring.canonical_gen(), k)));
    assert_el_eq!(ring, expected, current);

    // then test "thin bootstrapping" case
    assert_eq!(7, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(2, H.hypercube().dim_length(0));
    assert_eq!(5, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(4, H.hypercube().dim_length(1));
    let mut current = H.from_slot_values((1..9).map(|m| H.slot_ring().int_hom().map(m)));
    for transform in slots_to_powcoeffs_thin(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..2).flat_map(|i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4) as i32)))));
    assert_el_eq!(ring, expected, current);

    // F71[X]/Phi_35(X) ~ F71^24
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(71));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(5 * 7), 71);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);

    let mut current = H.from_slot_values((1..25).map(|m| H.slot_ring().int_hom().map(m)));
    for transform in slots_to_powcoeffs_thin(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..4).flat_map(|i| (0..6).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 7 + j * 5), ring_ref.int_hom().map((1 + j + i * 6) as i32)))));
    assert_el_eq!(ring, expected, current);

    // Z/8Z[X]/Phi_341 ~ GR(2, 3, 10)^30
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(11, 31), Zn::new(8));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(11 * 31), 2);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);

    let mut current = H.from_slot_values((1..=30).map(|m| H.slot_ring().int_hom().map(m)));
    for transform in slots_to_powcoeffs_thin(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let expected = ring.sum((0..30).map(|j| ring.mul(ring.pow(ring.canonical_gen(), j * 11), ring.int_hom().map((j + 1) as i32))));
    assert_el_eq!(ring, expected, current);
}

#[test]
fn test_powcoeffs_to_slots_thin() {
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(5 * 7), 11);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);
    assert_eq!(7, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(2, H.hypercube().dim_length(0));
    assert_eq!(5, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(4, H.hypercube().dim_length(1));

    let mut current = ring_literal(&ring, &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    for transform in powcoeffs_to_slots_thin(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let expected = H.from_slot_values([H.slot_ring().one()].into_iter().chain((2..9).map(|_| H.slot_ring().zero())));
    assert_el_eq!(ring, expected, current);
    
    let ring_ref = &ring;
    let mut current = ring.sum((0..6).flat_map(|i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4) as i32)))));
    for transform in powcoeffs_to_slots_thin(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let expected = H.from_slot_values([1, 2, 3, 4, 5, 6, 7, 8].into_iter().map(|i| H.slot_ring().int_hom().map(i)));
    assert_el_eq!(ring, expected, current);

    // F71[X]/Phi_35(X) ~ F71^24
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(71));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(5 * 7), 71);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);

    let ring_ref = &ring;
    let mut current = ring.sum((0..4).flat_map(|i| (0..6).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 7 + j * 5), ring_ref.int_hom().map((1 + j + i * 6) as i32)))));
    for transform in powcoeffs_to_slots_thin(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let expected = H.from_slot_values((1..25).map(|i| H.slot_ring().int_hom().map(i)));
    assert_el_eq!(ring, expected, current);
}

#[test]
fn test_slots_to_powcoeffs_fat() {
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(5 * 7), 11);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);

    // first test very simple case
    let mut current = ring_literal(&ring, &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    for transform in slots_to_powcoeffs_fat(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let expected = ring.sum([0, 5, 7, 12, 14, 19, 21, 26].into_iter().map(|k| ring.pow(ring.canonical_gen(), k)));
    assert_el_eq!(ring, expected, current);

    // then test "thin bootstrapping" case
    assert_eq!(7, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(2, H.hypercube().dim_length(0));
    assert_eq!(5, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(4, H.hypercube().dim_length(1));
    let mut current = H.from_slot_values((1..9).map(|i| H.slot_ring().int_hom().map(i)));
    for transform in slots_to_powcoeffs_fat(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..2).flat_map(|i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4) as i32)))));
    assert_el_eq!(ring, expected, current);

    // then test "fat bootstrapping" case
    let hom = H.slot_ring().base_ring().int_hom();
    let mut current = H.from_slot_values((1..9).map(|i| H.slot_ring().from_canonical_basis([hom.map(i), hom.map(i + 100), hom.map(i + 200)])));
    for transform in slots_to_powcoeffs_fat(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..3).flat_map(|k| (0..2).flat_map(move |i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), (i + k * 2) * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4 + k * 100) as i32))))));

    assert_el_eq!(ring, expected, current);

    // F71[X]/Phi_35(X) ~ F71^24
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(71));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(5 * 7), 71);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);
    assert_eq!(5, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(4, H.hypercube().dim_length(0));
    assert_eq!(7, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(6, H.hypercube().dim_length(1));

    let mut current = H.from_slot_values((1..25).map(|i| H.slot_ring().int_hom().map(i)));
    for transform in slots_to_powcoeffs_fat(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..4).flat_map(|i| (0..6).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 7 + j * 5), ring_ref.int_hom().map((1 + j + i * 6) as i32)))));
    assert_el_eq!(ring, expected, current);
}

#[test]
fn test_powcoeffs_to_slots_fat() {
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(5 * 7), 11);
    let H = HypercubeIsomorphism::new::<false>(&ring, hypercube);
    assert_eq!(7, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(2, H.hypercube().dim_length(0));
    assert_eq!(5, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(4, H.hypercube().dim_length(1));

    let ring_ref = &ring;
    let mut current = ring.sum((0..6).flat_map(|i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4) as i32)))));
    for transform in powcoeffs_to_slots_fat(&H) {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }
    let expected = H.from_slot_values([1, 2, 3, 4, 5, 6, 7, 8].into_iter().map(|i| H.slot_ring().from_canonical_basis([i, i + 8, i + 16].into_iter().map(|i| H.slot_ring().base_ring().int_hom().map(i)))));
    assert_el_eq!(ring, expected, current);
}

#[test]
#[ignore]
fn test_powcoeffs_to_slots_fat_large() {
    // let allocator = feanor_mempool::AllocRc(Rc::new(feanor_mempool::dynsize::DynLayoutMempool::<Global>::new(Alignment::of::<u64>())));
    let ring = RingValue::from(NumberRingQuotientBase::new(CompositeCyclotomicNumberRing::new(337, 127), Zn::new(65536)).into());
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(337 * 127), 2);
    let H = HypercubeIsomorphism::new::<true>(&ring, hypercube);
    assert_eq!(337, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(16, H.hypercube().dim_length(0));
    assert_eq!(127, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(126, H.hypercube().dim_length(1));

    let transform = powcoeffs_to_slots_fat(&H);

    let ring_ref = &ring;
    let mut current = ring.pow(ring_ref.canonical_gen(), 7 * 127 + 2 * 337);
    for transform in &transform {
        current = ring.get_ring().compute_linear_transform(&H, &current, &transform);
    }

    let expected = H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[0] == 7 && idxs[1] == 2 {
        H.slot_ring().one()
    } else {
        H.slot_ring().zero()
    }));

    assert_el_eq!(ring, expected, current);
}