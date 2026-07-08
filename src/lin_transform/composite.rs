
use feanor_math::algorithms::linsolve::LinSolveRingStore;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::group::AbelianGroupStore;
use feanor_math::homomorphism::*;
use feanor_math::matrix::OwnedMatrix;
use feanor_math::ring::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::primitive_int::*;
use feanor_math::seq::VectorFn;
use tracing::instrument;

use crate::circuit::CircuitEvaluatorCosts;
use crate::circuit::PlaintextCircuit;
use crate::lin_transform::trace::trace_circuit;
use crate::number_ring::galois::*;
use crate::number_ring::hypercube::structure::HypercubeStructure;
use crate::number_ring::hypercube::isomorphism::*;
use crate::number_ring::*;
use crate::lin_transform::matmul::*;
use crate::lin_transform::*;

use crate::NiceZn;

fn assert_hypercube_supported(H: &HypercubeStructure) {
    assert!(H.galois_group().m() % 2 == 1);
    assert!(H.galois_group().is_full_cyclotomic_galois_group());
    assert!(H.is_tensor_product_compatible());
}

#[instrument(skip_all)]
fn dwt1d_matrix<R>(H: &HypercubeStructure, slot_ring: &SlotRingOver<R>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOver<R>>) -> OwnedMatrix<El<SlotRingOver<R>>>
    where R: RingStore,
        R::Type: NiceZn
{
    assert_hypercube_supported(H);

    let Gal = H.galois_group();
    let ZZ_to_Zn = Gal.underlying_ring().can_hom(&StaticRing::<i64>::RING).unwrap();

    OwnedMatrix::from_fn(H.dim_length(dim_index), H.dim_length(dim_index), |i, j| {
        let exponent = Gal.underlying_ring().prod([
            *Gal.as_ring_el(&H.map_1d(dim_index, -(i as i64))),
            ZZ_to_Zn.map(j as i64),
            ZZ_to_Zn.map(H.galois_group().m() as i64 / H.factor_of_m(dim_index).unwrap())
        ]);
        return slot_ring.clone_el(&*zeta_powertable.get_power(Gal.underlying_ring().smallest_lift(exponent)));
    })
}

#[instrument(skip_all)]
fn dwt1d_inv_matrix<R>(H: &HypercubeStructure, slot_ring: &SlotRingOver<R>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOver<R>>) -> OwnedMatrix<El<SlotRingOver<R>>>
    where R: RingStore,
        R::Type: NiceZn
{
    assert_hypercube_supported(H);
    
    let mut A = dwt1d_matrix(H, slot_ring, dim_index, zeta_powertable);
    let mut rhs = OwnedMatrix::identity(H.dim_length(dim_index), H.dim_length(dim_index), slot_ring);
    let mut sol = OwnedMatrix::zero(H.dim_length(dim_index), H.dim_length(dim_index), slot_ring);
    <_ as LinSolveRingStore>::solve_right(slot_ring, A.data_mut(), rhs.data_mut(), sol.data_mut()).assert_solved();
    return sol;
}

///
/// Interprets each hypercolumn along the `i = dim_index`-th dimension as a vector of 
/// length `l_i`, and computes the discrete weighted transform along this vector, 
/// i.e. the evaluation at the primitive roots of unity `𝝵^(m/m_i * j)` for `j` coprime
/// to `m_i`. This assumes that `l_i = phi(m_i)`, i.e. the hypercube dimension is good.
/// 
#[instrument(skip_all)]
fn dwt1d<'a, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOf<R>>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

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
fn dwt1d_inv<'a, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOf<R>>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    if H.hypercube().dim_length(dim_index) == 1{
        Vec::new()
    } else {
        let A = dwt1d_inv_matrix(H.hypercube(), H.slot_ring(), dim_index, zeta_powertable);

        // multiplication with the matrix `A(i, j) = 𝝵^(j * shift_element(-i))` if we consider an element as multiple vectors along the `dim_index`-th dimension
        vec![MatmulTransform::matmul1d(
            H, 
            dim_index, 
            |i, j, _idxs| H.slot_ring().clone_el(A.at(i, j))
        )]
    }
}

/// 
/// Computes the first step in the <https://ia.cr/2014/873>-style Slots-to-PowCoeffs
/// transform for fat bootstrapping with composite moduli.
/// 
/// In this step, for each hypercolumn along the first hypercube dimension, the coefficients of each slot of
/// (w.r.t. the power-of-`𝝵` basis of each slot) are moved to the coefficients of a `d l_1 = phi(m_1)` degree
/// polynomial, stored "along" the hypercolumn.
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
fn slots_to_powcoeffs_fat_fst_step<R>(H: &HypercubeIsomorphism<R>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOf<R>>) -> OwnedMatrix<El<<R::Type as RingExtension>::BaseRing>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());
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
            *Gal.as_ring_el(&H.hypercube().map_1d(0, -(i as i64))), 
            ZZ_to_Gal.map(H.galois_group().m() as i64 / H.hypercube().factor_of_m(0).unwrap()),
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
pub fn slots_to_powcoeffs_fat<R>(H: &HypercubeIsomorphism<R>, max_levels: usize, cost_model: &CircuitEvaluatorCosts) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), slots_to_powcoeffs_fat_impl(H), max_levels, cost_model)
}

fn slots_to_powcoeffs_fat_impl<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let mut result = Vec::new();
    let zeta_powertable = PowerTable::new(H.slot_ring(), H.slot_ring().canonical_gen(), H.galois_group().m() as usize);

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
pub fn powcoeffs_to_slots_fat<R>(H: &HypercubeIsomorphism<R>, max_levels: usize, cost_model: &CircuitEvaluatorCosts) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), powcoeffs_to_slots_fat_impl(H), max_levels, cost_model)
}

fn powcoeffs_to_slots_fat_impl<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let mut result = Vec::new();
    let zeta_powertable = PowerTable::new(H.slot_ring(), H.slot_ring().canonical_gen(), H.galois_group().m() as usize);

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
pub fn slots_to_powcoeffs_thin<R>(H: &HypercubeIsomorphism<R>, max_levels: usize, cost_model: &CircuitEvaluatorCosts) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), slots_to_powcoeffs_thin_impl(H), max_levels, cost_model)
}

fn slots_to_powcoeffs_thin_impl<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let zeta_powertable = PowerTable::new(H.slot_ring(), H.slot_ring().canonical_gen(), H.galois_group().m() as usize);
    let mut result = Vec::new();

    for i in 0..H.hypercube().dim_count() {
        result.extend(dwt1d(H, i, &zeta_powertable));
    }
    return result;
}

/// 
/// Computes the last step in the <https://ia.cr/2014/873>-style PowCoeffs-to-Slots
/// transform for thin bootstrapping with composite moduli.
/// 
/// In general, we could use the inverse of [`slots_to_powcoeffs_fat_fst_step()`], and
/// then extract the constant coefficient of every slot. However, since we are in the thin
/// case, we can do better.
/// 
/// The map that we want to compute is
/// ```text
///   (\sum_(i = 0)^(p - 2) a_i 𝝵_p^(ig_k))_k -> (a_k)_k
/// ```
/// where `0 <= k < (p - 1)/f`.
/// 
/// We can implement this map by first performing a matmul with the matrix `C = (c_(kj))`,
/// `c_(kj) = (𝝵_p^(-kg^j) - 𝝵_p^(g^j))/p`, and then take the slotwise trace. This avoids the
/// blockmatmul that would be required when inverting [`slots_to_powcoeffs_fat_fst_step()`].
/// 
#[instrument(skip_all)]
fn powcoeffs_to_slots_thin_last_step<R>(H: &HypercubeIsomorphism<R>, dim_index: usize, zeta_powertable: &PowerTable<&SlotRingOf<R>>) -> OwnedMatrix<El<SlotRingOf<R>>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());
    assert_eq!(0, dim_index);

    let Gal = H.galois_group();
    let ZZ_to_Zn = Gal.underlying_ring().can_hom(&StaticRing::<i64>::RING).unwrap();
    let slot_ring = H.slot_ring();
    let scale = slot_ring.base_ring().invert(&slot_ring.base_ring().coerce(&StaticRing::<i64>::RING, H.hypercube().factor_of_m(dim_index).unwrap())).unwrap();

    OwnedMatrix::from_fn(H.hypercube().dim_length(dim_index), H.hypercube().dim_length(dim_index), |k, j| {
        let exponent1 = Gal.underlying_ring().prod([
            *Gal.as_ring_el(&H.hypercube().map_1d(dim_index, -(j as i64))),
            ZZ_to_Zn.map(-(k as i64)),
            ZZ_to_Zn.map(H.galois_group().m() as i64 / H.hypercube().factor_of_m(dim_index).unwrap())
        ]);
        let exponent2 = Gal.underlying_ring().prod([
            *Gal.as_ring_el(&H.hypercube().map_1d(dim_index, -(j as i64))),
            ZZ_to_Zn.map(H.galois_group().m() as i64 / H.hypercube().factor_of_m(dim_index).unwrap())
        ]);
        return slot_ring.inclusion().mul_ref_map(&slot_ring.sub_ref(
            &*zeta_powertable.get_power(Gal.underlying_ring().smallest_lift(exponent1)),
            &*zeta_powertable.get_power(Gal.underlying_ring().smallest_lift(exponent2))
        ), &scale);
    })
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
pub fn powcoeffs_to_slots_thin<R>(H: &HypercubeIsomorphism<R>, max_levels: usize, cost_model: &CircuitEvaluatorCosts) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let frobenius_subgroup = H.galois_group().parent().get_group().clone().subgroup([H.hypercube().frobenius(1)]);
    debug_assert_eq!(frobenius_subgroup.group_order(), H.slot_ring().rank());
    let trace_circuit = trace_circuit(H.ring(), &frobenius_subgroup);
    trace_circuit.compose(MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), powcoeffs_to_slots_thin_base(H), max_levels, cost_model), H.ring())
}

///
/// The PowCoeffs-to-Slots transform for thin bootstrapping, without the final trace.
/// 
fn powcoeffs_to_slots_thin_base<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let mut result = Vec::new();
    let zeta_powertable = PowerTable::new(H.slot_ring(), H.slot_ring().canonical_gen(), H.galois_group().m() as usize);

    for i in (1..H.hypercube().dim_count()).rev() {
        result.extend(dwt1d_inv(H, i, &zeta_powertable));
    }

    let last_step_matrix = powcoeffs_to_slots_thin_last_step(H, 0, &zeta_powertable);
    result.push(MatmulTransform::matmul1d(
        H,
        0,
        |i, j, _| H.slot_ring().clone_el(last_step_matrix.at(i, j))
    ));

    return result;
}

#[cfg(test)]
use crate::ring_literal;
#[cfg(test)]
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::integer::*;
#[cfg(test)]
use crate::number_ring::tensor_ring::TensorProductNumberRing;
#[cfg(test)]
use crate::{ZZi64, ZZbig};
#[cfg(test)]
use crate::circuit::DEFAULT_EVALUATOR_COSTS;

#[test]
fn test_slots_to_powcoeffs_thin() {
    feanor_tracing::DelayedLogger::init_test();
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(11, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &hypercube, None);

    // first test very simple case
    let mut current = ring_literal(&ring, &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    for transform in slots_to_powcoeffs_thin_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let expected = ring.sum([0, 5, 7, 12, 14, 19, 21, 26].into_iter().map(|k| ring.pow(ring.canonical_gen(), k)));
    assert_el_eq!(ring, expected, current);

    // then test "thin bootstrapping" case
    assert_eq!(7, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(2, H.hypercube().dim_length(0));
    assert_eq!(5, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(4, H.hypercube().dim_length(1));
    let mut current = H.from_slot_values((1..9).map(|m| H.slot_ring().int_hom().map(m)));
    for transform in slots_to_powcoeffs_thin_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..2).flat_map(|i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4) as i32)))));
    assert_el_eq!(ring, expected, current);

    // F71[X]/Phi_35(X) ~ F71^24
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(71));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(71, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &hypercube, None);

    let mut current = H.from_slot_values((1..25).map(|m| H.slot_ring().int_hom().map(m)));
    for transform in slots_to_powcoeffs_thin_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..4).flat_map(|i| (0..6).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 7 + j * 5), ring_ref.int_hom().map((1 + j + i * 6) as i32)))));
    assert_el_eq!(ring, expected, current);

    // Z/8Z[X]/Phi_341 ~ GR(2, 3, 10)^30
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(11, 31), Zn::new(8));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(2, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &hypercube, None);

    let mut current = H.from_slot_values((1..=30).map(|m| H.slot_ring().int_hom().map(m)));
    for transform in slots_to_powcoeffs_thin_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let expected = ring.sum((0..30).map(|j| ring.mul(ring.pow(ring.canonical_gen(), j * 11), ring.int_hom().map((j + 1) as i32))));
    assert_el_eq!(ring, expected, current);
}

#[test]
fn test_powcoeffs_to_slots_thin() {
    feanor_tracing::DelayedLogger::init_test();
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(11, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &hypercube, None);
    let trace = MatmulTransform::linear_combine_shifts_with_frobenius(&H, (0..H.slot_ring().rank()).map(|i| (vec![i as i64, 0, 0], H.ring().one())));
    assert_eq!(7, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(2, H.hypercube().dim_length(0));
    assert_eq!(5, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(4, H.hypercube().dim_length(1));

    let mut current = ring_literal(&ring, &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    for transform in powcoeffs_to_slots_thin_base(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &trace);
    let expected = H.from_slot_values([H.slot_ring().one()].into_iter().chain((2..9).map(|_| H.slot_ring().zero())));
    assert_el_eq!(ring, expected, current);
    
    let ring_ref = &ring;
    let mut current = ring.sum((0..6).flat_map(|i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4) as i32)))));
    for transform in powcoeffs_to_slots_thin_base(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &trace);
    let expected = H.from_slot_values([1, 2, 3, 4, 5, 6, 7, 8].into_iter().map(|i| H.slot_ring().int_hom().map(i)));
    assert_el_eq!(ring, expected, current);

    // F71[X]/Phi_35(X) ~ F71^24
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(71));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(71, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &hypercube, None);
    let trace = MatmulTransform::linear_combine_shifts_with_frobenius(&H, (0..H.slot_ring().rank()).map(|i| (vec![i as i64, 0, 0], H.ring().one())));

    let ring_ref = &ring;
    let mut current = ring.sum((0..4).flat_map(|i| (0..6).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 7 + j * 5), ring_ref.int_hom().map((1 + j + i * 6) as i32)))));
    for transform in powcoeffs_to_slots_thin_base(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &trace);
    let expected = H.from_slot_values((1..25).map(|i| H.slot_ring().int_hom().map(i)));
    assert_el_eq!(ring, expected, current);
}

#[test]
fn test_slots_to_powcoeffs_fat() {
    feanor_tracing::DelayedLogger::init_test();
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(11, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &hypercube, None);

    // first test very simple case
    let mut current = ring_literal(&ring, &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    for transform in slots_to_powcoeffs_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let expected = ring.sum([0, 5, 7, 12, 14, 19, 21, 26].into_iter().map(|k| ring.pow(ring.canonical_gen(), k)));
    assert_el_eq!(ring, expected, current);

    // then test "thin bootstrapping" case
    assert_eq!(7, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(2, H.hypercube().dim_length(0));
    assert_eq!(5, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(4, H.hypercube().dim_length(1));
    let mut current = H.from_slot_values((1..9).map(|i| H.slot_ring().int_hom().map(i)));
    for transform in slots_to_powcoeffs_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..2).flat_map(|i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4) as i32)))));
    assert_el_eq!(ring, expected, current);

    // then test "fat bootstrapping" case
    let hom = H.slot_ring().base_ring().int_hom();
    let mut current = H.from_slot_values((1..9).map(|i| H.slot_ring().from_canonical_basis([hom.map(i), hom.map(i + 100), hom.map(i + 200)])));
    for transform in slots_to_powcoeffs_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..3).flat_map(|k| (0..2).flat_map(move |i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), (i + k * 2) * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4 + k * 100) as i32))))));

    assert_el_eq!(ring, expected, current);

    // F71[X]/Phi_35(X) ~ F71^24
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(71));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(71, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &hypercube, None);
    assert_eq!(5, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(4, H.hypercube().dim_length(0));
    assert_eq!(7, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(6, H.hypercube().dim_length(1));

    let mut current = H.from_slot_values((1..25).map(|i| H.slot_ring().int_hom().map(i)));
    for transform in slots_to_powcoeffs_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let ring_ref = &ring;
    let expected = ring.sum((0..4).flat_map(|i| (0..6).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 7 + j * 5), ring_ref.int_hom().map((1 + j + i * 6) as i32)))));
    assert_el_eq!(ring, expected, current);
}

#[test]
fn test_powcoeffs_to_slots_fat() {
    feanor_tracing::DelayedLogger::init_test();
    // F11[X]/Phi_35(X) ~ F_(11^3)^8
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(11));
    let hypercube = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(11, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &hypercube, None);
    assert_eq!(7, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(2, H.hypercube().dim_length(0));
    assert_eq!(5, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(4, H.hypercube().dim_length(1));

    let ring_ref = &ring;
    let mut current = ring.sum((0..6).flat_map(|i| (0..4).map(move |j| ring_ref.mul(ring_ref.pow(ring_ref.canonical_gen(), i * 5 + j * 7), ring_ref.int_hom().map((1 + j + i * 4) as i32)))));
    for transform in powcoeffs_to_slots_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }
    let expected = H.from_slot_values([1, 2, 3, 4, 5, 6, 7, 8].into_iter().map(|i| H.slot_ring().from_canonical_basis([i, i + 8, i + 16].into_iter().map(|i| H.slot_ring().base_ring().int_hom().map(i)))));
    assert_el_eq!(ring, expected, current);
}

#[test]
#[ignore]
fn test_powcoeffs_to_slots_thin_large() {
    feanor_tracing::DelayedLogger::init_test();
    let ring = RingValue::from(NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(337, 127), Zn::new(65536)).into());
    let h = HypercubeStructure::halevi_shoup_hypercube(ring.acting_galois_group(), int_cast(2, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new(&ring, &h, Some("./cache"));
    assert_eq!(337, H.hypercube().factor_of_m(0).unwrap());
    assert_eq!(16, H.hypercube().dim_length(0));
    assert_eq!(127, H.hypercube().factor_of_m(1).unwrap());
    assert_eq!(126, H.hypercube().dim_length(1));

    let transform = powcoeffs_to_slots_thin_base(&H);

    println!("{}", transform.len());
    println!("{}", transform.last().unwrap().automorphism_count());
    let circuit = transform.last().unwrap().clone(&ring).to_circuit(&ring, &h, &DEFAULT_EVALUATOR_COSTS);
    println!("{}", circuit.galois_gate_output_sum());

    let ring_ref = &ring;
    let mut current = ring.pow(ring_ref.canonical_gen(), 7 * 127 + 2 * 337);
    for transform in &transform {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &transform);
    }

    let expected = H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[0] == 7 && idxs[1] == 2 {
        H.slot_ring().one()
    } else {
        H.slot_ring().zero()
    }));

    assert_el_eq!(ring, expected, current);
}