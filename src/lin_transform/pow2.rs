use feanor_math::algorithms::unity_root::is_prim_root_of_unity;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::group::*;
use feanor_math::rings::extension::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::rings::zn::*;
use feanor_math::assert_el_eq;
use feanor_math::seq::VectorView;
use tracing::instrument;

use crate::circuit::PlaintextCircuit;
use crate::lin_transform::matmul::*;
use crate::lin_transform::trace::trace_circuit;
use crate::number_ring::hypercube::structure::*;
use crate::lin_transform::PowerTable;
use crate::number_ring::galois::*;
use crate::number_ring::hypercube::isomorphism::*;
use crate::number_ring::*;
use crate::NiceZn;
use crate::ZZi64;

fn assert_hypercube_supported(H: &HypercubeStructure) {
    assert!(H.galois_group().is_full_cyclotomic_galois_group());
    let log2_m = ZZi64.abs_log2_ceil(&(H.galois_group().m() as i64)).unwrap();
    assert_eq!(H.galois_group().m(), 1 << log2_m);
}

///
/// Works separately on each block of size `l = blocksize` along the given given hypercube dimension.
/// This function computes the length-`l` DWT
/// ```text
///   sum_(0 <= i < l) a_i * 𝝵_(4l)^(i * g^j)
/// ``` 
/// from the length-`l/2` DWTs of the even-index resp. odd-index entries of `a_i`. These two sub-DWTs are expected to be written
/// in the first resp. second half of the input block (i.e. not interleaved, this is where the "bitreversed" comes from).
/// Here `g` is the generator of the current hypercube dimension, i.e. usually `g = 5`.
/// 
/// More concretely, it is expected that the input to the linear transform is
/// ```text
///   b_j = sum_(0 <= i < l/2) a_(2i) * 𝝵_(4l)^(2 * i * g^j)              if j < l/2
///   b_j = sum_(0 <= i < l/2) a_(2i + 1) * 𝝵_(4l)^(2 * i * g^j)
///       = sum_(0 <= i < l/2) a_(2i + 1) * 𝝵_(4l)^(2 * i * g^(j - l/2))  otherwise
/// ```
/// In this case, the output is
/// ```text
///   b_j = sum_(0 <= i < l) a_i * 𝝵_(4l)^(i * g^j)
/// ```
/// 
/// # Notes
///  - This does not compute the evaluation at all primitive `4l`-th roots of unity, but only at half of them - namely `𝝵_(4l)^(g^j)` for all `j`.
///    In particular, `g` does not generate `(Z/4lZ)*`, but `<g>` is an index 2 subgroup of it.
///  - `row_autos` can be given to use different `𝝵`s for each block; in particular, for the block with hypercube indices `idxs`, the DWT with root
///    of unity `𝝵 = root_of_unity_4l^row_autos(idxs)` is used. Note that the index passed to `row_autos` is the hypercube index of some element in the
///    block. It does not make sense for `row_autos` to behave differently on different indices in the same block, this will lead to 
///    `pow2_bitreversed_dwt_butterfly` give nonsensical results. If you pass `row_autos = |_| H.cyclotomic_index_ring().one()` then this uses the same
///    roots of unity everywhere, i.e. results in the behavior as outlined above.
/// 
fn pow2_bitreversed_dwt_butterfly<G, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, l: usize, root_of_unity_4l: El<SlotRingOf<R>>, row_autos: G) -> MatmulTransform<R::Type>
    where G: Fn(&[usize]) -> GaloisGroupEl,
        R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let dim_len = H.hypercube().dim_length(dim_index);
    let log2_len = ZZi64.abs_log2_ceil(&(dim_len as i64)).unwrap();
    assert_eq!(dim_len, 1 << log2_len);

    let g = H.hypercube().map_1d(dim_index, -1);
    let smaller_cyclotomic_index_ring = Zn::new(4 * l as u64);
    let Gal = H.galois_group().parent();
    let Zm = Gal.underlying_ring();
    let red = ZnReductionMap::new(Zm, &smaller_cyclotomic_index_ring).unwrap();
    assert_el_eq!(&smaller_cyclotomic_index_ring, &smaller_cyclotomic_index_ring.one(), &smaller_cyclotomic_index_ring.pow(red.map(*Gal.as_ring_el(&g)), l));

    let l = l;
    assert!(l > 1);
    assert!(dim_len % l == 0);
    let zeta_power_table = PowerTable::new(H.slot_ring(), root_of_unity_4l, 4 * l);

    enum TwiddleFactor {
        Zero, PosPowerZeta(ZnEl), NegPowerZeta(ZnEl)
    }

    let pow_of_zeta = |factor: TwiddleFactor| match factor {
        TwiddleFactor::PosPowerZeta(pow) => H.slot_ring().clone_el(&zeta_power_table.get_power(Gal.underlying_ring().smallest_positive_lift(pow))),
        TwiddleFactor::NegPowerZeta(pow) => H.slot_ring().negate(H.slot_ring().clone_el(&zeta_power_table.get_power(Gal.underlying_ring().smallest_positive_lift(pow)))),
        TwiddleFactor::Zero => H.slot_ring().zero()
    };

    let forward_mask = H.from_slot_values(H.hypercube().hypercube_iter(|idxs| {
        let idx_in_block = idxs[dim_index] % l;
        if idx_in_block >= l / 2 {
            TwiddleFactor::PosPowerZeta(Gal.underlying_ring().zero())
        } else {
            TwiddleFactor::Zero
        }
    }).map(&pow_of_zeta));

    let diagonal_mask = H.from_slot_values(H.hypercube().hypercube_iter(|idxs| {
        let idx_in_block = idxs[dim_index] % l;
        if idx_in_block >= l / 2 {
            TwiddleFactor::NegPowerZeta(Zm.mul(Zm.pow(*Gal.as_ring_el(&g), idx_in_block - l / 2), *Gal.as_ring_el(&row_autos(&idxs))))
        } else {
            TwiddleFactor::PosPowerZeta(Gal.underlying_ring().zero())
        }
    }).map(&pow_of_zeta));

    let backward_mask = H.from_slot_values(H.hypercube().hypercube_iter(|idxs| {
        let idx_in_block = idxs[dim_index] % l;
        if idx_in_block < l / 2 {
            TwiddleFactor::PosPowerZeta(Zm.mul(Zm.pow(*Gal.as_ring_el(&g), idx_in_block), *Gal.as_ring_el(&row_autos(&idxs))))
        } else {
            TwiddleFactor::Zero
        }
    }).map(&pow_of_zeta));

    let result = MatmulTransform::linear_combine_shifts(H, [
        (
            (0..H.hypercube().dim_count()).map(|_| 0).collect::<Vec<_>>(),
            diagonal_mask
        ),
        (
            (0..H.hypercube().dim_count()).map(|i| if i == dim_index { l as i64 / 2 } else { 0 }).collect::<Vec<_>>(),
            forward_mask
        ),
        (
            (0..H.hypercube().dim_count()).map(|i| if i == dim_index { -(l as i64) / 2 } else { 0 }).collect::<Vec<_>>(),
            backward_mask
        )
    ].iter().map(|(shift, coeff)| (shift.copy_els(), H.ring().clone_el(coeff))));
    return result;
}

///
/// Inverse of [`pow2_bitreversed_dwt_butterfly()`]
/// 
fn pow2_bitreversed_inv_dwt_butterfly<G, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, l: usize, root_of_unity_4l: El<SlotRingOf<R>>, row_autos: G) -> MatmulTransform<R::Type>
    where G: Fn(&[usize]) -> GaloisGroupEl,
        R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let dim_len = H.hypercube().dim_length(dim_index);
    let log2_len = ZZi64.abs_log2_ceil(&(dim_len as i64)).unwrap();
    assert_eq!(dim_len, 1 << log2_len);

    let g = H.hypercube().map_1d(dim_index, -1);
    let smaller_cyclotomic_index_ring = Zn::new(4 * l as u64);
    let Gal = H.galois_group().parent();
    let Zm = Gal.underlying_ring();
    let red = ZnReductionMap::new(Gal.underlying_ring(), &smaller_cyclotomic_index_ring).unwrap();
    assert_el_eq!(&smaller_cyclotomic_index_ring, &smaller_cyclotomic_index_ring.one(), &smaller_cyclotomic_index_ring.pow(red.map(*Gal.as_ring_el(&g)), l));

    let l = l;
    assert!(l > 1);
    assert!(dim_len % l == 0);
    let zeta_power_table = PowerTable::new(H.slot_ring(), root_of_unity_4l, 4 * l);

    enum TwiddleFactor {
        Zero, PosPowerZeta(ZnEl), NegPowerZeta(ZnEl)
    }

    let pow_of_zeta = |factor: TwiddleFactor| match factor {
        TwiddleFactor::PosPowerZeta(pow) => H.slot_ring().clone_el(&zeta_power_table.get_power(Gal.underlying_ring().smallest_positive_lift(pow))),
        TwiddleFactor::NegPowerZeta(pow) => H.slot_ring().negate(H.slot_ring().clone_el(&zeta_power_table.get_power(Gal.underlying_ring().smallest_positive_lift(pow)))),
        TwiddleFactor::Zero => H.slot_ring().zero()
    };

    let inv_2 = H.ring().base_ring().invert(&H.ring().base_ring().int_hom().map(2)).unwrap();

    let mut forward_mask = H.from_slot_values(H.hypercube().hypercube_iter(|idxs| {
        let idx_in_block = idxs[dim_index] % l;
        if idx_in_block >= l / 2 {
            TwiddleFactor::PosPowerZeta(Zm.mul(Zm.negate(Zm.pow(*Gal.as_ring_el(&g), idx_in_block - l / 2)), *Gal.as_ring_el(&row_autos(&idxs))))
        } else {
            TwiddleFactor::Zero
        }
    }).map(&pow_of_zeta));
    H.ring().inclusion().mul_assign_ref_map(&mut forward_mask, &inv_2);

    let mut diagonal_mask = H.from_slot_values(H.hypercube().hypercube_iter(|idxs| {
        let idx_in_block = idxs[dim_index] % l;
        if idx_in_block >= l / 2 {
            TwiddleFactor::NegPowerZeta(Zm.mul(Zm.negate(Zm.pow(*Gal.as_ring_el(&g), idx_in_block - l / 2)), *Gal.as_ring_el(&row_autos(&idxs))))
        } else {
            TwiddleFactor::PosPowerZeta(Gal.underlying_ring().zero())
        }
    }).map(&pow_of_zeta));
    H.ring().inclusion().mul_assign_ref_map(&mut diagonal_mask, &inv_2);

    let mut backward_mask = H.from_slot_values(H.hypercube().hypercube_iter(|idxs| {
        let idx_in_block = idxs[dim_index] % l;
        if idx_in_block < l / 2 {
            TwiddleFactor::PosPowerZeta(Gal.underlying_ring().zero())
        } else {
            TwiddleFactor::Zero
        }
    }).map(&pow_of_zeta));
    H.ring().inclusion().mul_assign_ref_map(&mut backward_mask, &inv_2);

    let result = MatmulTransform::linear_combine_shifts(H, [
        (
            (0..H.hypercube().dim_count()).map(|_| 0).collect::<Vec<_>>(),
            diagonal_mask
        ),
        (
            (0..H.hypercube().dim_count()).map(|i| if i == dim_index { l as i64 / 2 } else { 0 }).collect::<Vec<_>>(),
            forward_mask
        ),
        (
            (0..H.hypercube().dim_count()).map(|i| if i == dim_index { -(l as i64) / 2 } else { 0 }).collect::<Vec<_>>(),
            backward_mask
        )
    ].iter().map(|(shift, coeff)| (shift.copy_els(), H.ring().clone_el(coeff))));
    #[cfg(debug_assertions)] {
        let expected = pow2_bitreversed_dwt_butterfly(H, dim_index, l, H.slot_ring().clone_el(&zeta_power_table.get_power(1)), row_autos).inverse(&H);
        debug_assert!(result.eq(H.ring(), H.hypercube(), &expected));
    }
    return result;
}

///
/// Computes the evaluation of `f(X) = a_0 + a_1 X + a_2 X^2 + ... + a_(l_i - 1) X^(l_i - 1)` at the
/// `4 l_i`-primitive roots of unity corresponding to the subgroup `<g_i>` of `(Z/2mZ)*`.
/// Here `l_i` is the hypercube length of the given dimension and `g_i` is the generator of the hypercube
/// dimension.
/// 
/// More concretely, this computes
/// ```text
///   sum_(0 <= i < l_i) a(bitrev(i)) * 𝝵^(m / (4 l_i) * row_autos(idxs) * g^j)
/// ```
/// for `j` from `0` to `l_i`.
/// Here `𝝵` is the canonical generator of the slot ring, which is a primitive `m`-th root of unity.
/// 
fn pow2_bitreversed_dwt<G, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, row_autos: G) -> Vec<MatmulTransform<R::Type>>
    where G: Fn(&[usize]) -> GaloisGroupEl,
        R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let dim_len = H.hypercube().dim_length(dim_index);
    let log2_len = ZZi64.abs_log2_ceil(&(dim_len as i64)).unwrap();
    assert_eq!(dim_len, 1 << log2_len);
    assert!((H.galois_group().m() as usize / dim_len) % 4 == 0, "pow2_bitreversed_dwt() only possible if there is a 4l-th primitive root of unity");

    let zeta = H.slot_ring().pow(H.slot_ring().canonical_gen(), H.galois_group().m() as usize / dim_len / 4);

    debug_assert!(is_prim_root_of_unity(H.slot_ring(), &H.slot_ring().canonical_gen(), H.galois_group().m() as usize));
    debug_assert!(is_prim_root_of_unity(H.slot_ring(), &zeta, 4 * dim_len));

    let mut result = Vec::new();
    for log2_l in 1..=log2_len {
        result.push(pow2_bitreversed_dwt_butterfly(
            H, 
            dim_index, 
            1 << log2_l, 
            H.slot_ring().pow(H.slot_ring().clone_el(&zeta), dim_len / (1 << log2_l)), 
            &row_autos
        ));
    }

    return result;
}

///
/// Inverse to [`pow2_bitreversed_dwt()`]
/// 
#[instrument(skip_all)]
fn pow2_bitreversed_inv_dwt<G, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, row_autos: G) -> Vec<MatmulTransform<R::Type>>
    where G: Fn(&[usize]) -> GaloisGroupEl,
        R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let dim_len = H.hypercube().dim_length(dim_index);
    let log2_len = ZZi64.abs_log2_ceil(&(dim_len as i64)).unwrap();
    assert_eq!(dim_len, 1 << log2_len);
    assert!((H.galois_group().m() as usize / dim_len) % 4 == 0, "pow2_bitreversed_dwt() only possible if there is a 4l-th primitive root of unity");

    let zeta = H.slot_ring().pow(H.slot_ring().canonical_gen(), H.galois_group().m() as usize / dim_len / 4);
    debug_assert!(is_prim_root_of_unity(H.slot_ring(), &H.slot_ring().canonical_gen(), H.galois_group().m() as usize));
    debug_assert!(is_prim_root_of_unity(H.slot_ring(), &zeta, 4 * dim_len));

    let mut result = Vec::new();
    for log2_l in (1..=log2_len).rev() {
        result.push(pow2_bitreversed_inv_dwt_butterfly(
            H, 
            dim_index, 
            1 << log2_l, 
            H.slot_ring().pow(H.slot_ring().clone_el(&zeta), dim_len / (1 << log2_l)), 
            &row_autos
        ));
    }

    return result;
}

///
/// Computes the <https://ia.cr/2024/153>-style Slots-to-Coeffs linear transform for the thin-bootstrapping case,
/// i.e. where all slots contain elements in `Z/pZ`.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l/2` and `j in {0, 1}`. If `p = 1 mod 4`.
/// Then the returned linear transform will then put the value of slot `(i, 0)` into the coefficient of `X^(bitrev(i, l/2) * m/(2l))`
/// and the value of slot `(i, 1)` into the coefficient of `X^(bitrev(i, l/2) * m/(2l) + m/4)`.
/// 
/// If `p = 3 mod 4`, the slots are enumerated by `i` with `0 <= i < l` and the transform will put the value of slot `i` 
/// into the coefficient of `X^(bitrev(i, l) * m/(4l))`
/// 
#[instrument(skip_all)]
pub fn slots_to_coeffs_thin<R>(H: &HypercubeIsomorphism<R>) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), slots_to_coeffs_thin_impl(H))
}

#[instrument(skip_all)]
fn slots_to_coeffs_thin_impl<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let m = H.galois_group().m();
    let log2_m = ZZi64.abs_log2_ceil(&(m as i64)).unwrap();
    assert!(m == 1 << log2_m);

    if H.hypercube().dim_count() == 2 {
        // this is the `p = 1 mod 4` case
        assert_eq!(2, H.hypercube().dim_length(1));
        let zeta4 = H.slot_ring().pow(H.slot_ring().canonical_gen(), H.galois_group().m() as usize / 4);
        let mut result = Vec::new();

        // we first combine `a_(i_0)` and `a_(i_1)` to `(a_(i_0) + 𝝵^(m/4) a_(i_1), a_(i_0) - 𝝵^(m/4) a_(i_1))`
        result.push(MatmulTransform::linear_combine_shifts(H, [
            (
                (0..H.hypercube().dim_count()).map(|_| 0).collect::<Vec<_>>(),
                H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[1] == 0 {
                    H.slot_ring().one()
                } else {
                    debug_assert!(idxs[1] == 1);
                    H.slot_ring().negate(H.slot_ring().clone_el(&zeta4))
                }))
            ),
            (
                (0..H.hypercube().dim_count()).map(|i| if i == 1 { 1 } else { 0 }).collect::<Vec<_>>(),
                H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[1] == 0 {
                    H.slot_ring().clone_el(&zeta4)
                } else {
                    debug_assert!(idxs[1] == 1);
                    H.slot_ring().one()
                }))
            )
        ].iter().map(|(shift, coeff)| (shift.copy_els(), H.ring().clone_el(coeff)))));

        // then map the `a_(i_0) + 𝝵^(m/4) a_(i_1)` to `sum_i (a_(i_0) + 𝝵^(m/4) a_(i_1)) 𝝵^(m/(2l) i g^k)` for each slot `(k, 0)`, and similarly
        // for the slots `(*, 1)`. The negation in the second hypercolumn comes from the fact that `-𝝵^(m/4) = 𝝵^(-m/4)`
        result.extend(pow2_bitreversed_dwt(H, 0, |idxs| if idxs[1] == 0 {
            H.galois_group().identity()
        } else {
            debug_assert!(idxs[1] == 1);
            H.galois_group().from_representative(-1)
        }));
        
        return result;
    } else {
        // this is the `p = 3 mod 4` case
        assert_eq!(1, H.hypercube().dim_count());
        return pow2_bitreversed_dwt(H, 0, |_idxs| H.galois_group().identity());
    }
}

///
/// This is the inverse to [`slots_to_coeffs_thin()`]. Note that it is not the
/// "Coeffs-to-Slots" map, as it does not discard unused factors. However, it is not
/// too hard to build the "coeffs-to-slots" map from this, see [`coeffs_to_slots_thin()`]. 
/// 
fn slots_to_coeffs_thin_inv<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let m = H.galois_group().m();
    let log2_m = ZZi64.abs_log2_ceil(&(m as i64)).unwrap();
    assert!(m == 1 << log2_m);

    if H.hypercube().dim_count() == 2 {
        assert_eq!(2, H.hypercube().dim_length(1));
        let zeta4_inv = H.slot_ring().pow(H.slot_ring().canonical_gen(), 3 * H.galois_group().m() as usize / 4);
        let two_inv = H.ring().base_ring().invert(&H.slot_ring().base_ring().int_hom().map(2)).unwrap();
        let mut result = Vec::new();

        result.extend(pow2_bitreversed_inv_dwt(H, 0, |idxs| if idxs[1] == 0 {
            H.galois_group().identity()
        } else {
            debug_assert!(idxs[1] == 1);
            H.galois_group().from_representative(-1)
        }));

        result.push(MatmulTransform::linear_combine_shifts(H, [
            (
                (0..H.hypercube().dim_count()).map(|_| 0).collect::<Vec<_>>(),
                H.ring().inclusion().mul_map(H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[1] == 0 {
                    H.slot_ring().one()
                } else {
                    debug_assert!(idxs[1] == 1);
                    H.slot_ring().negate(H.slot_ring().clone_el(&zeta4_inv))
                })), H.ring().base_ring().clone_el(&two_inv))
            ),
            (
                (0..H.hypercube().dim_count()).map(|i| if i == 1 { 1 } else { 0 }).collect::<Vec<_>>(),
                H.ring().inclusion().mul_map(H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[1] == 0 {
                    H.slot_ring().one()
                } else {
                    debug_assert!(idxs[1] == 1);
                    H.slot_ring().clone_el(&zeta4_inv)
                })), two_inv)
            )
        ].iter().map(|(shift, coeff)| (shift.copy_els(), H.ring().clone_el(coeff)))));

        return result;
    } else {
        assert_eq!(1, H.hypercube().dim_count());
        return pow2_bitreversed_inv_dwt(H, 0, |_idxs| H.galois_group().identity());
    }
}

///
/// Computes the <https://ia.cr/2024/153>-style Coeffs-to-Slots linear transform for the thin-bootstrapping case,
/// i.e. where all slots contain elements in `Z/pZ`.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l/2` and `j in {0, 1}`. If `p = 1 mod 4`.
/// Then the returned linear transform will put the value of the coefficient of `X^(i * m/(2l))` into slot `(bitrev(i, l/2), 0)` 
/// and the value the coefficient of `X^(i * m/(2l) + m/4)` into slot `(bitrev(i, l/2), 1)`.
/// 
/// If `p = 3 mod 4`, the slots are enumerated by `i` with `0 <= i < l` and the transform will put the value of the coefficient
/// of `X^(i * m/(4l))` into slot `bitrev(i, l)`.
/// 
/// Note that the values of all other coefficients are discarded, hence this transform is not the inverse of [`slots_to_coeffs_thin()`].
/// However, `coeff_to_slots_thin()(slots_to_coeffs_thin()(x))` does give `x` for all thinly-packed plaintexts `x`, i.e. `x` where
/// each slot only contains an element in `Z/pZ`. 
/// 
#[instrument(skip_all)]
pub fn coeffs_to_slots_thin<R>(H: &HypercubeIsomorphism<R>) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let mut result = slots_to_coeffs_thin_inv(H);
    let last = MatmulTransform::mult_scalar_slots(H, &H.slot_ring().inclusion().map(H.slot_ring().base_ring().invert(&H.slot_ring().base_ring().int_hom().map(H.slot_ring().rank() as i32)).unwrap()));
    *result.last_mut().unwrap() = result.last().unwrap().compose(H.ring(), H.hypercube(), &last);

    let frobenius_subgroup = H.galois_group().parent().get_group().clone().subgroup([H.hypercube().frobenius(1)]);
    debug_assert_eq!(frobenius_subgroup.group_order(), H.slot_ring().rank());
    let trace_circuit = trace_circuit(H.ring(), &frobenius_subgroup);
    let result_circuit = MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), result);
    return trace_circuit.compose(result_circuit, H.ring());
}

#[cfg(test)]
use crate::ring_literal;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use feanor_math::algorithms::fft::cooley_tuckey::bitreverse;
#[cfg(test)]
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
#[cfg(test)]
use crate::ZZbig;

#[test]
fn test_slots_to_coeffs_thin() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    
    let mut current = H.from_slot_values((1..17).map(|i| H.slot_ring().int_hom().map(i)));
    for T in slots_to_coeffs_thin_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 32];
    for i in 0..8 {
        for j in 0..2 {
            expected[bitreverse(i, 3) * 2 + j * 16] = (i * 2 + j + 1) as i32;
        }
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);

    // `F23[X]/(X^32 + 1) ~ F_(23^8)^4`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(23));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(23, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);

    let mut current = H.from_slot_values([1, 2, 3, 4].into_iter().map(|i| H.slot_ring().int_hom().map(i)));
    for T in slots_to_coeffs_thin_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 32];
    for i in 0..4 {
        expected[bitreverse(i, 2) * 4] = (i + 1) as i32;
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);
}

#[test]
fn test_slots_to_coeffs_thin_inv() {
    // `F23[X]/(X^32 + 1) ~ F_(23^8)^4`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(23));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(23, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);

    for (transform, actual) in slots_to_coeffs_thin_impl(&H).into_iter().rev().zip(slots_to_coeffs_thin_inv(&H).into_iter()) {
        let expected = transform.inverse(&H);
        assert!(expected.eq(H.ring(), H.hypercube(), &actual));
    }
    
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    
    for (transform, actual) in slots_to_coeffs_thin_impl(&H).into_iter().rev().zip(slots_to_coeffs_thin_inv(&H).into_iter()) {
        let expected = transform.inverse(&H);
        assert!(expected.eq(H.ring(), H.hypercube(), &actual));
    }
}

#[test]
fn test_coeffs_to_slots_thin() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    
    let mut input = [0; 32];
    for i in 0..8 {
        for j in 0..2 {
            input[bitreverse(i, 3) * 2 + j * 16] = (i * 2 + j + 1) as i32;
            input[bitreverse(i, 3) * 2 + j * 16 + 1] = (i * 2 + j + 1 + 16) as i32;
        }
    }
    let current = ring_literal(&ring, &input);
    let circuit = coeffs_to_slots_thin(&H);
    let actual = circuit.evaluate(std::slice::from_ref(&current), ring.identity()).pop().unwrap();
    let expected = H.from_slot_values((1..17).map(|i| H.slot_ring().int_hom().map(i)));
    assert_el_eq!(&ring, &expected, &actual);

    // `F23[X]/(X^32 + 1) ~ F_(23^8)^4`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(23));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(23, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);

    let mut input = [0; 32];
    input[4] = 1;
    input[16] = 1;

    let current = ring_literal(&ring, &input);
    let circuit = coeffs_to_slots_thin(&H);
    let actual = circuit.evaluate(std::slice::from_ref(&current), ring.identity()).pop().unwrap();
    let expected = H.from_slot_values([0, 0, 1, 0].into_iter().map(|i| H.slot_ring().int_hom().map(i)));
    assert_el_eq!(&ring, &expected, &actual);

    let mut input = [0; 32];
    for i in 0..4 {
        input[bitreverse(i, 2) * 4] = (i + 1) as i32;
        for k in 1..4 {
            input[bitreverse(i, 2) * 4 + k] = (i + 1 + 4 * k) as i32;
        }
        for k in 0..4 {
            input[bitreverse(i, 2) * 4 + k + 16] = (i + 1 + 4 * k + 16) as i32;
        }
    }
    let current = ring_literal(&ring, &input);
    let circuit = coeffs_to_slots_thin(&H);
    let actual = circuit.evaluate(std::slice::from_ref(&current), ring.identity()).pop().unwrap();
    let expected = H.from_slot_values([1, 2, 3, 4].into_iter().map(|i| H.slot_ring().int_hom().map(i)));
    assert_el_eq!(&ring, &expected, &actual);
}
