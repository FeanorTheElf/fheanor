use feanor_math::assert_el_eq;
use feanor_math::divisibility::DivisibilityRing;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::group::*;
use feanor_math::rings::extension::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::rings::zn::*;
use feanor_math::seq::VectorFn;
use feanor_math::seq::VectorView;
use tracing::instrument;

use crate::circuit::Coefficient;
use crate::circuit::PlaintextCircuit;
use crate::lin_transform::matmul::*;
use crate::lin_transform::trace::trace_circuit;
use crate::number_ring::hypercube::structure::*;
use crate::number_ring::galois::*;
use crate::number_ring::hypercube::isomorphism::*;
use crate::number_ring::*;
use crate::*;

fn assert_hypercube_supported(H: &HypercubeStructure) {
    assert!(H.dim_count() == 1 || (H.dim_count() == 2 && H.dim_length(1) == 2));
    let log2_m = ZZi64.abs_log2_ceil(&(H.galois_group().m() as i64)).unwrap();
    assert_eq!(H.galois_group().m(), 1 << log2_m);
}

///
/// Works separately on each block of size `l = blocksize` along the given given hypercube dimension.
/// This function computes the length-`l` DWT
/// ```text
///   sum_(0 <= i < l) a_i * 𝝵^(i * g^j)
/// ``` 
/// from the length-`l/2` DWTs of the even-index resp. odd-index entries of `a_i`. 
/// Here `𝝵` should be an `m'`-th root of unity, such that `g mod m'` has order `l`
/// as element of `(Z/m'Z)*`. In particular, if we have a power of two cyclotomic
/// conductor, `𝝵` should be `𝝵_m^( l m / ord(g) )` where `ord(g)` is the order
/// of `g` in `(Z/mZ)*`.
/// 
/// The two sub-DWTs are expected to be written in the first resp. second half of
/// the input block (i.e. not interleaved, this is where the "bitreversed" comes from).
/// Here `g` is the generator of the current hypercube dimension, i.e. usually `g = 5`.
/// 
/// More concretely, it is expected that the input to the linear transform is
/// ```text
///   b_j = sum_(0 <= i < l/2) a_(2i) * 𝝵^(2 * i * g^j)              if j < l/2
///   b_j = sum_(0 <= i < l/2) a_(2i + 1) * 𝝵^(2 * i * g^j)
///       = sum_(0 <= i < l/2) a_(2i + 1) * 𝝵^(2 * i * g^(j - l/2))  otherwise
/// ```
/// In this case, the output is
/// ```text
///   b_j = sum_(0 <= i < l) a_i * 𝝵_^(i * g^j)
/// ```
/// 
/// # Notes
///  - `row_autos` can be given to use different `𝝵`s for each block; in particular, for the
///    block with hypercube indices `idxs`, the DWT with root of unity `𝝵 = root_of_unity^row_autos(idxs)` 
///    is used. Note that the index passed to `row_autos` is the hypercube index of some element in the
///    block. It does not make sense for `row_autos` to behave differently on different indices in the 
///    same block, this will lead to `pow2_bitreversed_dwt_butterfly` give nonsensical results. If you pass
///    `row_autos = |_| H.galois_group().one()` then this uses the same roots of unity everywhere, i.e. 
///    results in the behavior as outlined above.
/// 
fn pow2_bitreversed_dwt_butterfly<G, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, l: usize, root_of_unity: El<SlotRingOf<R>>, row_autos: G) -> MatmulTransform<R::Type>
    where G: Fn(&[usize]) -> GaloisGroupEl,
        R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let dim_len = H.hypercube().dim_length(dim_index);
    let log2_len = ZZi64.abs_log2_ceil(&(dim_len as i64)).unwrap();
    assert_eq!(dim_len, 1 << log2_len);

    assert!(l >= 2);
    assert!(l % 2 == 0);
    assert!(dim_len % l == 0);

    let g = H.hypercube().map_1d(dim_index, -1);
    let Gal = H.galois_group().parent();
    let Zm = Gal.underlying_ring();
    assert!(H.slot_ring().eq_el(&root_of_unity, &H.slot_ring().negate(H.slot_ring().pow(H.slot_ring().clone_el(&root_of_unity), Zm.smallest_positive_lift(Zm.pow(*Gal.as_ring_el(&g), l / 2)) as usize))));

    enum TwiddleFactor {
        Zero, PosPowerZeta(ZnEl), NegPowerZeta(ZnEl)
    }

    let pow_of_zeta = |factor: TwiddleFactor| match factor {
        TwiddleFactor::PosPowerZeta(pow) => H.slot_ring().pow(H.slot_ring().clone_el(&root_of_unity), Zm.smallest_positive_lift(pow) as usize),
        TwiddleFactor::NegPowerZeta(pow) => H.slot_ring().negate(H.slot_ring().pow(H.slot_ring().clone_el(&root_of_unity), Zm.smallest_positive_lift(pow) as usize)),
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
fn pow2_bitreversed_inv_dwt_butterfly<G, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, l: usize, root_of_unity: El<SlotRingOf<R>>, row_autos: G) -> MatmulTransform<R::Type>
    where G: Fn(&[usize]) -> GaloisGroupEl,
        R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let dim_len = H.hypercube().dim_length(dim_index);
    let log2_len = ZZi64.abs_log2_ceil(&(dim_len as i64)).unwrap();
    assert_eq!(dim_len, 1 << log2_len);

    assert!(l >= 2);
    assert!(l % 2 == 0);
    assert!(dim_len % l == 0);

    let g = H.hypercube().map_1d(dim_index, -1);
    let Gal = H.galois_group().parent();
    let Zm = Gal.underlying_ring();
    assert_el_eq!(H.slot_ring(), &root_of_unity, &H.slot_ring().negate(H.slot_ring().pow(H.slot_ring().clone_el(&root_of_unity), Zm.smallest_positive_lift(Zm.pow(*Gal.as_ring_el(&g), l / 2)) as usize)));

    enum TwiddleFactor {
        Zero, PosPowerZeta(ZnEl), NegPowerZeta(ZnEl)
    }

    let pow_of_zeta = |factor: TwiddleFactor| match factor {
        TwiddleFactor::PosPowerZeta(pow) => H.slot_ring().pow(H.slot_ring().clone_el(&root_of_unity), Zm.smallest_positive_lift(pow) as usize),
        TwiddleFactor::NegPowerZeta(pow) => H.slot_ring().negate(H.slot_ring().pow(H.slot_ring().clone_el(&root_of_unity), Zm.smallest_positive_lift(pow) as usize)),
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

    return result;
}

///
/// Computes the evaluation of `f(X) = a_0 + a_1 X + a_2 X^2 + ... + a_(l - 1) X^(l - 1)` at the
/// `4 l`-primitive roots of unity corresponding to the subgroup `<g>` of `(Z/mZ)*/<p>`.
/// Here `l` is the hypercube length of the given dimension and `g` is the generator 
/// of the hypercube dimension.
/// 
/// More concretely, this computes
/// ```text
///   sum_(0 <= i < l) a(bitrev(i)) * 𝝵^(i * row_autos(idxs) * g^j)
/// ```
/// for `j` from `0` to `l - 1`. The operation is `F_(p^d)`-linear.
/// 
#[instrument(skip_all)]
fn pow2_bitreversed_dwt<G, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, row_autos: G) -> Vec<MatmulTransform<R::Type>>
    where G: Fn(&[usize]) -> GaloisGroupEl,
        R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let dim_len = H.hypercube().dim_length(dim_index);
    let log2_len = ZZi64.abs_log2_ceil(&(dim_len as i64)).unwrap();
    assert_eq!(dim_len, 1 << log2_len);

    let zeta = H.slot_ring().pow(H.slot_ring().canonical_gen(), H.hypercube().ord_generator(dim_index) / dim_len);

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
/// Inverse to [`pow2_bitreversed_dwt()`].
/// 
#[instrument(skip_all)]
fn pow2_bitreversed_inv_dwt<G, R>(H: &HypercubeIsomorphism<R>, dim_index: usize, row_autos: G) -> Vec<MatmulTransform<R::Type>>
    where G: Fn(&[usize]) -> GaloisGroupEl,
        R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    assert_hypercube_supported(H.hypercube());

    let dim_len = H.hypercube().dim_length(dim_index);
    let log2_len = ZZi64.abs_log2_ceil(&(dim_len as i64)).unwrap();
    assert_eq!(dim_len, 1 << log2_len);

    let zeta = H.slot_ring().pow(H.slot_ring().canonical_gen(), H.hypercube().ord_generator(dim_index) / dim_len);

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
/// Computes the <https://ia.cr/2024/153>-style Slots-to-Coeffs linear transform for the thin bootstrapping case,
/// i.e. where all slots contain elements in `Z/pZ`.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l` and `j in {0, 1}`.
/// Then the returned linear transform will then put the value of slot `(i, 0)` into the coefficient of
/// `X^(bitrev(i, l) * m/(4l))` and the value of slot `(i, 1)` into the coefficient of `X^(bitrev(i, l) * m/(4l) + m/4)`.
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
    MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), slots_to_coeffs_base(H))
}

#[instrument(skip_all)]
fn slots_to_coeffs_base<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
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
        let root_of_unity = H.slot_ring().pow(H.slot_ring().canonical_gen(), H.hypercube().ord_generator(0));
        let root_of_unity_inv = H.slot_ring().invert(&root_of_unity).unwrap();
        let mut result = Vec::new();

        // we first combine `a_(i0)` and `a_(i1)` to `(a_(i0) + 𝝵^(m/4) a_(i1), a_(i0) - 𝝵^(m/4) a_(i1))`
        result.push(MatmulTransform::linear_combine_shifts(H, [
            (
                (0..H.hypercube().dim_count()).map(|_| 0).collect::<Vec<_>>(),
                H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[1] == 0 {
                    H.slot_ring().one()
                } else {
                    debug_assert!(idxs[1] == 1);
                    H.slot_ring().clone_el(&root_of_unity_inv)
                }))
            ),
            (
                (0..H.hypercube().dim_count()).map(|i| if i == 1 { 1 } else { 0 }).collect::<Vec<_>>(),
                H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[1] == 0 {
                    H.slot_ring().clone_el(&root_of_unity)
                } else {
                    debug_assert!(idxs[1] == 1);
                    H.slot_ring().one()
                }))
            )
        ].iter().map(|(shift, coeff)| (shift.copy_els(), H.ring().clone_el(coeff)))));

        // then map the `a_(i0) + 𝝵^(m/4) a_(i1)` to `sum_i (a_(i0) + 𝝵^(m/4) a_(i1)) 𝝵^(i g^k)` 
        // for each slot `(k, 0)`, and similarly for the slots `(*, 1)`. The negation in the second 
        // hypercolumn comes from the fact that `-𝝵^(m/4) = 𝝵^(-m/4)`
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
/// Computes the <https://ia.cr/2024/153>-style Slots-to-Coeffs linear transform for the fat bootstrapping case.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l` and `j in {0, 1}`. 
/// Then the returned linear transform will then put the coefficient of `𝝵^k` in slot `(i, 0)` into the
/// coefficient of `X^(bitrev(i, l) * m/(4l) + k)` and the coefficient of `𝝵^k` in slot `(i, 1)` into the
/// coefficient of `X^(bitrev(i, l) * m/(4l) + m/4 + k)`.
/// 
/// If `p = 3 mod 4`, the slots are enumerated by `i` with `0 <= i < l` and the transform will put the coefficient
/// of `𝝵^k` in slot `i` into the coefficient of `X^(bitrev(i, l) * m/(4l) + k)` if `k < d/2` and into the coefficient
/// of `X^(bitrev(i, l) * m/(4l) + m/4 + k - d/2)` if `k >= d/2`.
/// 
#[instrument(skip_all)]
pub fn slots_to_coeffs_fat<R>(H: &HypercubeIsomorphism<R>) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), slots_to_coeffs_fat_impl(H))
}

///
/// Computes the <https://ia.cr/2024/153>-style Slots-to-Coeffs linear transform with packing
/// for the fat bootstrapping case. Thus, the resulting circuit will have `d` inputs and one output.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l` and `j in {0, 1}`. 
/// Then the returned linear transform will then put the slot `(i, 0)` of the `bitrev(k, d)`-th input into
/// the coefficient coefficient of `X^(bitrev(i, l) * m/(4l) + k)` and slot `(i, 1)` of the `bitrev(k, d)`-th
/// input into the coefficient of `X^(bitrev(i, l) * m/(4l) + m/4 + k)`.
/// 
/// If `p = 3 mod 4`, the slots are enumerated by `i` with `0 <= i < l` and the transform will put 
/// slot `i` of the `bitrev(k, d)`-th input into the coefficient of `X^(bitrev(i, l) * m/(4l) + k)` and
/// slot `i` of the `bitrev(k + d/2, d)`-th into the coefficient of `X^(bitrev(i, l) * m/(4l) + m/4 + k)`,
/// where `0 <= k < d/2`.
/// 
#[instrument(skip_all)]
pub fn slots_to_coeffs_fat_pack<R>(H: &HypercubeIsomorphism<R>) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let ring = H.ring();
    let S = H.slot_ring();
    let Gal = H.galois_group();
    let d= S.rank();
    let log2_d = ZZi64.abs_log2_ceil(&(d as i64)).unwrap();
    let m = Gal.m() as usize;

    let mut result = PlaintextCircuit::identity(d, ring);
    
    if H.hypercube().dim_count() == 2 {
        // this is the `p = 1 mod 4` case
        assert_eq!(2, H.hypercube().dim_length(1));
        result = PlaintextCircuit::linear_transform(&[Coefficient::One, Coefficient::Other(ring.pow(ring.canonical_gen(), d/2))], ring).tensor_pow(d/2, ring).compose(result, ring);
    } else {
        // this is the `p = 3 mod 4` case
        assert_eq!(1, H.hypercube().dim_count());
        result = PlaintextCircuit::linear_transform(&[Coefficient::One, Coefficient::Other(ring.pow(ring.canonical_gen(), m/4))], ring).tensor_pow(d/2, ring).compose(result, ring);
    }

    for i in 2..=log2_d {
        result = PlaintextCircuit::linear_transform(&[Coefficient::One, Coefficient::Other(ring.pow(ring.canonical_gen(), d >> i))], ring).tensor_pow(d >> i, ring).compose(result, ring);
    }

    result = MatmulTransform::to_circuit_many(ring, H.hypercube(), slots_to_coeffs_fat_Xbasis(H)).compose(result, ring);

    return result;
}

///
/// Basically the slots-to-coeffs map, but without initial transform from powers of `𝝵` within
/// each slot to projections of `X`.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l` and `j in {0, 1}`. 
/// Then the returned linear transform will then put the coefficient of `𝝵^(k g^i)` in slot `(i, 0)` into the
/// coefficient of `X^(bitrev(i, l) * m/(4l) + k)` and the coefficient of `𝝵^(-k g^i)` in slot `(i, 1)` into the
/// coefficient of `X^(bitrev(i, l) * m/(4l) + m/4 + k)`.
/// 
/// If `p = 3 mod 4`, the slots are enumerated by `i` with `0 <= i < l` and the transform will put the coefficient
/// of `𝝵^(k g^i)` in slot `i` into the coefficient of `X^(bitrev(i, l) * m/(4l) + k)` and the coefficient of `𝝵^(k g^i + m/4)`
/// into the coefficient of `X^(bitrev(i, l) * m/(4l) + m/4 + k)` for `0 <= k < d/2`.
/// 
#[instrument(skip_all)]
fn slots_to_coeffs_fat_Xbasis<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let S = H.slot_ring();
    let Gal = H.galois_group();
    let d= S.rank();
    let m = Gal.m() as usize;
    let mut result = Vec::new();

    if H.hypercube().dim_count() == 2 {
        // this is the `p = 1 mod 4` case
        assert_eq!(2, H.hypercube().dim_length(1));
        let initial_transform = MatmulTransform::blockmatmul0d_inv(H, |i, j, idxs| 
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), j * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(i)
        );

        result.push(initial_transform);
        result.extend(slots_to_coeffs_fat_impl(H));
    } else {
        // this is the `p = 3 mod 4` case
        assert_eq!(1, H.hypercube().dim_count());
        let initial_transform = MatmulTransform::blockmatmul0d_inv(H, |i, j, idxs| if j < d/2 {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), j * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(i)
        } else {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), m/4 + (j - d/2) * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(i)
        });

        result.extend(slots_to_coeffs_fat_impl(H));
        take_mut::take(&mut result[0], |first| first.compose(H.ring(), H.hypercube(), &initial_transform));
    }
    return result;
}

///
/// Basically the slots-to-coeffs map, but without initial transform from powers of `𝝵` within
/// each slot to projections of `X`.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l` and `j in {0, 1}`. 
/// Then the returned linear transform will then put the coefficient of `𝝵^k` in slot `(i, 0)` into the
/// coefficient of `X^(bitrev(i, l) * m/(4l) + k)` and the coefficient of `𝝵^k` in slot `(i, 1)` into the
/// coefficient of `X^(bitrev(i, l) * m/(4l) + m/4 + k)`.
/// 
/// If `p = 3 mod 4`, the slots are enumerated by `i` with `0 <= i < l` and the transform will put the coefficient
/// of `𝝵^k` in slot `i` into the coefficient of `X^(bitrev(i, l) * m/(4l) + k)` if `k < d/2` and into the coefficient
/// of `X^(bitrev(i, l) * m/(4l) + m/4 + k - d/2)` if `k >= d/2`.
/// 
#[instrument(skip_all)]
fn slots_to_coeffs_fat_impl<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let m = H.galois_group().m();
    let log2_m = ZZi64.abs_log2_ceil(&(m as i64)).unwrap();
    assert!(m == 1 << log2_m);
    let S = H.slot_ring();
    let Gal = H.galois_group();
    let d = S.rank();

    let mut result = Vec::new();

    if H.hypercube().dim_count() == 2 {
        // this is the `p = 1 mod 4` case
        assert_eq!(2, H.hypercube().dim_length(1));

        result.extend(slots_to_coeffs_base(H));
        // in this case, we have `𝝵_4l = 𝝵_m^d` in `Fp`; thus, the transform
        // `𝝵^j -> 𝝵^(j g^i)` for `0 <= j < d` acts trivially on the coefficients
        // of the previous dwt

        result.push(MatmulTransform::blockmatmul0d(H, |row, col, idxs| 
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), col * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(row)
        ));
    } else {
        // this is the `p = 3 mod 4` case
        assert_eq!(1, H.hypercube().dim_count());

        result.push(MatmulTransform::blockmatmul0d(H, |row, col, _idxs| if col < d/2 {
           if row == col { S.base_ring().one() } else { S.base_ring().zero() }
        } else {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), col - d/2 + m as usize/4)).at(row)
        }));

        result.extend(slots_to_coeffs_base(H));

        // in this case, we need a transform that acts trivially on `Fp[𝝵_m^(d/2)]`
        result.push(MatmulTransform::blockmatmul0d(H, |row, col, idxs| if col < d/2 {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), col * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(row)
        } else {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), d/2 + (col - d/2) * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(row)
        }));
    }

    return result;
}

///
/// This is the inverse to [`slots_to_coeffs_base()`]. Note that it is not the
/// "Coeffs-to-Slots" map, as it does not discard unused factors. However, it is not
/// too hard to build the "coeffs-to-slots" map from this, see [`coeffs_to_slots_thin()`]. 
/// 
fn slots_to_coeffs_base_inv<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let m = H.galois_group().m();
    let log2_m = ZZi64.abs_log2_ceil(&(m as i64)).unwrap();
    assert!(m == 1 << log2_m);

    if H.hypercube().dim_count() == 2 {
        assert_eq!(2, H.hypercube().dim_length(1));
        let root_of_unity = H.slot_ring().pow(H.slot_ring().canonical_gen(), H.hypercube().ord_generator(0));
        let root_of_unity_inv = H.slot_ring().invert(&root_of_unity).unwrap();
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
                    H.slot_ring().clone_el(&root_of_unity)
                })), H.ring().base_ring().clone_el(&two_inv))
            ),
            (
                (0..H.hypercube().dim_count()).map(|i| if i == 1 { 1 } else { 0 }).collect::<Vec<_>>(),
                H.ring().inclusion().mul_map(H.from_slot_values(H.hypercube().hypercube_iter(|idxs| if idxs[1] == 0 {
                    H.slot_ring().one()
                } else {
                    debug_assert!(idxs[1] == 1);
                    H.slot_ring().clone_el(&root_of_unity_inv)
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
    let mut result = slots_to_coeffs_base_inv(H);
    let last = MatmulTransform::mult_scalar_slots(H, &H.slot_ring().inclusion().map(H.slot_ring().base_ring().invert(&H.slot_ring().base_ring().int_hom().map(H.slot_ring().rank() as i32)).unwrap()));
    *result.last_mut().unwrap() = result.last().unwrap().compose(H.ring(), H.hypercube(), &last);

    let frobenius_subgroup = H.galois_group().parent().get_group().clone().subgroup([H.hypercube().frobenius(1)]);
    debug_assert_eq!(frobenius_subgroup.group_order(), H.slot_ring().rank());
    let trace_circuit = trace_circuit(H.ring(), &frobenius_subgroup);
    let result_circuit = MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), result);
    return trace_circuit.compose(result_circuit, H.ring());
}

///
/// Computes the <https://ia.cr/2024/153>-style Coeffs-to-Slots linear transform for the fat bootstrapping case.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l` and `j in {0, 1}`. 
/// Then the returned linear transform will then put the coefficient of `X^(bitrev(i, l) * m/(4l) + k)` into the
/// coefficient of `𝝵^k` in slot `(i, 0)` and the coefficient of `X^(bitrev(i, l) * m/(4l) + m/4 + k)` into to
/// coefficient of `𝝵^k` of slot `(i, 1)`.
/// 
/// If `p = 3 mod 4`, the slots are enumerated by `i` with `0 <= i < l` and the transform will put the coefficient
/// of `X^(bitrev(i, l) * m/(4l) + k + m/4 * l)` into the coefficient of `𝝵^(k + d/2 * l)` in slot `i`, where 
/// `0 <= k < d/2` and `l in {0, 1}`.
/// 
#[instrument(skip_all)]
pub fn coeffs_to_slots_fat<R>(H: &HypercubeIsomorphism<R>) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), coeffs_to_slots_fat_impl(H))
}

///
/// Computes the <https://ia.cr/2024/153>-style Coeffs-to-Slots linear transform with unpacking
/// for the fat bootstrapping case. Thus, the resulting circuit will have one input and `d` outputs,
/// each of them packing coeffficients from the input in its slots.
/// 
/// In the case `p = 1 mod 4`, the slots are enumerated by `i, j` with `0 <= i < l` and `j in {0, 1}`. 
/// Then the returned linear transform will then put the coefficient of `X^(bitrev(i, l) * m/(4l) + k)`
/// into the slot `(i, 0)` of the `bitrev(k, d)`-th output, and the coefficient of
/// `X^(bitrev(i, l) * m/(4l) + m/4 + k)` into slot `(i, 1)` of the `bitrev(k, d)`-th output.
/// 
/// If `p = 3 mod 4`, the slots are enumerated by `i` with `0 <= i < l` and the transform will put the
/// coefficient of `X^(bitrev(i, l) * m/(4l) + k)` into slot `i` of the `bitrev(k, d)`-th output and
/// the coefficient of `X^(bitrev(i, l) * m/(4l) + m/4 + k)` into slot `i` of the `bitrev(k + d/2, d)`-th
/// output, where `0 <= k < d/2`.
/// 
#[instrument(skip_all)]
pub fn coeffs_to_slots_fat_unpack<R>(H: &HypercubeIsomorphism<R>) -> PlaintextCircuit<R::Type>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient + DivisibilityRing,
        BaseRing<R>: NiceZn
{
    let m: usize = H.galois_group().m() as usize;
    let log2_m = ZZi64.abs_log2_ceil(&(m as i64)).unwrap();
    assert!(m == 1 << log2_m);
    
    let ring = H.ring();
    let S = H.slot_ring();
    let Gal = H.galois_group();
    let d= S.rank();
    let log2_d = ZZi64.abs_log2_ceil(&(d as i64)).unwrap();

    let mut base_transform = coeffs_to_slots_fat_Xbasis(H);
    take_mut::take(base_transform.last_mut().unwrap(), |transform| transform.compose(ring, H.hypercube(), &MatmulTransform::mult_ring_element(ring, H.hypercube(), 
        &ring.inclusion().map(ring.base_ring().invert(&ring.base_ring().int_hom().map(d as i32)).unwrap())
    )));
    let mut result = MatmulTransform::to_circuit_many(H.ring(), H.hypercube(), base_transform);

    for i in (1..log2_d).rev() {
        let coeff = H.ring().pow(H.ring().canonical_gen(), m - (1 << (log2_d - i - 1)));
        result = PlaintextCircuit::add(ring).tensor(PlaintextCircuit::linear_transform_ring(&[coeff], ring).compose(PlaintextCircuit::sub(ring), ring), ring).tensor_pow(1 << (log2_d - i - 1), ring)
            .compose(
                PlaintextCircuit::identity(1, ring).tensor(PlaintextCircuit::gal(H.hypercube().frobenius(1 << i), Gal, ring), ring)
                    .compose(PlaintextCircuit::identity(1, ring).output_twice(ring), ring).output_twice(ring)
                    .tensor_pow(1 << (log2_d - i - 1), ring),
                ring
            ).compose(result, ring);
    }

    if H.hypercube().dim_count() == 2 {
        // this is the `p = 1 mod 4` case
        assert_eq!(2, H.hypercube().dim_length(1));

        let coeff = H.ring().pow(H.ring().canonical_gen(), m - (1 << (log2_d - 1)));
        result = PlaintextCircuit::add(ring).tensor(PlaintextCircuit::linear_transform_ring(&[coeff], ring).compose(PlaintextCircuit::sub(ring), ring), ring).tensor_pow(1 << (log2_d - 1), ring)
            .compose(
                PlaintextCircuit::identity(1, ring).tensor(PlaintextCircuit::gal(H.hypercube().frobenius(1), Gal, ring), ring)
                    .compose(PlaintextCircuit::identity(1, ring).output_twice(ring), ring).output_twice(ring)
                    .tensor_pow(1 << (log2_d - 1), ring),
                ring
            ).compose(result, ring);

    } else {
        // this is the `p = 3 mod 4` case
        assert_eq!(1, H.hypercube().dim_count());
    
        let coeff = H.ring().pow(H.ring().canonical_gen(), m - m/4);
        result = PlaintextCircuit::add(ring).tensor(PlaintextCircuit::linear_transform_ring(&[coeff], ring).compose(PlaintextCircuit::sub(ring), ring), ring).tensor_pow(1 << (log2_d - 1), ring)
            .compose(
                PlaintextCircuit::identity(1, ring).tensor(PlaintextCircuit::gal(H.hypercube().frobenius(1), Gal, ring), ring)
                    .compose(PlaintextCircuit::identity(1, ring).output_twice(ring), ring).output_twice(ring)
                    .tensor_pow(1 << (log2_d - 1), ring),
                ring
            ).compose(result, ring);
    }

    return result;
}

///
/// Inverse to [`slots_to_coeffs_fat_impl()`].
/// 
#[instrument(skip_all)]
fn coeffs_to_slots_fat_impl<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let m = H.galois_group().m();
    let log2_m = ZZi64.abs_log2_ceil(&(m as i64)).unwrap();
    assert!(m == 1 << log2_m);

    let mut result = Vec::new();

    if H.hypercube().dim_count() == 2 {
        // this is the `p = 1 mod 4` case
        assert_eq!(2, H.hypercube().dim_length(1));
        let S = H.slot_ring();
        let Gal = H.galois_group();

        result.push(MatmulTransform::blockmatmul0d_inv(H, |row, col, idxs| 
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), col * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(row)
        ));
        result.extend(slots_to_coeffs_base_inv(H));
    } else {
        // this is the `p = 3 mod 4` case
        assert_eq!(1, H.hypercube().dim_count());
        let S = H.slot_ring();
        let Gal = H.galois_group();
        let d= S.rank();

        result.push(MatmulTransform::blockmatmul0d_inv(H, |row, col, idxs| if col < d/2 {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), col * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(row)
        } else {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), d/2 + (col - d/2) * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(row)
        }));

        result.extend(slots_to_coeffs_base_inv(H));

        result.push(MatmulTransform::blockmatmul0d_inv(H, |row, col, _idxs| if col < d/2 {
           if row == col { S.base_ring().one() } else { S.base_ring().zero() }
        } else {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), col - d/2 + m as usize/4)).at(row)
        }));
    }

    return result;
}

///
/// Inverse to [`slots_to_coeffs_fat_Xbasis()`].
/// 
#[instrument(skip_all)]
fn coeffs_to_slots_fat_Xbasis<R>(H: &HypercubeIsomorphism<R>) -> Vec<MatmulTransform<R::Type>>
    where R: RingStore,
        R::Type: Sized + NumberRingQuotient,
        BaseRing<R>: NiceZn
{
    let mut result = Vec::new();
    let S = H.slot_ring();
    let Gal = H.galois_group();
    let d = S.rank();
    let m = Gal.m() as usize;

    if H.hypercube().dim_count() == 2 {
        // this is the `p = 1 mod 4` case
        assert_eq!(2, H.hypercube().dim_length(1));
        result.extend(coeffs_to_slots_fat_impl(H));
        let final_transform = MatmulTransform::blockmatmul0d(H, |i, j, idxs| 
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), j * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(i)
        );
        result.push(final_transform);
    } else {
        // this is the `p = 3 mod 4` case
        assert_eq!(1, H.hypercube().dim_count());
        result.extend(coeffs_to_slots_fat_impl(H));
        let final_transform = MatmulTransform::blockmatmul0d(H, |i, j, idxs| if j < d/2 {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), j * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(i)
        } else {
            S.wrt_canonical_basis(&S.pow(S.canonical_gen(), m/4 + (j - d/2) * Gal.representative(&Gal.inv(&H.hypercube().map_usize(idxs))) as usize)).at(i)
        });
        take_mut::take(result.last_mut().unwrap(), |last| final_transform.compose(H.ring(), H.hypercube(), &last));
    }
    return result;
}

#[cfg(test)]
use feanor_math::rings::poly::dense_poly::DensePolyRing;
#[cfg(test)]
use feanor_math::rings::poly::PolyRingStore;
#[cfg(test)]
use feanor_math::algorithms::fft::cooley_tuckey::bitreverse;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::Pow2CyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::quotient_by_ideal::NumberRingQuotientByIdealBase;
#[cfg(test)]
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;
#[cfg(test)]
use crate::ring_literal;

#[test]
fn test_slots_to_coeffs_non_cyclotomic_ring() {
    let number_ring = Pow2CyclotomicNumberRing::new(64);
    let acting_galois_group = number_ring.galois_group().get_group().clone().subgroup([number_ring.galois_group().from_representative(17)]);
    let FpX = DensePolyRing::new(zn_big::Zn::new(ZZbig, int_cast(257, ZZbig, ZZi64)), "X");
    let [t] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(4) - 2]);
    let P = NumberRingQuotientByIdealBase::new::<false>(number_ring, FpX, t, acting_galois_group);
    let h = HypercubeStructure::default_pow2_hypercube(P.acting_galois_group(), int_cast(257, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&P, &h, Some("."));

    let input = H.from_slot_values([
        H.slot_ring().zero(), 
        H.slot_ring().neg_one(), 
        H.slot_ring().zero(),
        H.slot_ring().one(),
    ]);
    let actual = MatmulTransform::to_circuit_many(&P, &h, slots_to_coeffs_base(&H)).evaluate(&[input], P.identity()).pop().unwrap();

    let expected = P.from_canonical_basis([
        P.base_ring().zero(), 
        P.base_ring().zero(),
        P.base_ring().neg_one(), 
        P.base_ring().one()
    ]);
    assert_el_eq!(&P, expected, actual);
    
    let number_ring = Pow2CyclotomicNumberRing::new(64);
    let acting_galois_group = number_ring.galois_group().get_group().clone().subgroup([number_ring.galois_group().from_representative(33), number_ring.galois_group().from_representative(-1)]);
    let FpX = DensePolyRing::new(zn_big::Zn::new(ZZbig, int_cast(665857, ZZbig, ZZi64)), "X");
    let [t] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(30) - X.pow_ref(2) + 6]);
    let P = NumberRingQuotientByIdealBase::new::<false>(number_ring, FpX, t, acting_galois_group);
    let h = HypercubeStructure::default_pow2_hypercube(P.acting_galois_group(), int_cast(665857, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&P, &h, Some("."));

    let input = H.from_slot_values([
        H.slot_ring().zero(), 
        H.slot_ring().one(),
        H.slot_ring().neg_one(),
        H.slot_ring().zero(),
    ]);
    let actual = MatmulTransform::to_circuit_many(&P, &h, slots_to_coeffs_base(&H)).evaluate(&[input], P.identity()).pop().unwrap();

    let expected = P.from_canonical_basis([
        P.base_ring().zero(), 
        P.base_ring().neg_one(),
        P.base_ring().one(), 
        P.base_ring().zero()
    ]);
    assert_el_eq!(&P, expected, actual);
}

#[test]
fn test_slots_to_coeffs_thin() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    
    let mut current = H.from_slot_values((1..17).map(|i| H.slot_ring().int_hom().map(i)));
    for T in slots_to_coeffs_base(&H) {
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
    for T in slots_to_coeffs_base(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 32];
    for i in 0..4 {
        expected[bitreverse(i, 2) * 4] = (i + 1) as i32;
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);
}

#[test]
fn test_slots_to_coeffs_fat() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();
    
    let mut current = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| H.slot_ring().sum(
        (0..2).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), k), 
            (i + 1 + 16 * k) as i32
        ))
    )));
    for T in slots_to_coeffs_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 32];
    for i in 0..8 {
        for j in 0..2 {
            for k in 0..2 {
                expected[bitreverse(i, 3) * 2 + j * 16 + k] = (i * 2 + j + 16 * k + 1) as i32;
            }
        }
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);

    // `F23[X]/(X^32 + 1) ~ F_(23^8)^4`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(23));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(23, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();

    let mut current = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| H.slot_ring().sum(
        (0..8).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), k), 
            (i + 1 + 4 * k) as i32
        ))
    )));
    for T in slots_to_coeffs_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 32];
    for i in 0..4 {
        for k in 0..8 {
            if k < 4 {
                expected[bitreverse(i, 2) * 4 + k] = (i + 1 + k * 4) as i32;
            } else {
                expected[bitreverse(i, 2) * 4 + k - 4 + 16] = (i + 1 + k * 4) as i32;
            }
        }
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);

    // `F31[X]/(X^64 + 1) ~ F_(31^4)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(128);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(31));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(31, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();

    let mut current = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| H.slot_ring().sum(
        (0..4).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), k), 
            (i + 1 + 16 * k) as i32
        ))
    )));
    for T in slots_to_coeffs_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 64];
    for i in 0..16 {
        for k in 0..4 {
            if k < 2 {
                expected[bitreverse(i, 4) * 2 + k] = (i + 1 + k * 16) as i32;
            } else {
                expected[bitreverse(i, 4) * 2 + k - 2 + 32] = (i + 1 + k * 16) as i32;
            }
        }
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);
}

#[test]
fn test_slots_to_coeffs_fat_Xbasis() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();
    let Gal = H.galois_group();

    let mut current = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, g)| H.slot_ring().sum(
        (0..2).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), k * Gal.representative(&Gal.inv(&g)) as usize), 
            (i + 1 + 16 * k) as i32
        ))
    )));
    for T in slots_to_coeffs_fat_Xbasis(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 32];
    for i in 0..8 {
        for j in 0..2 {
            for k in 0..2 {
                expected[bitreverse(i, 3) * 2 + j * 16 + k] = (i * 2 + j + 16 * k + 1) as i32;
            }
        }
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);

    // `F23[X]/(X^32 + 1) ~ F_(23^8)^4`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(23));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(23, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();
    let Gal = H.galois_group();

    let mut current = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, g)| H.slot_ring().sum(
        (0..8).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), if k < 4 {
                k * Gal.representative(&Gal.inv(&g)) as usize
            } else {
                (k - 4) * Gal.representative(&Gal.inv(&g)) as usize + 16
            }), 
            (i + 1 + 4 * k) as i32
        ))
    )));
    for T in slots_to_coeffs_fat_Xbasis(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 32];
    for i in 0..4 {
        for k in 0..8 {
            if k < 4 {
                expected[bitreverse(i, 2) * 4 + k] = (i + 1 + k * 4) as i32;
            } else {
                expected[bitreverse(i, 2) * 4 + k - 4 + 16] = (i + 1 + k * 4) as i32;
            }
        }
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);

    // `F31[X]/(X^64 + 1) ~ F_(31^4)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(128);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(31));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(31, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();
    let Gal = H.galois_group();

    let mut current = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, g)| H.slot_ring().sum(
        (0..4).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), if k < 2 {
                k * Gal.representative(&Gal.inv(&g)) as usize
            } else {
                (k - 2) * Gal.representative(&Gal.inv(&g)) as usize + 32
            }), 
            (i + 1 + 16 * k) as i32
        ))
    )));
    for T in slots_to_coeffs_fat_Xbasis(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let mut expected = [0; 64];
    for i in 0..16 {
        for k in 0..4 {
            if k < 2 {
                expected[bitreverse(i, 4) * 2 + k] = (i + 1 + k * 16) as i32;
            } else {
                expected[bitreverse(i, 4) * 2 + k - 2 + 32] = (i + 1 + k * 16) as i32;
            }
        }
    }
    assert_el_eq!(&ring, &ring_literal(&ring, &expected), &current);
}

#[test]
fn test_coeffs_to_slots_fat() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();
    
    let mut current = [0; 32];
    for i in 0..8 {
        for j in 0..2 {
            for k in 0..2 {
                current[bitreverse(i, 3) * 2 + j * 16 + k] = (i * 2 + j + 16 * k + 1) as i32;
            }
        }
    }
    let mut current = ring_literal(&ring, &current);
    for T in coeffs_to_slots_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let expected = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| H.slot_ring().sum(
        (0..2).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), k), 
            (i + 1 + 16 * k) as i32
        ))
    )));
    assert_el_eq!(&ring, &expected, &current);
    
    // `F31[X]/(X^64 + 1) ~ F_(31^4)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(128);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(31));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(31, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();

    let mut current = [0; 64];
    for i in 0..16 {
        for k in 0..4 {
            if k < 2 {
                current[bitreverse(i, 4) * 2 + k] = (i + 1 + k * 16) as i32;
            } else {
                current[bitreverse(i, 4) * 2 + k - 2 + 32] = (i + 1 + k * 16) as i32;
            }
        }
    }
    let mut current = ring_literal(&ring, &current);
    for T in coeffs_to_slots_fat_impl(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let expected = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| H.slot_ring().sum(
        (0..4).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), k), 
            (i + 1 + 16 * k) as i32
        ))
    )));
    assert_el_eq!(&ring, &expected, &current);
}

#[test]
fn test_coeffs_to_slots_fat_unpack() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    
    let mut current = [0; 32];
    for i in 0..8 {
        for j in 0..2 {
            for k in 0..2 {
                current[bitreverse(i, 3) * 2 + j * 16 + k] = (i * 2 + j + 16 * k + 1) as i32;
            }
        }
    }
    let current = ring_literal(&ring, &current);
    let actual = coeffs_to_slots_fat_unpack(&H).evaluate(&[current], ring.identity());
    let expected = (0..2).map(|k| H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| 
        H.slot_ring().int_hom().map((i + 1 + 16 * bitreverse(k, 1)) as i32)
    ))).collect::<Vec<_>>();
    
    assert_eq!(expected.len(), actual.len());
    for (expected, actual) in expected.iter().zip(actual.iter()) {
        assert_el_eq!(&ring, &expected, &actual);
    }

    // `F31[X]/(X^64 + 1) ~ F_(31^4)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(128);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(31));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(31, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);

    let mut current = [0; 64];
    for i in 0..16 {
        for k in 0..4 {
            if k < 2 {
                current[bitreverse(i, 4) * 2 + k] = (i + 1 + k * 16) as i32;
            } else {
                current[bitreverse(i, 4) * 2 + k - 2 + 32] = (i + 1 + k * 16) as i32;
            }
        }
    }

    let actual = coeffs_to_slots_fat_unpack(&H).evaluate(&[ring_literal(&ring, &current)], ring.identity());
    let expected = (0..4).map(|k| H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| 
        H.slot_ring().int_hom().map((i + 1 + 16 * bitreverse(k, 2)) as i32)
    ))).collect::<Vec<_>>();

    assert_eq!(expected.len(), actual.len());
    for (expected, actual) in expected.iter().zip(actual.iter()) {
        assert_el_eq!(&ring, &expected, &actual);
    }
}

#[test]
fn test_slots_to_coeffs_pack() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    
    let input = (0..2).map(|k| H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| 
        H.slot_ring().int_hom().map((i + 1 + 16 * bitreverse(k, 1)) as i32)
    ))).collect::<Vec<_>>();
    let actual = slots_to_coeffs_fat_pack(&H).evaluate(&input, ring.identity());
    
    let mut expected = [0; 32];
    for i in 0..8 {
        for j in 0..2 {
            for k in 0..2 {
                expected[bitreverse(i, 3) * 2 + j * 16 + k] = (i * 2 + j + 16 * k + 1) as i32;
            }
        }
    }
    assert_eq!(1, actual.len());
    assert_el_eq!(&ring, ring_literal(&ring, &expected), &actual[0]);

    // `F31[X]/(X^64 + 1) ~ F_(31^4)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(128);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(31));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(31, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);

    let input = (0..4).map(|k| H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, _)| 
        H.slot_ring().int_hom().map((i + 1 + 16 * bitreverse(k, 2)) as i32)
    ))).collect::<Vec<_>>();
    let actual = slots_to_coeffs_fat_pack(&H).evaluate(&input, ring.identity());

    let mut expected = [0; 64];
    for i in 0..16 {
        for k in 0..4 {
            if k < 2 {
                expected[bitreverse(i, 4) * 2 + k] = (i + 1 + k * 16) as i32;
            } else {
                expected[bitreverse(i, 4) * 2 + k - 2 + 32] = (i + 1 + k * 16) as i32;
            }
        }
    }
    assert_eq!(1, actual.len());
    assert_el_eq!(&ring, ring_literal(&ring, &expected), &actual[0]);
}

#[test]
fn test_coeffs_to_slots_fat_Xbasis() {
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let Gal = H.galois_group();
    let S = H.slot_ring();
    
    let mut current = [0; 32];
    for i in 0..8 {
        for j in 0..2 {
            for k in 0..2 {
                current[bitreverse(i, 3) * 2 + j * 16 + k] = (i * 2 + j + 16 * k + 1) as i32;
            }
        }
    }
    let mut current = ring_literal(&ring, &current);
    for T in coeffs_to_slots_fat_Xbasis(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let expected = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, g)| H.slot_ring().sum(
        (0..2).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), k * Gal.representative(&Gal.inv(&g)) as usize), 
            (i + 1 + 16 * k) as i32
        ))
    )));
    assert_el_eq!(&ring, &expected, &current);

    // `F31[X]/(X^64 + 1) ~ F_(31^4)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(128);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(31));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(31, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    let S = H.slot_ring();
    let Gal = H.galois_group();

    let mut current = [0; 64];
    for i in 0..16 {
        for k in 0..4 {
            if k < 2 {
                current[bitreverse(i, 4) * 2 + k] = (i + 1 + k * 16) as i32;
            } else {
                current[bitreverse(i, 4) * 2 + k - 2 + 32] = (i + 1 + k * 16) as i32;
            }
        }
    }
    let mut current = ring_literal(&ring, &current);
    for T in coeffs_to_slots_fat_Xbasis(&H) {
        current = ring.get_ring().compute_linear_transform(H.hypercube(), &current, &T);
    }

    let expected = H.from_slot_values(H.hypercube().element_iter().enumerate().map(|(i, g)| H.slot_ring().sum(
        (0..4).map(|k| S.int_hom().mul_map(
            S.pow(S.canonical_gen(), if k < 2 {
                k * Gal.representative(&Gal.inv(&g)) as usize
            } else {
                (k - 2) * Gal.representative(&Gal.inv(&g)) as usize + 32
            }), 
            (i + 1 + 16 * k) as i32
        ))
    )));
    assert_el_eq!(&ring, &expected, &current);
}

#[test]
fn test_slots_to_coeffs_thin_inv() {
    // `F23[X]/(X^32 + 1) ~ F_(23^8)^4`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(23));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(23, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);

    for (transform, actual) in slots_to_coeffs_base(&H).into_iter().rev().zip(slots_to_coeffs_base_inv(&H).into_iter()) {
        let expected = transform.inverse(&H);
        assert!(expected.eq(H.ring(), H.hypercube(), &actual));
    }
    
    // `F97[X]/(X^32 + 1) ~ F_(97^2)^16`
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(64);
    let ring = NumberRingQuotientByIntBase::new(number_ring, Zn::new(97));
    let hypercube = HypercubeStructure::default_pow2_hypercube(ring.acting_galois_group(), int_cast(97, ZZbig, ZZi64));
    let H = HypercubeIsomorphism::new::<false>(&&ring, &hypercube, None);
    
    for (transform, actual) in slots_to_coeffs_base(&H).into_iter().rev().zip(slots_to_coeffs_base_inv(&H).into_iter()) {
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
