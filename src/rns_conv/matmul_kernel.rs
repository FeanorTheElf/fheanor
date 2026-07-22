//! Skinny integer matrix multiplication.
//!
//! Both kernels compute `out = lhs * rhs` where the contraction dimension `m`
//! and the number of output rows `n` are small (say `<= 32`) while the row
//! length `k` is large. They share one layout:
//!
//! * The long `k` axis is split into cache blocks of `BLOCK` columns. For a
//!   fixed block, the corresponding slice of every `rhs` row is reused across
//!   all `n` output rows, so -- as long as the block stays resident in cache --
//!   each `rhs` element is fetched from memory once and each `out` element is
//!   written once, the minimum traffic this product allows.
//! * Within a block, columns are handled in register tiles of `TILE`. The
//!   `TILE` i128 accumulators stay in registers across the whole `m`-long
//!   contraction, so the inner loop is a plain stream of multiply-accumulates
//!   with no load/store of the accumulators until the tile is finished.
//!
//! Keeping the accumulators in registers is what makes the widening multiply
//! fast: `(a as i128) * (b as i128)` with `i64` operands lowers to a single
//! `64x64 -> 128` multiply here, whereas accumulating straight into memory made
//! LLVM emit a full (three-multiply) `128x128` product -- about 3x slower.
//!
//! For `n = 1` the layout degenerates to a single streaming pass over the `rhs`
//! rows, which is the memory-bound regime the second kernel's `n = 1` case
//! cares about.

use std::mem::MaybeUninit;

use feanor_math::matrix::{AsPointerToSlice, Submatrix, SubmatrixMut};
use rayon_cond::CondIterator;
use tracing::{Level, Span, span};

use crate::is_parallel;

/// Columns processed per cache block along the long `k` axis. Sized so one
/// block of `rhs` (`m * BLOCK` i64s, <= 128 KiB for `m = 32`) is reused from L2
/// across the `n` output rows while the `out` block stays in L1.
pub const BLOCK: usize = 512;

/// Columns held in registers at once within a block. Four i128 accumulators
/// (two registers each) fit the general-purpose register file alongside the
/// loop's working values.
const TILE: usize = 4;

/// Matrix multiplication of the nxm `i64` matrix `lhs` and the mxk `i64` matrix `rhs`.
///
/// `lhs` is in row-major storage, and both `rhs` and `out` are given as collections of their rows.
///
/// Optimized for small `n, m` (say <= 32) and large `k`.
#[allow(unused)]
pub fn skinny_matmul_i64_i64_i128<'a, V1, V2, V3>(
    lhs: Submatrix<V1, i64>,
    rhs: Submatrix<V2, i64>,
    mut out: SubmatrixMut<'a, V3, MaybeUninit<i128>>,
) -> SubmatrixMut<'a, V3, i128>
    where V1: Sync + AsPointerToSlice<i64>,
        V2: Sync + AsPointerToSlice<i64>,
        V3: Sync + AsPointerToSlice<i128> + AsPointerToSlice<MaybeUninit<i128>>,
{
    let n = lhs.row_count();
    let m = lhs.col_count();
    let k = rhs.col_count();
    assert_eq!(m, rhs.row_count());
    assert_eq!(n, out.row_count());
    assert_eq!(k, out.col_count());

    let mut tasks = Vec::with_capacity(k.div_ceil(BLOCK));
    let mut current_out = out.reborrow();
    while current_out.col_count() > BLOCK {
        let out_col_count = current_out.col_count();
        let (current, rest) = current_out.split_cols(0..BLOCK, BLOCK..out_col_count);
        tasks.push(current);
        current_out = rest;
    }
    tasks.push(current_out);
    let outer_span = Span::current();
    CondIterator::new(tasks, is_parallel()).enumerate().for_each(|(i, out)| span!(parent: &outer_span, Level::INFO, "matmul_block").in_scope(|| {
        _ = skinny_matmul_i64_i64_i128_block(
            lhs,
            rhs.restrict_cols((i * BLOCK)..usize::min((i + 1) * BLOCK, k)),
            out
        );
    }));

    // SAFETY: this was just initialized above
    return unsafe { out.assume_init() };
}

pub fn skinny_matmul_i64_i64_i128_block<'a, V1, V2, V3>(
    lhs: Submatrix<V1, i64>,
    rhs: Submatrix<V2, i64>,
    mut out: SubmatrixMut<'a, V3, MaybeUninit<i128>>,
) -> SubmatrixMut<'a, V3, i128>
    where V1: AsPointerToSlice<i64>,
        V2: AsPointerToSlice<i64>,
        V3: AsPointerToSlice<i128> + AsPointerToSlice<MaybeUninit<i128>>,
{
    let n = lhs.row_count();
    let m = lhs.col_count();
    let k = rhs.col_count();
    assert_eq!(m, rhs.row_count());
    assert_eq!(n, out.row_count());
    assert_eq!(k, out.col_count());
    assert!(k <= BLOCK);

    for i in 0..n {
        let lhs_row = lhs.row_at(i);
        let o = out.row_mut_at(i);
        let mut c = 0;
        while c + TILE <= k {
            let mut acc = [0i128; TILE];
            for (&a, row) in lhs_row.iter().zip(rhs.row_iter()) {
                let r: &[i64; TILE] = row[c..c + TILE].try_into().unwrap();
                for t in 0..TILE {
                    acc[t] += (a as i128) * (r[t] as i128);
                }
            }
            for j in 0..TILE {
                o[c + j] = MaybeUninit::new(acc[j]);
            }
            c += TILE;
        }
        // Tail: fewer than TILE columns left in this block.
        while c < k {
            let mut acc = 0i128;
            for (&a, row) in lhs_row.iter().zip(rhs.row_iter()) {
                acc += (a as i128) * (row[c] as i128);
            }
            o[c] = MaybeUninit::new(acc);
            c += 1;
        }
    }

    // SAFETY: this was just initialized above
    return unsafe { out.assume_init() };
}

/// Matrix multiplication of the nxm `i128` matrix `lhs` and the mxk `i64` matrix `rhs`.
///
/// `lhs` is in row-major storage, and both `rhs` and `out` are given as collections of their rows.
///
/// Optimized for small `n, m` (say <= 32) and large `k`. An important special case is `n = 1`,
/// which should also be efficient.
///
/// The mathematical products are assumed to fit in i128 (no overflow), so each
/// `lhs * rhs` term is a plain `128x64 -> 128` multiply.
#[allow(unused)]
pub fn skinny_matmul_i128_i64_i128<'a, V1, V2, V3>(
    lhs: Submatrix<V1, i128>,
    rhs: Submatrix<V2, i64>,
    mut out: SubmatrixMut<'a, V3, MaybeUninit<i128>>,
) -> SubmatrixMut<'a, V3, i128>
    where V1: Sync + AsPointerToSlice<i128>,
        V2: Sync + AsPointerToSlice<i64>,
        V3: Sync + AsPointerToSlice<i128> + AsPointerToSlice<MaybeUninit<i128>>,
{
    let n = lhs.row_count();
    let m = lhs.col_count();
    let k = rhs.col_count();
    assert_eq!(m, rhs.row_count());
    assert_eq!(n, out.row_count());
    assert_eq!(k, out.col_count());

    let mut tasks = Vec::with_capacity(k.div_ceil(BLOCK));
    let mut current_out = out.reborrow();
    while current_out.col_count() > BLOCK {
        let out_col_count = current_out.col_count();
        let (current, rest) = current_out.split_cols(0..BLOCK, BLOCK..out_col_count);
        tasks.push(current);
        current_out = rest;
    }
    tasks.push(current_out);
    let outer_span = Span::current();
    CondIterator::new(tasks, is_parallel()).enumerate().for_each(|(i, out)| span!(parent: &outer_span, Level::INFO, "matmul_block").in_scope(|| {
        _ = skinny_matmul_i128_i64_i128_block(
            lhs,
            rhs.restrict_cols((i * BLOCK)..usize::min((i + 1) * BLOCK, k)),
            out
        )
    }));
    // SAFETY: this was just initialized above
    return unsafe { out.assume_init() };
}

pub fn skinny_matmul_i128_i64_i128_block<'a, V1, V2, V3>(
    lhs: Submatrix<V1, i128>,
    rhs: Submatrix<V2, i64>,
    mut out: SubmatrixMut<'a, V3, MaybeUninit<i128>>,
) -> SubmatrixMut<'a, V3, i128>
    where V1: AsPointerToSlice<i128>,
        V2: AsPointerToSlice<i64>,
        V3: AsPointerToSlice<i128> + AsPointerToSlice<MaybeUninit<i128>>,
{
    let n = lhs.row_count();
    let m = lhs.col_count();
    let k = rhs.col_count();
    assert_eq!(m, rhs.row_count());
    assert_eq!(n, out.row_count());
    assert_eq!(k, out.col_count());
    assert!(k <= BLOCK);

    for i in 0..n {
        let lhs_row = lhs.row_at(i);
        let o = out.row_mut_at(i);
        let mut c = 0;
        while c + TILE <= k {
            let mut acc = [0i128; TILE];
            for (&a, row) in lhs_row.iter().zip(rhs.row_iter()) {
                let r: &[i64; TILE] = row[c..c + TILE].try_into().unwrap();
                for t in 0..TILE {
                    acc[t] += a * (r[t] as i128);
                }
            }
            for j in 0..TILE {
                o[c + j] = MaybeUninit::new(acc[j]);
            }
            c += TILE;
        }
        while c < k {
            let mut acc = 0i128;
            for (&a, row) in lhs_row.iter().zip(rhs.row_iter()) {
                acc += a * (row[c] as i128);
            }
            o[c] = MaybeUninit::new(acc);
            c += 1;
        }
    }
    // SAFETY: this was just initialized above
    return unsafe { out.assume_init() };
}
