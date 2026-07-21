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

use feanor_math::matrix::{AsPointerToSlice, Submatrix, SubmatrixMut};
use rayon_cond::CondIterator;
use tracing::{Level, span};

use crate::is_parallel;

/// Columns processed per cache block along the long `k` axis. Sized so one
/// block of `rhs` (`m * BLOCK` i64s, <= 128 KiB for `m = 32`) is reused from L2
/// across the `n` output rows while the `out` block stays in L1.
const BLOCK: usize = 512;

/// Columns held in registers at once within a block. Four i128 accumulators
/// (two registers each) fit the general-purpose register file alongside the
/// loop's working values.
const TILE: usize = 4;

/// Matrix multiplication of the nxm `i64` matrix `lhs` and the mxk `i64` matrix `rhs`.
///
/// `lhs` is in row-major storage, and both `rhs` and `out` are given as collections of their rows.
///
/// Optimized for small `n, m` (say <= 32) and large `k`.
pub fn skinny_matmul_i64_i64_i128<V1, V2, V3>(
    lhs: Submatrix<V1, i64>,
    rhs: Submatrix<V2, i64>,
    mut out: SubmatrixMut<V3, i128>,
) 
    where V1: Sync + AsPointerToSlice<i64>,
        V2: Sync + AsPointerToSlice<i64>,
        V3: Sync + AsPointerToSlice<i128>
{
    let n = lhs.row_count();
    let m = lhs.col_count();
    let k = rhs.col_count();
    assert_eq!(m, rhs.row_count());
    assert_eq!(n, out.row_count());
    assert_eq!(k, out.col_count());

    let mut tasks = Vec::with_capacity(k.div_ceil(BLOCK));
    while out.col_count() > BLOCK {
        let out_col_count = out.col_count();
        let (current, rest) = out.split_cols(0..BLOCK, BLOCK..out_col_count);
        tasks.push(current);
        out = rest;
    }
    tasks.push(out);
    CondIterator::new(tasks, is_parallel()).enumerate().for_each(|(i, out)| span!(Level::INFO, "matmul_block").in_scope(|| {
        skinny_matmul_i64_i64_i128_block(
            lhs,
            rhs.restrict_cols((i * BLOCK)..usize::min((i + 1) * BLOCK, k)),
            out
        )
    }));
}

fn skinny_matmul_i64_i64_i128_block<V1, V2, V3>(
    lhs: Submatrix<V1, i64>,
    rhs: Submatrix<V2, i64>,
    mut out: SubmatrixMut<V3, i128>,
) 
    where V1: AsPointerToSlice<i64>,
        V2: AsPointerToSlice<i64>,
        V3: AsPointerToSlice<i128>,
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
            o[c..c + TILE].copy_from_slice(&acc);
            c += TILE;
        }
        // Tail: fewer than TILE columns left in this block.
        while c < k {
            let mut acc = 0i128;
            for (&a, row) in lhs_row.iter().zip(rhs.row_iter()) {
                acc += (a as i128) * (row[c] as i128);
            }
            o[c] = acc;
            c += 1;
        }
    }
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
pub fn skinny_matmul_i128_i64_i128<V1, V2, V3>(
    lhs: Submatrix<V1, i128>,
    rhs: Submatrix<V2, i64>,
    mut out: SubmatrixMut<V3, i128>,
) 
    where V1: Sync + AsPointerToSlice<i128>,
        V2: Sync + AsPointerToSlice<i64>,
        V3: Sync + AsPointerToSlice<i128>,
{
    let n = lhs.row_count();
    let m = lhs.col_count();
    let k = rhs.col_count();
    assert_eq!(m, rhs.row_count());
    assert_eq!(n, out.row_count());
    assert_eq!(k, out.col_count());

    let mut tasks = Vec::with_capacity(k.div_ceil(BLOCK));
    while out.col_count() > BLOCK {
        let out_col_count = out.col_count();
        let (current, rest) = out.split_cols(0..BLOCK, BLOCK..out_col_count);
        tasks.push(current);
        out = rest;
    }
    tasks.push(out);
    CondIterator::new(tasks, is_parallel()).enumerate().for_each(|(i, out)| span!(Level::INFO, "matmul_block").in_scope(|| {
        skinny_matmul_i128_i64_i128_block(
            lhs,
            rhs.restrict_cols((i * BLOCK)..usize::min((i + 1) * BLOCK, k)),
            out
        )
    }));
}

fn skinny_matmul_i128_i64_i128_block<V1, V2, V3>(
    lhs: Submatrix<V1, i128>,
    rhs: Submatrix<V2, i64>,
    mut out: SubmatrixMut<V3, i128>,
) 
    where V1: AsPointerToSlice<i128>,
        V2: AsPointerToSlice<i64>,
        V3: AsPointerToSlice<i128>,
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
            o[c..c + TILE].copy_from_slice(&acc);
            c += TILE;
        }
        while c < k {
            let mut acc = 0i128;
            for (&a, row) in lhs_row.iter().zip(rhs.row_iter()) {
                acc += a * (row[c] as i128);
            }
            o[c] = acc;
            c += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // xorshift, kept dependency-free
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        // i64 bounded to ~2^57 so a sum of <= 32 i64*i64 products stays within i128
        fn i64(&mut self) -> i64 {
            (self.next() as i64) >> 7
        }
        // i128 spanning into the high limb (~2^89) so the 128x64 path is exercised
        fn i128(&mut self) -> i128 {
            ((self.next() as i64 as i128) << 26) | (self.next() as i64 as i128 >> 38)
        }
        // i64 bounded to ~2^29 so ~2^89 * ~2^29 * 32 stays within i128
        fn i64_narrow(&mut self) -> i64 {
            (self.next() as i64) >> 35
        }
    }

    fn run_i64(lhs: &[i64], rhs: &[Vec<i64>], n: usize, m: usize, k: usize) -> Vec<Vec<i128>> {
        let mut out = vec![vec![0i128; k]; n];
        skinny_matmul_i64_i64_i128(
            Submatrix::from_1d(lhs, n, m), 
            Submatrix::from_2d(rhs), 
            SubmatrixMut::from_2d(&mut out)
        );
        out
    }

    fn run_i128(lhs: &[i128], rhs: &[Vec<i64>], n: usize, m: usize, k: usize) -> Vec<Vec<i128>> {
        let mut out = vec![vec![0i128; k]; n];
        skinny_matmul_i128_i64_i128(
            Submatrix::from_1d(lhs, n, m), 
            Submatrix::from_2d(rhs), 
            SubmatrixMut::from_2d(&mut out)
        );
        out
    }

    fn expect_i64(lhs: &[i64], rhs: &[Vec<i64>], n: usize, m: usize, k: usize) -> Vec<Vec<i128>> {
        let mut out = vec![vec![0i128; k]; n];
        for i in 0..n {
            for l in 0..k {
                let mut acc = 0i128;
                for j in 0..m {
                    acc += (lhs[i * m + j] as i128) * (rhs[j][l] as i128);
                }
                out[i][l] = acc;
            }
        }
        out
    }

    fn expect_i128(lhs: &[i128], rhs: &[Vec<i64>], n: usize, m: usize, k: usize) -> Vec<Vec<i128>> {
        let mut out = vec![vec![0i128; k]; n];
        for i in 0..n {
            for l in 0..k {
                let mut acc = 0i128;
                for j in 0..m {
                    acc += lhs[i * m + j] * (rhs[j][l] as i128);
                }
                out[i][l] = acc;
            }
        }
        out
    }

    // Sizes chosen to exercise: n != m, the n = 1 special case, m = 1, k = 1,
    // k below / equal to / crossing TILE and BLOCK boundaries.
    const CASES: &[(usize, usize, usize)] = &[
        (1, 1, 1),
        (1, 1, 3),
        (3, 5, 1),
        (1, 32, 1000),
        (32, 1, 777),
        (7, 3, 4),
        (4, 4, TILE - 1),
        (2, 2, TILE),
        (2, 2, TILE + 1),
        (5, 6, BLOCK - 1),
        (5, 6, BLOCK),
        (3, 4, BLOCK + 7),
        (8, 8, 2 * BLOCK + 13),
        (32, 32, 300),
    ];

    #[test]
    fn matches_reference_i64() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for &(n, m, k) in CASES {
            let lhs: Vec<i64> = (0..n * m).map(|_| rng.i64()).collect();
            let rhs: Vec<Vec<i64>> = (0..m).map(|_| (0..k).map(|_| rng.i64()).collect()).collect();
            assert_eq!(
                run_i64(&lhs, &rhs, n, m, k),
                expect_i64(&lhs, &rhs, n, m, k),
                "i64 kernel mismatch at n={n} m={m} k={k}"
            );
        }
    }

    #[test]
    fn matches_reference_i128() {
        let mut rng = Rng(0xd1b5_4a32_d192_ed03);
        for &(n, m, k) in CASES {
            let lhs: Vec<i128> = (0..n * m).map(|_| rng.i128()).collect();
            let rhs: Vec<Vec<i64>> = (0..m).map(|_| (0..k).map(|_| rng.i64_narrow()).collect()).collect();
            assert_eq!(
                run_i128(&lhs, &rhs, n, m, k),
                expect_i128(&lhs, &rhs, n, m, k),
                "i128 kernel mismatch at n={n} m={m} k={k}"
            );
        }
    }

    #[test]
    fn handles_extreme_i64_values() {
        // full-range i64 factors; a single i64*i64 product is always exact in i128
        let n = 2;
        let m = 2;
        let k = 5;
        let lhs = vec![i64::MAX, i64::MIN, -1, 1];
        let rhs = vec![
            vec![i64::MAX, i64::MIN, 0, 7, -7],
            vec![i64::MIN, i64::MAX, -3, 3, 123456789],
        ];
        assert_eq!(
            run_i64(&lhs, &rhs, n, m, k),
            expect_i64(&lhs, &rhs, n, m, k)
        );
    }
}
