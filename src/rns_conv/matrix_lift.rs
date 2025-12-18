use feanor_math::integer::*;
use feanor_math::matrix::*;
use feanor_math::homomorphism::*;
use feanor_math::seq::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::ring::*;
use feanor_math::ordered::OrderedRingStore;
use tracing::instrument;

use std::alloc::Allocator;
use std::alloc::Global;
use std::array::from_fn;

use crate::{ZZbig, ZZi64, ZZi128};
use super::RNSOperation;

///
/// Stores values for an almost exact conversion between RNS bases.
/// A complete conversion refers to the function
/// ```text
///   Z/QZ -> Z/Q'Z, x -> [lift(x)]
/// ```
/// In our case, the output of the function is allowed to have an error of `{ -Q, 0, Q }`,
/// unless the shortest lift of the input is bounded by `Q/4`, in which case the result
/// is always correct.
/// 
/// # Implementation
/// 
/// Similar to (the now deprecated) [`AlmostExactBaseConversion`], but this implementation
/// writes the operation as integer matrix multiplication, and is usually more efficient.
/// 
/// [`AlmostExactBaseConversion`]: crate::rns_conv::lift::AlmostExactBaseConversion
/// 
pub struct AlmostExactMatrixBaseConversion<A = Global>
    where A: Allocator + Clone
{
    from_summands: Vec<Zn>,
    to_summands: Vec<Zn>,
    /// the values `q/Q mod q` for each RNS factor q dividing Q (ordered as `from_summands`)
    q_over_Q: Vec<ZnEl>,
    /// shortest lifts of the values `Q/q mod q'` for each RNS factor q dividing Q (ordered 
    /// as `from_summands`, mapped to col index) and q' dividing Q' (ordered as `to_summands`,
    /// mapped to row index)
    Q_over_q_mod: OwnedMatrix<i64>,
    /// the values `round( Q/q/gamma )` for each RNS factor `q` dividing `Q`; Unfortunately,
    /// these sometimes exceed 64 bits, thus cannot store them in the matrix `Q_over_q_mod`
    Q_over_q_downscaled: Vec<i128>,
    gamma: i128,
    /// `Q mod q'` for every RNS factor q' of Q' (ordered as `to_summands`)
    Q_mod_q: Vec<ZnEl>,
    allocator: A
}

// we currently use `any_lift()`; I haven't yet documented it anywhere, but in fact the largest output of `zn_64::Zn::any_lift()` is currently `6 * modulus()`
const ZN_ANY_LIFT_FACTOR: i64 = 6;

const BLOCK_SIZE_LOG2: usize = 2;
const BLOCK_SIZE: usize = 1 << BLOCK_SIZE_LOG2;

#[inline]
fn matmul_4x4_i64_to_i128(lhs: [&[i64; BLOCK_SIZE]; BLOCK_SIZE], rhs: [&[i64]; BLOCK_SIZE], out: &mut [&mut [i128]; BLOCK_SIZE]) {
    let len = rhs[0].len();
    for i in 0..BLOCK_SIZE {
        assert_eq!(len, rhs[i].len());
        assert_eq!(len, out[i].len());
    }

    for (l_r, o_r) in lhs.into_iter().zip(out.into_iter()) {
        let o_r = &mut **o_r;
        for j in 0..len {
            let mut value = 0;
            for k in 0..BLOCK_SIZE {
                // safe since k < len
                debug_assert!(j < rhs[k].len());
                value += (unsafe { *rhs[k].get_unchecked(j) } as i128) * (l_r[k] as i128);
            }
            // safe since k < len
            debug_assert!(j < o_r.len());
            *unsafe { o_r.get_unchecked_mut(j) } += value;
        }
    }
}

#[inline]
fn vecmatmul_4_i128_to_i128(lhs: [i128; BLOCK_SIZE], rhs: [&[i64]; BLOCK_SIZE], out: &mut [i128]) {
    let len = out.len();
    for i in 0..BLOCK_SIZE {
        assert_eq!(len, rhs[i].len());
    }

    for j in 0..len {
        let mut value = 0;
        for k in 0..BLOCK_SIZE {
            // safe since k < len
            debug_assert!(j < rhs[k].len());
            value += (unsafe { *rhs[k].get_unchecked(j) } as i128) * (lhs[k] as i128);
        }
        // safe since k < len
        debug_assert!(j < out.len());
        *unsafe { out.get_unchecked_mut(j) } += value;
    }
}

fn pad_to_block(len: usize) -> usize {
    if len == 0 {
        0
    } else {
        ((len - 1) / (1 << BLOCK_SIZE_LOG2) + 1) * (1 << BLOCK_SIZE_LOG2)
    }
}

impl AlmostExactMatrixBaseConversion {

    ///
    /// Creates a new [`AlmostExactMatrixBaseConversion`] from `q` to `q'`.
    /// 
    pub fn new(in_rings: Vec<Zn>, out_rings: Vec<Zn>) -> Self {
        Self::new_with_alloc(in_rings, out_rings, Global)
    }
}

impl<A> AlmostExactMatrixBaseConversion<A> 
    where A: Allocator + Clone
{
    ///
    /// Creates a new [`AlmostExactMatrixBaseConversion`] from `q` to `q'`.
    /// 
    #[instrument(skip_all)]
    pub fn new_with_alloc(in_rings: Vec<Zn>, out_rings: Vec<Zn>, allocator: A) -> Self {
        
        let Q = ZZbig.prod((0..in_rings.len()).map(|i| int_cast(*in_rings.at(i).modulus(), ZZbig, ZZi64)));

        let max = |l, r| if ZZbig.is_geq(&l, &r) { l } else { r };
        let max_computation_result = ZZbig.prod([
            in_rings.iter().map(|ring| int_cast(*ring.modulus() * ZN_ANY_LIFT_FACTOR, ZZbig, ZZi64)).reduce(max).unwrap_or(ZZbig.zero()),
            out_rings.iter().map(|ring| int_cast(*ring.modulus(), ZZbig, ZZi64)).reduce(max).unwrap_or(ZZbig.zero()),
            ZZbig.int_hom().map(in_rings.len() as i32)
        ].into_iter());
        assert!(ZZbig.is_lt(&max_computation_result, &ZZbig.power_of_two(i128::BITS as usize - 1)), "temporarily unreduced modular lift sum will overflow");

        // When computing the approximate lifted value, we can work with `gamma` in place of `Q`, where `gamma >= 4 r max(q)` (`q` runs through the input factors)
        let log2_r = ZZi64.abs_log2_ceil(&(in_rings.len() as i64)).unwrap_or(0);
        let log2_qmax = ZZi64.abs_log2_ceil(&(0..in_rings.len()).map(|i| *in_rings.at(i).modulus()).max().unwrap_or(0)).unwrap_or(0);
        let log2_any_lift_factor = ZZi64.abs_log2_ceil(&ZN_ANY_LIFT_FACTOR).unwrap_or(0);
        let gamma = ZZbig.power_of_two(log2_r + log2_qmax + log2_any_lift_factor + 2);
        // we compute a sum of `r` summands, each being a product of a lifted value (mod `q`, `q | Q`) and `gamma/q`; this must not overflow
        assert!(ZZbig.abs_log2_ceil(&gamma).unwrap() + log2_r + log2_any_lift_factor + 1 < ZZi128.get_ring().representable_bits().unwrap(), "correction computation will overflow");
        let gamma_log2 = ZZbig.abs_log2_ceil(&gamma).unwrap();
        assert!(gamma_log2 == ZZbig.abs_log2_floor(&gamma).unwrap());

        let Q_over_q_mod = OwnedMatrix::from_fn_in(pad_to_block(out_rings.len()), pad_to_block(in_rings.len()), |i, j| {
            if i < out_rings.len() && j < in_rings.len() {
                let ring = out_rings.at(i);
                ring.smallest_lift(ring.coerce(&ZZbig, ZZbig.checked_div(&Q, &int_cast(*in_rings.at(j).modulus(), ZZbig, ZZi64)).unwrap()))
            } else {
                0
            }
        }, Global);
        let Q_over_q_downscaled = (0..pad_to_block(in_rings.len())).map(|j| if j < in_rings.len() {
            int_cast(ZZbig.rounded_div(ZZbig.clone_el(&gamma), &int_cast(*in_rings.at(j).modulus(), ZZbig, ZZi64)), ZZi128, ZZbig)
        } else {
            0
        }).collect();
        let q_over_Q = (0..(in_rings.len())).map(|i| 
            in_rings.at(i).invert(&in_rings.at(i).coerce(&ZZbig, ZZbig.checked_div(&Q, &int_cast(*in_rings.at(i).modulus(), ZZbig, ZZi64)).unwrap())).unwrap()
        ).collect();

        Self {
            Q_over_q_mod: Q_over_q_mod,
            Q_over_q_downscaled: Q_over_q_downscaled,
            q_over_Q: q_over_Q,
            Q_mod_q: (0..out_rings.len()).map(|i| out_rings.at(i).coerce(&ZZbig, ZZbig.clone_el(&Q))).collect(),
            gamma: ZZi128.power_of_two(gamma_log2),
            allocator: allocator.clone(),
            from_summands: in_rings,
            to_summands: out_rings
        }
    }
}

impl<A> RNSOperation for AlmostExactMatrixBaseConversion<A> 
    where A: Allocator + Clone
{
    type Ring = Zn;

    type RingType = ZnBase;

    fn input_rings<'a>(&'a self) -> &'a [Zn] {
        &self.from_summands
    }

    fn output_rings<'a>(&'a self) -> &'a [Zn] {
        &self.to_summands
    }

    ///
    /// Performs the (almost) exact RNS base conversion
    /// ```text
    ///   Z/QZ -> Z/Q'Z, x -> smallest_lift(x) + kQ mod Q''
    /// ```
    /// where `k in { -1, 0, 1 }`.
    /// 
    /// Furthermore, if the shortest lift of the input is bounded by `Q/4`,
    /// then the result is guaranteed to be exact.
    /// 
    #[instrument(skip_all)]
    fn apply<V1, V2>(&self, input: Submatrix<V1, El<Self::Ring>>, mut output: SubmatrixMut<V2, El<Self::Ring>>)
        where V1: AsPointerToSlice<El<Self::Ring>>,
            V2: AsPointerToSlice<El<Self::Ring>>
    {
        {
            assert_eq!(input.row_count(), self.input_rings().len());
            assert_eq!(output.row_count(), self.output_rings().len());
            assert_eq!(input.col_count(), output.col_count());

            let in_len = input.row_count();
            let out_len = output.row_count();
            let col_count = input.col_count();

            let int_to_homs = (0..self.output_rings().len()).map(|k| self.output_rings().at(k).can_hom(&ZZi128).unwrap()).collect::<Vec<_>>();

            let mut lifts = OwnedMatrix::from_fn_in(pad_to_block(in_len), pad_to_block(col_count), |_, _| 0, self.allocator.clone());
            let mut lifts = lifts.data_mut();

            for i in 0..in_len {
                for j in 0..col_count {
                    *lifts.at_mut(i, j) = self.from_summands[i].any_lift(self.from_summands[i].mul_ref(input.at(i, j), self.q_over_Q.at(i)));
                    debug_assert!(*lifts.at(i, 0) >= 0 && *lifts.at(i, 0) as i128 <= ZN_ANY_LIFT_FACTOR as i128 * *self.from_summands[i].modulus() as i128);
                }
            }

            let mut output_unreduced = OwnedMatrix::zero(pad_to_block(out_len), pad_to_block(col_count), ZZi128);

            assert_eq!(0, self.Q_over_q_mod.row_count() % BLOCK_SIZE);
            assert_eq!(0, self.Q_over_q_mod.col_count() % BLOCK_SIZE);
            assert_eq!(0, output_unreduced.row_count() % BLOCK_SIZE);
            assert_eq!(0, lifts.row_count() % BLOCK_SIZE);
            for (lhs_blocks, mut res_block) in self.Q_over_q_mod.data().row_iter().array_chunks::<BLOCK_SIZE>().zip(
                output_unreduced.data_mut().row_iter().array_chunks::<BLOCK_SIZE>()
            ) {
                for (j, rhs_block) in lifts.as_const().row_iter().array_chunks::<BLOCK_SIZE>().enumerate() {
                    matmul_4x4_i64_to_i128(
                        from_fn(|i| &lhs_blocks[i].as_chunks::<BLOCK_SIZE>().0[j]), 
                        rhs_block, 
                        &mut res_block);
                }
            }

            let mut output_correction: Vec<i128> = (0..pad_to_block(col_count)).map(|_| 0).collect();
            assert_eq!(0, self.Q_over_q_downscaled.len() % BLOCK_SIZE);
            for (lhs_block, rhs_block) in self.Q_over_q_downscaled.iter().copied().array_chunks::<BLOCK_SIZE>().zip(
                lifts.as_const().row_iter().array_chunks::<BLOCK_SIZE>()
            ) {
                vecmatmul_4_i128_to_i128(lhs_block, rhs_block, &mut output_correction);
            }

            for j in 0..col_count {
                let mut correction = *output_correction.at(j);
                correction = ZZi128.rounded_div(correction, &self.gamma);

                for i in 0..out_len {
                    *output.at_mut(i, j) = self.to_summands[i].sub(
                        int_to_homs.at(i).map_ref(output_unreduced.at(i, j)), 
                        self.to_summands[i].mul_ref_snd(int_to_homs[i].map(correction), &self.Q_mod_q[i])
                    );
                }
            }
        }
    }
}

#[cfg(test)]
use feanor_math::{assert_el_eq, assert_matrix_eq};
#[cfg(test)]
use test::Bencher;
#[cfg(test)]
use feanor_math::algorithms::miller_rabin::is_prime;
#[cfg(test)]
use feanor_math::rings::finite::FiniteRingStore;
#[cfg(test)]
use feanor_math::primitive_int::StaticRing;

#[cfg(test)]
fn check_almost_exact_result(to: &[Zn], k: i32, q: i32, actual: &[ZnEl], expected: &[ZnEl]) {
    for j in 0..to.len() {
        assert!(
            to.at(j).is_zero(&to.at(j).sub_ref(expected.at(j), actual.at(j))) || 
                to.at(j).eq_el(&to.at(j).sub_ref(expected.at(j), actual.at(j)), &to.at(j).int_hom().map(q)) ||
                to.at(j).eq_el(&to.at(j).sub_ref(expected.at(j), actual.at(j)), &to.at(j).int_hom().map(-q)),
            "Expected {} to be {} +/- {}, input was {}",
            to.at(j).format(actual.at(j)),
            to.at(j).format(expected.at(j)),
            q,
            k
        );
    }
}

#[test]
fn test_matmul() {
    let mat_data = (0..(BLOCK_SIZE * BLOCK_SIZE)).map(|x| x as i64).collect::<Vec<_>>();
    let mat = mat_data.as_chunks::<BLOCK_SIZE>().0.iter().array_chunks::<BLOCK_SIZE>().next().unwrap();

    let mut res_data = (0..(BLOCK_SIZE * BLOCK_SIZE)).map(|x| x as i128).collect::<Vec<_>>();
    let mut res = res_data.chunks_mut(BLOCK_SIZE).array_chunks::<BLOCK_SIZE>().next().unwrap();

    matmul_4x4_i64_to_i128(mat, from_fn(|i| &mat[i][..]), &mut res);

    let expected = [
        [56, 63, 70, 77],
        [156, 179, 202, 225],
        [256, 295, 334, 373],
        [356, 411, 466, 521]
    ];
    assert_matrix_eq!(ZZi128, expected, from_fn::<_, BLOCK_SIZE, _>(|i| res[i].as_chunks::<BLOCK_SIZE>().0[0]));
}

#[test]
fn test_empty_rns_base_conversion() {
    let from = vec![];
    let to = vec![Zn::new(17), Zn::new(257)];

    let table = AlmostExactMatrixBaseConversion::new_with_alloc(from.clone(), to.clone(), Global);

    let mut actual = to.iter().map(|Zn| Zn.one()).collect::<Vec<_>>();
    table.apply(Submatrix::from_1d(&[], from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));
    for j in 0..to.len() {
        assert_el_eq!(to.at(j), to.at(j).zero(), actual.at(j));
    }

    let from = vec![Zn::new(17), Zn::new(257)];
    let to = vec![];

    let table = AlmostExactMatrixBaseConversion::new_with_alloc(from.clone(), to.clone(), Global);

    let input = from.iter().map(|Zn| Zn.one()).collect::<Vec<_>>();
    table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut [], to.len(), 1));
}

#[test]
fn test_rns_base_conversion() {
    let from = vec![Zn::new(17), Zn::new(97)];
    let to = vec![Zn::new(17), Zn::new(97), Zn::new(113), Zn::new(257)];
    let q = 17 * 97;

    let table = AlmostExactMatrixBaseConversion::new_with_alloc(from.clone(), to.clone(), Global);

    for k in (-q/2)..=(q/2) {
        let input = from.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();

        table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));

        check_almost_exact_result(&to, k, q, &actual, &expected);
    }
    
    for k in -(q/4)..=(q/4) {
        let input = from.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();

        table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));

        for j in 0..to.len() {
            assert_el_eq!(to.at(j), expected.at(j), actual.at(j));
        }
    }
}

#[test]
fn test_rns_base_conversion_both_unordered() {
    let from = vec![Zn::new(31), Zn::new(29)];
    let to = vec![Zn::new(5), Zn::new(17), Zn::new(23), Zn::new(19)];
    let q = 31 * 29;
    let table = AlmostExactMatrixBaseConversion::new_with_alloc(from.clone(), to.clone(), Global);

    for k in -(q/2)..=(q/2) {
        let input = from.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let expected = to.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|ring| ring.zero()).collect::<Vec<_>>();

        table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));

        check_almost_exact_result(&to, k, q, &actual, &expected);
    }
}

#[test]
fn test_rns_base_conversion_small() {
    let from = vec![Zn::new(3), Zn::new(97)];
    let to = vec![Zn::new(17)];
    let q = 3 * 97;

    let table = AlmostExactMatrixBaseConversion::new_with_alloc(from.clone(), to.clone(), Global);
    
    for k in -(q/2)..=(q/2) {
        let input = from.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let expected = to.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|ring| ring.zero()).collect::<Vec<_>>();

        table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));

        check_almost_exact_result(&to, k, q, &actual, &expected);
    }
}

#[test]
fn test_rns_base_conversion_not_coprime() {
    let from = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    let to = vec![Zn::new(17), Zn::new(97), Zn::new(113), Zn::new(257)];
    let q = 17 * 97 * 113;

    let table = AlmostExactMatrixBaseConversion::new_with_alloc(from.clone(), to.clone(), Global);

    for k in -(q/4)..=(q/4) {
        let input = from.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let expected = to.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|ring| ring.zero()).collect::<Vec<_>>();

        table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));

        for i in 0..to.len() {
            assert_el_eq!(to[i], expected[i], actual.at(i));
        }
    }
}

#[test]
fn test_rns_base_conversion_not_coprime_from_unordered() {
    let from = vec![Zn::new(113), Zn::new(17), Zn::new(97)];
    let to = vec![Zn::new(17), Zn::new(97), Zn::new(113), Zn::new(257)];
    let q = 113 * 17 * 97;

    let table = AlmostExactMatrixBaseConversion::new_with_alloc(from.clone(), to.clone(), Global);

    for k in -(q/4)..=(q/4) {
        let input = from.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let expected = to.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|ring| ring.zero()).collect::<Vec<_>>();

        table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));

        for i in 0..to.len() {
            assert_el_eq!(to[i], expected[i], actual.at(i));
        }
    }
}

#[test]
fn test_rns_base_conversion_coprime() {
    let from = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    let to = vec![Zn::new(19), Zn::new(23), Zn::new(257)];
    let q = 113 * 17 * 97;

    let table = AlmostExactMatrixBaseConversion::new_with_alloc(from.clone(), to.clone(), Global);

    for k in -(q/4)..=(q/4) {
        let input = from.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let expected = to.iter().map(|ring| ring.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|ring| ring.zero()).collect::<Vec<_>>();

        table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));

        for i in 0..to.len() {
            assert_el_eq!(to[i], expected[i], actual.at(i));
        }
    }
}

#[bench]
fn bench_rns_base_conversion(bencher: &mut Bencher) {
    let in_moduli_count = 20;
    let out_moduli_count = 40;
    let cols = 1000;
    let mut primes = ((1 << 30)..).map(|k| (1 << 10) * k + 1).filter(|p| is_prime(&StaticRing::<i64>::RING, p, 10)).map(|p| Zn::new(p as u64));
    let in_moduli = primes.by_ref().take(in_moduli_count).collect::<Vec<_>>();
    let out_moduli = primes.take(out_moduli_count).collect::<Vec<_>>();
    let conv = AlmostExactMatrixBaseConversion::new_with_alloc(in_moduli.clone(), out_moduli.clone(), Global);
    
    let mut rng = oorandom::Rand64::new(1);
    let mut in_data = (0..(in_moduli_count * cols)).map(|idx| in_moduli[idx / cols].zero()).collect::<Vec<_>>();
    let mut in_matrix = SubmatrixMut::from_1d(&mut in_data, in_moduli_count, cols);
    let mut out_data = (0..(out_moduli_count * cols)).map(|idx| out_moduli[idx / cols].zero()).collect::<Vec<_>>();
    let mut out_matrix = SubmatrixMut::from_1d(&mut out_data, out_moduli_count, cols);

    bencher.iter(|| {
        for i in 0..in_moduli_count {
            for j in 0..cols {
                *in_matrix.at_mut(i, j) = in_moduli[i].random_element(|| rng.rand_u64());
            }
        }
        conv.apply(in_matrix.as_const(), out_matrix.reborrow());
        for i in 0..out_moduli_count {
            for j in 0..cols {
                std::hint::black_box(out_matrix.at(i, j));
            }
        }
    });
}

#[test]
fn test_base_conversion_large() {
    let primes: [i64; 34] = [
        72057594040066049,
        288230376150870017,
        288230376150876161,
        288230376150878209,
        288230376150890497,
        288230376150945793,
        288230376150956033,
        288230376151062529,
        288230376151123969,
        288230376151130113,
        288230376151191553,
        288230376151388161,
        288230376151422977,
        288230376151529473,
        288230376151545857,
        288230376151554049,
        288230376151601153,
        288230376151625729,
        288230376151683073,
        288230376151748609,
        288230376151760897,
        288230376151779329,
        288230376151812097,
        288230376151902209,
        288230376151951361,
        288230376151994369,
        288230376152027137,
        288230376152061953,
        288230376152137729,
        288230376152154113,
        288230376152156161,
        288230376152205313,
        288230376152227841,
        288230376152340481,
    ];
    let in_len = 17;
    let from = &primes[..in_len];
    let from_prod = ZZbig.prod(from.iter().map(|p| int_cast(*p, ZZbig, StaticRing::<i64>::RING)));
    let to = &primes[in_len..];
    let number = ZZbig.get_ring().parse("156545561910861509258548850310120795193837265771491906959215072510998373539323526014165281634346450795208120921520265422129013635769405993324585707811035953253906720513250161495607960734366886366296007741500531044904559075687514262946086011957808717474666493477109586105297965072817051127737667010", 10).unwrap();
    assert!(ZZbig.is_lt(&number, &from_prod));
    
    let from = from.iter().map(|p| Zn::new(*p as u64)).collect::<Vec<_>>();
    let to = to.iter().map(|p| Zn::new(*p as u64)).collect::<Vec<_>>();
    let conversion = AlmostExactMatrixBaseConversion::new_with_alloc(from, to.clone(), Global);

    let input = (0..in_len).map(|i| conversion.input_rings().at(i).coerce(&ZZbig, ZZbig.clone_el(&number))).collect::<Vec<_>>();
    let expected = (0..(primes.len() - in_len)).map(|i| conversion.output_rings().at(i).coerce(&ZZbig, ZZbig.clone_el(&number))).collect::<Vec<_>>();
    let mut output = (0..(primes.len() - in_len)).map(|i| conversion.output_rings().at(i).zero()).collect::<Vec<_>>();
    conversion.apply(Submatrix::from_1d(&input, in_len, 1), SubmatrixMut::from_1d(&mut output, primes.len() - in_len, 1));

    for j in 0..to.len() {
        assert!(
            to.at(j).is_zero(&to.at(j).sub_ref(expected.at(j), output.at(j))) || 
                to.at(j).eq_el(&to.at(j).sub_ref(expected.at(j), output.at(j)), &to.at(j).coerce(&ZZbig, ZZbig.clone_el(&from_prod))) ||
                to.at(j).eq_el(&to.at(j).sub_ref(expected.at(j), output.at(j)), &to.at(j).negate(to.at(j).coerce(&ZZbig, ZZbig.clone_el(&from_prod)))),
            "Expected {} to be {} +/- {}",
            to.at(j).format(output.at(j)),
            to.at(j).format(expected.at(j)),
            ZZbig.format(&from_prod)
        );
    }
}