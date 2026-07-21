use feanor_math::integer::*;
use feanor_math::matrix::*;
use feanor_math::homomorphism::*;
use feanor_math::seq::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::ring::*;
use feanor_math::ordered::OrderedRingStore;
use rayon_cond::CondIterator;
use tracing::Level;
use tracing::Span;
use tracing::instrument;
use tracing::span;

use std::slice::from_ref;

use crate::is_parallel;
use crate::rns_conv::matmul_kernel::BLOCK;
use crate::rns_conv::matmul_kernel::skinny_matmul_i64_i64_i128_block;
use crate::rns_conv::matmul_kernel::skinny_matmul_i128_i64_i128_block;
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
/// Similar to (the now deprecated) [`RNSBaseConversion`], but this implementation
/// writes the operation as integer matrix multiplication, and is usually more efficient.
/// 
/// [`RNSBaseConversion`]: crate::rns_conv::bconv::RNSBaseConversion
/// 
pub struct RNSBaseConversion(RNSMatrixBaseConversionEnum);

enum RNSMatrixBaseConversionEnum {
    General(GeneralRNSMatrixBaseConversion),
    SingleIn(SingleInRNSMatrixBaseConversion)
}

struct GeneralRNSMatrixBaseConversion {
    from_moduli: Vec<Zn>,
    to_moduli: Vec<Zn>,
    /// the values `q/Q mod q` for each RNS factor q dividing Q (ordered as `from_summands`)
    q_over_Q: Vec<ZnEl>,
    /// shortest lifts of the values `Q/q mod q'` for each RNS factor q dividing Q (ordered 
    /// as `from_summands`, mapped to col index) and q' dividing Q' (ordered as `to_summands`,
    /// mapped to row index)
    Q_over_q_mod: OwnedMatrix<i64>,
    /// the values `round( Q/q/gamma )` for each RNS factor `q` dividing `Q`; Unfortunately,
    /// these sometimes exceed 64 bits, thus cannot store them in the matrix `Q_over_q_mod`
    Q_over_q_downscaled: Vec<i128>,
    log2_gamma: usize,
    /// `Q mod q'` for every RNS factor q' of Q' (ordered as `to_summands`)
    Q_mod_q: Vec<ZnEl>

}

struct SingleInRNSMatrixBaseConversion {
    from_modulus: Zn,
    to_moduli: Vec<Zn>
}

// we currently use `any_lift()`; I haven't yet documented it anywhere, but in fact the largest output of `zn_64::Zn::any_lift()` is currently `6 * modulus()`
const ZN_ANY_LIFT_FACTOR: i64 = 6;

impl RNSBaseConversion {

    ///
    /// Creates a new [`RNSBaseConversion`] from `q` to `q'`.
    /// 
    pub fn new(in_rings: Vec<Zn>, out_rings: Vec<Zn>) -> Self {
        if in_rings.len() == 1 {
            Self(RNSMatrixBaseConversionEnum::SingleIn(SingleInRNSMatrixBaseConversion { from_modulus: in_rings[0], to_moduli: out_rings }))
        } else {
            Self(RNSMatrixBaseConversionEnum::General(GeneralRNSMatrixBaseConversion::new(in_rings, out_rings)))
        }
    }
}

impl GeneralRNSMatrixBaseConversion {
    ///
    /// Creates a new [`RNSMatrixBaseConversion`] from `q` to `q'`.
    /// 
    #[instrument(skip_all)]
    fn new(in_rings: Vec<Zn>, out_rings: Vec<Zn>) -> Self {
        
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
        let log2_gamma = ZZbig.abs_log2_ceil(&gamma).unwrap();
        assert!(log2_gamma == ZZbig.abs_log2_floor(&gamma).unwrap());

        let Q_over_q_mod = OwnedMatrix::from_fn(out_rings.len(), in_rings.len(), |i, j| {
            if i < out_rings.len() && j < in_rings.len() {
                let ring = out_rings.at(i);
                ring.smallest_lift(ring.coerce(&ZZbig, ZZbig.checked_div(&Q, &int_cast(*in_rings.at(j).modulus(), ZZbig, ZZi64)).unwrap()))
            } else {
                0
            }
        });
        let Q_over_q_downscaled = (0..in_rings.len()).map(|j| if j < in_rings.len() {
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
            log2_gamma: log2_gamma,
            from_moduli: in_rings,
            to_moduli: out_rings
        }
    }

    fn stage1<V1, V2, V3>(
        &self,
        input: Submatrix<V1, ZnEl>,
        mut lifts: SubmatrixMut<V2, i64>,
        mut out: SubmatrixMut<V3, i128>,
        mut correction: &mut [i128]
    ) 
        where V1: Sync + AsPointerToSlice<ZnEl>,
            V2: Sync + AsPointerToSlice<i64>,
            V3: Sync + AsPointerToSlice<i128>
    {
        let in_len = lifts.row_count();
        assert_eq!(in_len, input.row_count());
        let col_count = lifts.col_count();
        assert_eq!(col_count, out.col_count());

        let mut tasks = Vec::with_capacity(col_count.div_ceil(BLOCK));
        while out.col_count() > BLOCK {
            let out_col_count = out.col_count();
            let (out_part, out_rest) = out.split_cols(0..BLOCK, BLOCK..out_col_count);
            let (lifts_part, lifts_rest) = lifts.split_cols(0..BLOCK, BLOCK..out_col_count);
            let (correction_part, correction_rest) = correction.split_at_mut(BLOCK);
            tasks.push((lifts_part, out_part, correction_part));
            out = out_rest;
            lifts = lifts_rest;
            correction = correction_rest;
        }
        tasks.push((lifts, out, correction));

        let outer_span = Span::current();
        CondIterator::new(tasks, is_parallel()).enumerate().for_each(|(j_base, (mut lifts, out, correction))| span!(parent: &outer_span, Level::INFO, "bconv_stage1_block").in_scope(|| {
            for i in 0..in_len {
                for j in 0..lifts.col_count() {
                    *lifts.at_mut(i, j) = self.from_moduli[i].any_lift(self.from_moduli[i].mul_ref(input.at(i, j + j_base * BLOCK), self.q_over_Q.at(i)));
                    debug_assert!(*lifts.at(i, 0) >= 0 && *lifts.at(i, 0) as i128 <= ZN_ANY_LIFT_FACTOR as i128 * *self.from_moduli[i].modulus() as i128);
                }
            }
            skinny_matmul_i64_i64_i128_block(
                self.Q_over_q_mod.data(),
                lifts.as_const(),
                out
            );
            skinny_matmul_i128_i64_i128_block(
                Submatrix::from_1d(&self.Q_over_q_downscaled, 1, in_len), 
                lifts.as_const(),
                SubmatrixMut::from_1d(correction, 1, lifts.col_count()) 
            );
        }));
    }

    fn stage2<V1, V2>(
        &self,
        correction: &[i128],
        output_unreduced: Submatrix<V1, i128>,
        mut out: SubmatrixMut<V2, ZnEl>,
    ) 
        where V1: Sync + AsPointerToSlice<i128>,
            V2: Sync + AsPointerToSlice<ZnEl>
    {
        let out_len = output_unreduced.row_count();
        assert_eq!(out_len, out.row_count());
        let col_count = output_unreduced.col_count();
        assert_eq!(col_count, out.col_count());
        let half = 1i128 << (self.log2_gamma - 1);
        let i128_to_homs = (0..self.to_moduli.len()).map(|k| self.to_moduli.at(k).can_hom(&ZZi128).unwrap()).collect::<Vec<_>>();
        let i64_to_homs = (0..self.to_moduli.len()).map(|k| self.to_moduli.at(k).can_hom(&ZZi64).unwrap()).collect::<Vec<_>>();

        let mut tasks = Vec::with_capacity(col_count.div_ceil(BLOCK));
        while out.col_count() > BLOCK {
            let out_col_count = out.col_count();
            let (current, rest) = out.split_cols(0..BLOCK, BLOCK..out_col_count);
            tasks.push(current);
            out = rest;
        }
        tasks.push(out);

        let outer_span = Span::current();
        CondIterator::new(tasks, is_parallel()).enumerate().for_each(|(j_base, mut out)| span!(parent: &outer_span, Level::INFO, "bconv_stage2_block").in_scope(|| {
            for j in 0..out.col_count() {
                let correction = i64::try_from((correction.at(j_base * BLOCK + j) + half) >> &self.log2_gamma).unwrap();
                for i in 0..out_len {
                    *out.at_mut(i, j) = self.to_moduli[i].sub(
                        i128_to_homs.at(i).map_ref(output_unreduced.at(i, j + j_base * BLOCK)), 
                        self.to_moduli[i].mul_ref_snd(i64_to_homs[i].map(correction), &self.Q_mod_q[i])
                    );
                }
            }
        }));
        
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
    fn convert_base<V1, V2>(&self, input: Submatrix<V1, El<Zn>>, output: SubmatrixMut<V2, El<Zn>>)
        where V1: Sync + AsPointerToSlice<El<Zn>>,
            V2: Sync + AsPointerToSlice<El<Zn>>
    {
        assert_eq!(input.row_count(), self.from_moduli.len());
        assert_eq!(output.row_count(), self.to_moduli.len());
        assert_eq!(input.col_count(), output.col_count());

        let in_len = input.row_count();
        let out_len = output.row_count();
        let col_count = input.col_count();
        let mut lifts = OwnedMatrix::zero(in_len, col_count, ZZi64);
        let mut output_unreduced = OwnedMatrix::zero(out_len, col_count, ZZi128);
        let mut corrections: Vec<i128> = (0..col_count).map(|_| 0).collect();

        self.stage1(input, lifts.data_mut(), output_unreduced.data_mut(), &mut corrections);

        self.stage2(&corrections, output_unreduced.data(), output);
    }
}

impl SingleInRNSMatrixBaseConversion {

    #[instrument(skip_all)]
    fn convert_base<V1, V2>(&self, input: Submatrix<V1, El<Zn>>, mut output: SubmatrixMut<V2, El<Zn>>)
        where V1: AsPointerToSlice<El<Zn>>,
            V2: AsPointerToSlice<El<Zn>>
    {
        assert_eq!(input.row_count(), 1);
        assert_eq!(output.row_count(), self.to_moduli.len());
        assert_eq!(input.col_count(), output.col_count());

        let mut lifts = Vec::with_capacity(output.col_count());
        lifts.extend(input.row_at(0).iter().map(|x| self.from_modulus.smallest_lift(*x)));

        for i in 0..output.row_count() {
            let Zp = &self.to_moduli[i];
            if self.from_modulus.modulus() <= Zp.modulus() {
                let from_modulus = *self.from_modulus.modulus();
                let neg_from_modulus_Zp = Zp.coerce(&ZZi64, -from_modulus);
                for j in 0..output.col_count() {
                    let val = lifts[j];
                    *output.at_mut(i, j) = if val < 0 {
                        Zp.add(Zp.get_ring().from_int_promise_reduced(val + from_modulus), neg_from_modulus_Zp)
                    } else {
                        Zp.get_ring().from_int_promise_reduced(val)
                    }
                }
            } else {
                let mod_p = Zp.can_hom(&ZZi64).unwrap();
                for j in 0..output.col_count() {
                    let val = lifts[j];
                    *output.at_mut(i, j) = mod_p.map(val);
                }
            }
        }
    }
}

impl RNSOperation for RNSBaseConversion {

    type Ring = Zn;

    type RingType = ZnBase;

    fn input_rings<'a>(&'a self) -> &'a [Zn] {
        match &self.0 {
            RNSMatrixBaseConversionEnum::General(rns_conv) => &rns_conv.from_moduli,
            RNSMatrixBaseConversionEnum::SingleIn(rns_conv) => from_ref(&rns_conv.from_modulus)
        }
    }

    fn output_rings<'a>(&'a self) -> &'a [Zn] {
        match &self.0 {
            RNSMatrixBaseConversionEnum::General(rns_conv) => &rns_conv.to_moduli,
            RNSMatrixBaseConversionEnum::SingleIn(rns_conv) => &rns_conv.to_moduli
        }
    }

    fn apply<V1, V2>(&self, input: Submatrix<V1, El<Self::Ring>>, output: SubmatrixMut<V2, El<Self::Ring>>)
        where V1: Sync + AsPointerToSlice<El<Self::Ring>>,
            V2: Sync + AsPointerToSlice<El<Self::Ring>>
    {
        match &self.0 {
            RNSMatrixBaseConversionEnum::General(rns_conv) => rns_conv.convert_base(input, output),
            RNSMatrixBaseConversionEnum::SingleIn(rns_conv) => rns_conv.convert_base(input, output),
        }
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
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
fn test_empty_rns_base_conversion() {
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![];
    let to = vec![Zn::new(17), Zn::new(257)];

    let table = RNSBaseConversion::new(from.clone(), to.clone());

    let mut actual = to.iter().map(|Zn| Zn.one()).collect::<Vec<_>>();
    table.apply(Submatrix::from_1d(&[], from.len(), 1), SubmatrixMut::from_1d(&mut actual, to.len(), 1));
    for j in 0..to.len() {
        assert_el_eq!(to.at(j), to.at(j).zero(), actual.at(j));
    }

    let from = vec![Zn::new(17), Zn::new(257)];
    let to = vec![];

    let table = RNSBaseConversion::new(from.clone(), to.clone());

    let input = from.iter().map(|Zn| Zn.one()).collect::<Vec<_>>();
    table.apply(Submatrix::from_1d(&input, from.len(), 1), SubmatrixMut::from_1d(&mut [], to.len(), 1));
}

#[test]
fn test_rns_base_conversion() {
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(17), Zn::new(97)];
    let to = vec![Zn::new(17), Zn::new(97), Zn::new(113), Zn::new(257)];
    let q = 17 * 97;

    let table = RNSBaseConversion::new(from.clone(), to.clone());

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
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(31), Zn::new(29)];
    let to = vec![Zn::new(5), Zn::new(17), Zn::new(23), Zn::new(19)];
    let q = 31 * 29;
    let table = RNSBaseConversion::new(from.clone(), to.clone());

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
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(3), Zn::new(97)];
    let to = vec![Zn::new(17)];
    let q = 3 * 97;

    let table = RNSBaseConversion::new(from.clone(), to.clone());
    
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
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    let to = vec![Zn::new(17), Zn::new(97), Zn::new(113), Zn::new(257)];
    let q = 17 * 97 * 113;

    let table = RNSBaseConversion::new(from.clone(), to.clone());

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
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(113), Zn::new(17), Zn::new(97)];
    let to = vec![Zn::new(17), Zn::new(97), Zn::new(113), Zn::new(257)];
    let q = 113 * 17 * 97;

    let table = RNSBaseConversion::new(from.clone(), to.clone());

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
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    let to = vec![Zn::new(19), Zn::new(23), Zn::new(257)];
    let q = 113 * 17 * 97;

    let table = RNSBaseConversion::new(from.clone(), to.clone());

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
    feanor_tracing::DelayedLogger::init_test();
    let in_moduli_count = 20;
    let out_moduli_count = 40;
    let cols = 1000;
    let mut primes = ((1 << 30)..).map(|k| (1 << 10) * k + 1).filter(|p| is_prime(&StaticRing::<i64>::RING, p, 10)).map(|p| Zn::new(p as u64));
    let in_moduli = primes.by_ref().take(in_moduli_count).collect::<Vec<_>>();
    let out_moduli = primes.take(out_moduli_count).collect::<Vec<_>>();
    let conv = RNSBaseConversion::new(in_moduli.clone(), out_moduli.clone());
    
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
    feanor_tracing::DelayedLogger::init_test();
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
    let conversion = RNSBaseConversion::new(from, to.clone());

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