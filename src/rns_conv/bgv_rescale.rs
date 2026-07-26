use std::mem::MaybeUninit;

use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::homomorphism::*;
use feanor_math::integer::int_cast;
use feanor_math::matrix::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::rings::zn::*;
use rayon_cond::CondIterator;
use tracing::{Level, Span, instrument, span};

use crate::rns_conv::matmul_kernel::BLOCK;
use crate::rns_conv::{RNSOperation, UsedBaseConversion};
use crate::{SCRATCH_ALLOCATOR, ZZbig, ZZi64, is_parallel};

/// Computes the base conversion that preserves the congruence modulo some `t` in a certain sense,
/// which is required during BGV modulus-switching.
///
/// Concretely, the image `y` of `x` is the almost-smallest integer that is `= x mod b` and `= 0 mod
/// t`. In particular, assuming that `b | q`, we compute the map
/// ```text
///   Z/bZ -> Z/qZ,  x -> lift*(x) - b lift(lift*(x) b^-1 mod t)
/// ```
/// To allow an efficient RNS implementation, we allow `lift*` to make an error of `+/- b`.
/// Hence, "almost-smallest" could be the smallest, or second-smallest integer if there is
/// almost a tie.
pub struct RNSCongruencePreservingBaseConversion {
    /// ordered as supplied when instantiating the object
    b_moduli: Vec<Zn>,
    /// moduli corresponding to `qt`
    intermediate_moduli: Vec<Zn>,
    /// the first this many moduli of `intermediate_moduli` are the output moduli
    q_moduli_count: usize,
    /// moduli of `q` are sorted as in `intermediate_moduli`
    b_to_intermediate_lift: UsedBaseConversion,
    /// `b^-1` as an element of `Z/tZ`
    b_inv_mod_t: El<Zn>,
    /// `b` as an element of `Z/qZ`
    b_mod_q: Vec<El<Zn>>,
}

impl RNSCongruencePreservingBaseConversion {
    /// Creates a new [`RNSCongruencePreservingBaseConversion`], where
    ///  - `b` is the product of the moduli in `in_moduli`
    ///  - `q` is the product of the moduli in `out_moduli`
    ///  - `t` is the modulus of `plaintext_modulus`
    pub fn new(in_moduli: Vec<Zn>, out_moduli: Vec<Zn>, plaintext_modulus: Zn) -> Self {
        let ZZ = plaintext_modulus.integer_ring();
        for ring in &in_moduli {
            assert!(ring.integer_ring().get_ring() == ZZ.get_ring());
        }
        for ring in &out_moduli {
            assert!(ring.integer_ring().get_ring() == ZZ.get_ring());
        }

        let b = ZZbig.prod(
            in_moduli
                .iter()
                .map(|rns_factor| int_cast(ZZ.clone_el(rns_factor.modulus()), &ZZbig, ZZ)),
        );

        let b_moduli = in_moduli.clone();
        let q_moduli_count = out_moduli.len();
        let mut intermediate_moduli = out_moduli;
        intermediate_moduli.push(plaintext_modulus);

        Self {
            intermediate_moduli: intermediate_moduli.clone(),
            q_moduli_count,
            b_mod_q: intermediate_moduli[..q_moduli_count]
                .iter()
                .map(|rns_factor| rns_factor.coerce(&ZZbig, ZZbig.clone_el(&b)))
                .collect(),
            b_inv_mod_t: plaintext_modulus.invert(&plaintext_modulus.coerce(&ZZbig, b)).unwrap(),
            b_to_intermediate_lift: UsedBaseConversion::new(b_moduli.clone(), intermediate_moduli.clone()),
            b_moduli,
        }
    }

    pub fn t_modulus(&self) -> &Zn { self.intermediate_moduli.last().unwrap() }
}

impl RNSOperation for RNSCongruencePreservingBaseConversion {
    type Ring = Zn;

    type RingType = ZnBase;

    fn input_rings<'a>(&'a self) -> &'a [Zn] { &self.b_moduli }

    fn output_rings<'a>(&'a self) -> &'a [Zn] { &self.intermediate_moduli[..self.q_moduli_count] }

    #[instrument(skip_all)]
    fn apply<'a, V1, V2>(
        &self,
        input: Submatrix<V1, El<Self::Ring>>,
        mut output: SubmatrixMut<'a, V2, MaybeUninit<El<Self::Ring>>>,
    ) -> SubmatrixMut<'a, V2, El<Self::Ring>>
    where
        V1: Sync + AsPointerToSlice<El<Self::Ring>>,
        V2: Sync + AsPointerToSlice<El<Self::Ring>> + AsPointerToSlice<MaybeUninit<El<Self::Ring>>>,
    {
        // `input` is ordered as in `b_moduli`
        assert_eq!(input.row_count(), self.input_rings().len());
        assert_eq!(output.row_count(), self.output_rings().len());
        assert_eq!(input.col_count(), output.col_count());
        let Zt = self.t_modulus();

        // Compute `lift(x) mod intermediate`
        let mut x_lift = OwnedMatrix::uninit_in(self.intermediate_moduli.len(), input.col_count(), &SCRATCH_ALLOCATOR);
        let x_lift = self.b_to_intermediate_lift.apply(input, x_lift.data_mut());

        // now compute `lift(x_lift b^-1 mod t)`, which we use to take care of the congruence modulo `t`
        // later; because of the helper moduli, this is small enough not to cause any error
        let row_count = x_lift.row_count();
        let (x_mod_q, mut x_mod_t) = x_lift.split_rows(0..(row_count - 1), (row_count - 1)..row_count);
        for j in 0..input.col_count() {
            Zt.mul_assign_ref(x_mod_t.at_mut(0, j), &self.b_inv_mod_t);
        }
        let mod_t_correction = x_mod_t;

        let mut tasks = Vec::with_capacity(input.col_count().div_ceil(BLOCK));
        let mut out_current = output.reborrow();
        while out_current.col_count() > BLOCK {
            let fst_col_count = out_current.col_count();
            let (part, rest) = out_current.split_cols(0..BLOCK, BLOCK..fst_col_count);
            tasks.push(part);
            out_current = rest;
        }
        tasks.push(out_current);

        // compute the result as `x_mod_q - b * mod_t_correction`
        let outer_span = Span::current();
        CondIterator::new(tasks, is_parallel())
            .enumerate()
            .for_each(|(j_base, mut out)| {
                span!(parent: &outer_span, Level::INFO, "rescale_stage1_block").in_scope(|| {
                    for i in 0..self.q_moduli_count {
                        debug_assert!(self.intermediate_moduli[i].get_ring() == self.output_rings()[i].get_ring());
                        let Zp = &self.intermediate_moduli[i];
                        let b_mod_p = self.b_mod_q[i];

                        if Zt.modulus() <= Zp.modulus() {
                            let t = *Zt.modulus();
                            let neg_t_Zp = Zp.coerce(&ZZi64, -t);
                            for j in 0..out.col_count() {
                                let val = Zt.smallest_lift(*mod_t_correction.at(0, j + j_base * BLOCK));
                                let correction = if val < 0 {
                                    Zp.add(Zp.get_ring().from_int_promise_reduced(val + t), neg_t_Zp)
                                } else {
                                    Zp.get_ring().from_int_promise_reduced(val)
                                };
                                *out.at_mut(i, j) = MaybeUninit::new(
                                    Zp.sub(*x_mod_q.at(i, j + j_base * BLOCK), Zp.mul(correction, b_mod_p)),
                                );
                            }
                        } else {
                            let mod_p = Zp.can_hom(&ZZi64).unwrap();
                            for j in 0..out.col_count() {
                                let correction =
                                    mod_p.map(Zt.smallest_lift(*mod_t_correction.at(0, j + j_base * BLOCK)));
                                *out.at_mut(i, j) = MaybeUninit::new(
                                    Zp.sub(*x_mod_q.at(i, j + j_base * BLOCK), Zp.mul(correction, b_mod_p)),
                                );
                            }
                        }
                    }
                })
            });
        // SAFETY: we just initialized it
        return unsafe { output.assume_init() };
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::seq::*;

#[test]
fn test_congruence_preserving_baseconv_small() {
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(23)];
    let to = vec![Zn::new(17), Zn::new(29)];
    let Zt = Zn::new(5);
    let Zb = Zn::new(23);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;

    let baseconv = RNSCongruencePreservingBaseConversion::new(from.clone(), to.clone(), Zt.clone());

    let ZZ_to_Zt = Zt.int_hom();
    let ZZ_to_Zb = Zb.int_hom();

    for i in -(b / 2)..=(b / 2) {
        let input = i;
        let input_mod_b = Zb.smallest_lift(ZZ_to_Zb.map(input)) as i32;
        let expected = input_mod_b
            - b * Zt.smallest_lift(Zt.checked_div(&ZZ_to_Zt.map(input_mod_b), &ZZ_to_Zt.map(b)).unwrap()) as i32;
        assert_el_eq!(&Zb, ZZ_to_Zb.map(input), ZZ_to_Zb.map(expected));
        assert_eq!(0, expected % t);
        assert!(expected.abs() <= b * t / 2);

        let input = from.iter().map(|Zn| Zn.int_hom().map(input)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|_| MaybeUninit::uninit()).collect::<Vec<_>>();

        let actual = baseconv.apply(
            Submatrix::from_1d(&input, 1, 1),
            SubmatrixMut::from_1d(&mut actual, 2, 1),
        );

        for j in 0..expected.len() {
            // we currently assume no error happens
            assert_el_eq!(to.at(j), expected.at(j), actual.at(j, 0));
        }
    }
}

#[test]
fn test_congruence_preserving_baseconv_two_denominators() {
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(23), Zn::new(7)];
    let to = vec![Zn::new(17), Zn::new(5), Zn::new(11)];
    let Zt = Zn::new(3);
    let Zb = Zn::new(23 * 7);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;

    let baseconv = RNSCongruencePreservingBaseConversion::new(from.clone(), to.clone(), Zt.clone());

    let ZZ_to_Zt = Zt.int_hom();
    let ZZ_to_Zb = Zb.int_hom();

    for i in -(b / 2)..=(b / 2) {
        let input = i;
        let input_mod_b = Zb.smallest_lift(ZZ_to_Zb.map(input)) as i32;
        let expected = input_mod_b
            - b * Zt.smallest_lift(Zt.checked_div(&ZZ_to_Zt.map(input_mod_b), &ZZ_to_Zt.map(b)).unwrap()) as i32;
        assert_el_eq!(&Zb, ZZ_to_Zb.map(input), ZZ_to_Zb.map(expected));
        assert_eq!(0, expected % t);
        assert!(expected.abs() <= b * t / 2);

        let input = from.iter().map(|Zn| Zn.int_hom().map(input)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|_| MaybeUninit::uninit()).collect::<Vec<_>>();

        let actual = baseconv.apply(
            Submatrix::from_1d(&input, 2, 1),
            SubmatrixMut::from_1d(&mut actual, 3, 1),
        );

        for j in 0..expected.len() {
            // we currently assume no error happens
            assert_el_eq!(to.at(j), expected.at(j), actual.at(j, 0));
        }
    }
}

#[test]
fn test_congruence_preserving_baseconv_unordered() {
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(19), Zn::new(7), Zn::new(13)];
    let to = vec![Zn::new(17), Zn::new(5), Zn::new(3)];
    let Zt = Zn::new(11);
    let Zb = Zn::new(19 * 7 * 13);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;

    let baseconv = RNSCongruencePreservingBaseConversion::new(from.clone(), to.clone(), Zt.clone());

    let ZZ_to_Zt = Zt.int_hom();
    let ZZ_to_Zb = Zb.int_hom();

    for i in -(b / 2)..=(b / 2) {
        let input = i;
        let input_mod_b = Zb.smallest_lift(ZZ_to_Zb.map(input)) as i32;
        let expected = input_mod_b
            - b * Zt.smallest_lift(Zt.checked_div(&ZZ_to_Zt.map(input_mod_b), &ZZ_to_Zt.map(b)).unwrap()) as i32;
        assert_el_eq!(&Zb, ZZ_to_Zb.map(input), ZZ_to_Zb.map(expected));
        assert_eq!(0, expected % t);
        assert!(expected.abs() <= b * t / 2);

        let input = from.iter().map(|Zn| Zn.int_hom().map(input)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|_| MaybeUninit::uninit()).collect::<Vec<_>>();

        let actual = baseconv.apply(
            Submatrix::from_1d(&input, 3, 1),
            SubmatrixMut::from_1d(&mut actual, 3, 1),
        );

        for j in 0..expected.len() {
            // we currently assume no error happens
            assert_el_eq!(to.at(j), expected.at(j), actual.at(j, 0));
        }
    }
}
