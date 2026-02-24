use feanor_math::matrix::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::integer::*;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::ring::*;
use feanor_math::seq::*;
use tracing::instrument;

#[allow(unused)] // this import is used in test or debug_assertion builds
use feanor_math::homomorphism::*;

use std::alloc::{Allocator, Global};

use crate::rns_conv::{UsedBaseConversion, RNSOperation};
use crate::ZZbig;

///
/// Computes almost exact rescaling with final conversion.
/// The exact rescaling with conversion refers to the map
/// ```text
///   Z/qZ -> Z/q'Z, x -> round(lift(x) * a/b) mod b
/// ```
/// where `b | q` and `gcd(a, q) = 1`. We allow this implementation to
/// make an error of `+/- 1` in the result.
/// This requires that the shortest lift of the input is bounded by `q/4`.
/// 
/// # Use case
/// 
/// Primarily, this is relevant as it is used during multiplication for BFV.
/// In this case, we always have `q' = b`.
/// 
pub struct RNSRescalingConversion<A = Global>
    where A: Allocator + Clone
{
    /// rescale `Z/qZ -> Z/(aq/b)Z`
    rescaling: RNSRescaling<A>,
    /// convert `Z/(aq/b)Z -> Z/q'Z`
    convert: UsedBaseConversion<A>
}

impl RNSRescalingConversion {

    ///
    /// Creates a new [`RNSRescalingConversion`], where
    ///  - `q` is the product of `in_moduli`
    ///  - `q'` is the product of `out_moduli`
    ///  - `a` is the product of `a_moduli`
    ///  - `b` is the product of the moduli in `in_moduli` indexed by `b_moduli_indices`
    /// 
    pub fn new(in_moduli: Vec<Zn>, out_moduli: Vec<Zn>, a_moduli: Vec<Zn>, b_moduli_indices: Vec<usize>) -> Self {
        Self::new_with_alloc(in_moduli, out_moduli, a_moduli, b_moduli_indices, Global)
    }

}

impl<A> RNSRescalingConversion<A>
    where A: Allocator + Clone
{
    ///
    /// Creates a new [`RNSRescalingConversion`], where
    ///  - `q` is the product of `in_moduli`
    ///  - `q'` is the product of `out_moduli`
    ///  - `a` is the product of `a_moduli`
    ///  - `b` is the product of the moduli in `in_moduli` indexed by `b_moduli_indices`
    /// 
    #[instrument(skip_all)]
    pub fn new_with_alloc(in_moduli: Vec<Zn>, out_moduli: Vec<Zn>, a_moduli: Vec<Zn>, b_moduli_indices: Vec<usize>, allocator: A) -> Self {
        let intermediate_moduli: Vec<_> = in_moduli.iter().enumerate()
            .filter(|(i, _)| !b_moduli_indices.contains(i)).map(|(_, Zn)| Zn)
            .chain(a_moduli.iter())
            .cloned().collect();
        let rescaling = RNSRescaling::new_with_alloc(in_moduli.clone(), intermediate_moduli.clone(), allocator.clone());
        let convert = UsedBaseConversion::new_with_alloc(intermediate_moduli, out_moduli, allocator);
        return Self { rescaling, convert };
    }

    pub fn num(&self) -> &El<BigIntRing> {
        self.rescaling.num()
    }

    pub fn den(&self) -> &El<BigIntRing> {
        self.rescaling.den()
    }
}

impl<A> RNSOperation for RNSRescalingConversion<A>
    where A: Allocator + Clone
{
    type Ring = Zn;

    type RingType = ZnBase;

    fn input_rings<'a>(&'a self) -> &'a [Zn] {
        self.rescaling.input_rings()
    }

    fn output_rings<'a>(&'a self) -> &'a [Zn] {
        self.convert.output_rings()
    }

    #[instrument(skip_all)]
    fn apply<V1, V2>(&self, input: Submatrix<V1, El<Self::Ring>>, output: SubmatrixMut<V2, El<Self::Ring>>)
            where V1: AsPointerToSlice<El<Self::Ring>>,
                V2: AsPointerToSlice<El<Self::Ring>>
    {
        assert_eq!(input.col_count(), output.col_count());
        #[cfg(debug_assertions)] {
            use std::cmp::min;
            use feanor_math::ordered::OrderedRingStore;

            let rns_ring = zn_rns::Zn::new(self.input_rings().iter().cloned().collect(), ZZbig);
            // unfortunately, checking all the inputs takes a lot of time, and even though we only do it on debug builds,
            // it is not good to extremely blow up the test times. Hence, check only some input elements 
            for j in (0..min(500, input.col_count())).step_by(7) {
                debug_assert!(
                    ZZbig.is_leq(&ZZbig.int_hom().mul_map(ZZbig.abs(rns_ring.smallest_lift(rns_ring.from_congruence((0..input.row_count()).map(|i| self.input_rings().at(i).clone_el(input.at(i, j)))))), 4), rns_ring.modulus()),
                    "Input is not <= q/4 in absolute value"
                );
            }
        }

        let mut tmp = (0..(self.rescaling.output_rings().len() * input.col_count())).map(|idx| self.rescaling.output_rings().at(idx  / input.col_count()).zero()).collect::<Vec<_>>();
        let mut tmp = SubmatrixMut::from_1d(&mut tmp, self.rescaling.output_rings().len(), input.col_count());
        self.rescaling.apply(input, tmp.reborrow());
        self.convert.apply(tmp.as_const(), output);
    }
}

///
/// Computes almost exact rescaling.
/// The exact rescaling refers to the map
/// ```text
///   Z/qZ -> Z/(aq/b)Z, x -> round(lift(x) * a/b) mod aq/b
/// ```
/// where `b | q` and `gcd(a, q) = 1`. We allow allow an error of `+/- 1`, 
/// as this enables a fast RNS implementation
/// 
/// # Examples
/// ```rust
/// # use feanor_math::ring::*;
/// # use feanor_math::rings::zn::zn_64::*;
/// # use feanor_math::assert_el_eq;
/// # use feanor_math::homomorphism::*;
/// # use feanor_math::matrix::*;
/// # use fheanor::rns_conv::*;
/// # use fheanor::rns_conv::bfv_rescale::RNSRescaling;
/// let from = vec![Zn::new(17), Zn::new(19), Zn::new(23)];
/// let from_modulus = 17 * 19 * 23;
/// let to = vec![Zn::new(29)];
/// let rescaling = RNSRescaling::new(from.clone(), to.clone());
/// let mut output = [to[0].zero()];
///
/// let x = 1000;
/// rescaling.apply(Submatrix::from_1d(&[from[0].int_hom().map(x), from[1].int_hom().map(x), from[2].int_hom().map(x)], 3, 1), SubmatrixMut::from_1d(&mut output, 1, 1));
/// assert_el_eq!(
///     &to[0],
///     &to[0].int_hom().map(/* rounded division */ (x * 29 + from_modulus / 2) / from_modulus),
///     &output[0]);
/// ```
/// We sometimes get an error of `+/- 1`
/// ```should_panic
/// # use feanor_math::ring::*;
/// # use feanor_math::rings::zn::zn_64::*;
/// # use feanor_math::assert_el_eq;
/// # use feanor_math::homomorphism::*;
/// # use feanor_math::matrix::*;
/// # use fheanor::rns_conv::*;
/// # use fheanor::rns_conv::bfv_rescale::RNSRescaling;
/// # let from = vec![Zn::new(17), Zn::new(19), Zn::new(23)];
/// # let from_modulus = 17 * 19 * 23;
/// # let to = vec![Zn::new(29)];
/// # let rescaling = RNSRescaling::new(from.clone(), to.clone());
/// # let mut output = [to[0].zero()];
/// for x in 1000..2000 {
///     rescaling.apply(Submatrix::from_1d(&[from[0].int_hom().map(x), from[1].int_hom().map(x), from[2].int_hom().map(x)], 3, 1), SubmatrixMut::from_1d(&mut output, 1, 1));
///     assert_el_eq!(
///         &to[0],
///         &to[0].int_hom().map(/* rounded division */ (x * 29 + from_modulus / 2) / from_modulus + 1),
///         &output[0]);
/// }
/// ```
/// 
pub struct RNSRescaling<A = Global>
    where A: Allocator + Clone
{
    /// the `i`-th element is the position of `in_moduli[i]` in `out_moduli + b_moduli`
    in_moduli_in_out_b_moduli: Vec<usize>,
    in_moduli: Vec<Zn>,
    b_to_out_moduli_lift: UsedBaseConversion<A>,
    /// `a` as an element of each modulus of `in_moduli`
    a: Vec<El<Zn>>,
    /// `b^-1` as an element of each modulus of `out_moduli`
    b_inv: Vec<El<Zn>>,
    allocator: A,
    a_bigint: El<BigIntRing>,
    b_bigint: El<BigIntRing>
}

impl RNSRescaling {
    
    ///
    /// Creates a new [`RNSRescaling`], where
    ///  - `q` is the product of `in_moduli`
    ///  - `aq/b` is the product of `out_moduli`
    /// 
    /// The factors `a` and `b` are computed from these two lists.
    /// 
    pub fn new(in_moduli: Vec<Zn>, out_moduli: Vec<Zn>) -> Self {
        Self::new_with_alloc(in_moduli, out_moduli, Global)
    }
}

impl<A> RNSRescaling<A>
    where A: Allocator + Clone
{
    pub fn num(&self) -> &El<BigIntRing> {
        &self.a_bigint
    }

    pub fn den(&self) -> &El<BigIntRing> {
        &self.b_bigint
    }

    ///
    /// Creates a new [`RNSRescaling`], where
    ///  - `q` is the product of `in_moduli`
    ///  - `aq/b` is the product of `out_moduli`
    /// 
    /// The factors `a` and `b` are computed from these two lists.
    /// 
    #[instrument(skip_all)]
    pub fn new_with_alloc(in_moduli: Vec<Zn>, out_moduli: Vec<Zn>, allocator: A) -> Self {

        let mut b_moduli = Vec::new();
        let mut in_moduli_in_out_b_moduli = Vec::new();
        for Zn in &in_moduli {
            if let Some((idx, _)) = out_moduli.iter().enumerate().find(|(_, out_Zn)| Zn.get_ring() == out_Zn.get_ring()) {
                in_moduli_in_out_b_moduli.push(idx);
            } else {
                in_moduli_in_out_b_moduli.push(out_moduli.len() + b_moduli.len());
                b_moduli.push(Zn.clone());
            }
        }
        let a = ZZbig.prod(out_moduli.iter()
            .filter(|Zn| in_moduli.iter().all(|in_Zn| Zn.get_ring() != in_Zn.get_ring()))
            .map(|Zn| int_cast(*Zn.modulus(), ZZbig, Zn.integer_ring())));
        let b = ZZbig.prod(b_moduli.iter().map(|Zn| int_cast(*Zn.modulus(), ZZbig, Zn.integer_ring())));

        RNSRescaling {
            a: in_moduli.iter().map(|Zn| Zn.coerce(&ZZbig, ZZbig.clone_el(&a))).collect(),
            b_inv: out_moduli.iter().map(|Zn| Zn.invert(&Zn.coerce(&ZZbig, ZZbig.clone_el(&b))).unwrap()).collect(),
            b_to_out_moduli_lift: UsedBaseConversion::new_with_alloc(b_moduli, out_moduli, allocator.clone()),
            in_moduli_in_out_b_moduli: in_moduli_in_out_b_moduli,
            in_moduli: in_moduli,
            allocator: allocator,
            a_bigint: a,
            b_bigint: b
        }
    }

    fn b_moduli(&self) -> &[Zn] {
        self.b_to_out_moduli_lift.input_rings()
    }
}

impl<A> RNSOperation for RNSRescaling<A>
    where A: Allocator + Clone
{
    type Ring = Zn;
    type RingType = ZnBase;

    fn input_rings<'a>(&'a self) -> &'a [Zn] {
        &self.in_moduli
    }

    fn output_rings<'a>(&'a self) -> &'a [Zn] {
        self.b_to_out_moduli_lift.output_rings()
    }

    #[instrument(skip_all)]
    fn apply<V1, V2>(&self, input: Submatrix<V1, El<Self::Ring>>, output: SubmatrixMut<V2, El<Self::Ring>>)
        where V1: AsPointerToSlice<El<Self::Ring>>,
            V2: AsPointerToSlice<El<Self::Ring>>
    {
        assert_eq!(input.row_count(), self.input_rings().len());
        assert_eq!(output.row_count(), self.output_rings().len());
        assert_eq!(input.col_count(), output.col_count());
        let col_count = input.col_count();

        // Allocate `x_mod_b` and `x_mod_aq_over_b`
        let mut x_mod_b = Vec::with_capacity_in(self.b_moduli().len() * col_count, self.allocator.clone());
        x_mod_b.extend(self.b_moduli().iter().flat_map(|Zn| (0..col_count).map(|_| Zn.zero())));
        let mut x_mod_b = SubmatrixMut::from_1d(&mut x_mod_b, self.b_moduli().len(), col_count);

        let mut x_mod_aq_over_b = output;

        // Compute `x := el * a mod aq`, store it in `x_mod_b` and `x_mod_aq_over_b`
        for (i, (Zn, a)) in self.input_rings().iter().zip(self.a.iter()).enumerate() {
            let target_idx = self.in_moduli_in_out_b_moduli[i];
            let source = input.row_at(i);
            let target = if target_idx >= self.output_rings().len() {
                x_mod_b.row_mut_at(target_idx - self.output_rings().len())
            } else {
                x_mod_aq_over_b.row_mut_at(target_idx)
            };
            for j in 0..col_count {
                *target.at_mut(j) = Zn.mul_ref(source.at(j), a);
            }
        }

        // Compute the shortest lift of `x mod b` to `aq/b`; Here we might introduce an error of `+/- b`
        // that will later be rescaled to `+/- 1`.
        let mut x_mod_b_lift = Vec::with_capacity_in(self.output_rings().len() * col_count, self.allocator.clone());
        x_mod_b_lift.extend(self.output_rings().iter().flat_map(|Zn| (0..col_count).map(|_| Zn.zero())));
        let mut x_mod_b_lift = SubmatrixMut::from_1d(&mut x_mod_b_lift, self.output_rings().len(), col_count);
        self.b_to_out_moduli_lift.apply(x_mod_b.as_const(), x_mod_b_lift.reborrow());

        // compute the result
        let mut result = x_mod_aq_over_b;
        for (i, (Zn, b_inv)) in self.output_rings().iter().zip(self.b_inv.iter()).enumerate() {
            let result_row = result.row_mut_at(i);
            let delta_row = x_mod_b_lift.row_at(i);
            for j in 0..col_count {
                // Subtract `lift(x mod b) mod aq/b` from `result`
                let divisble_by_b = Zn.sub_ref(result_row.at(j), delta_row.at(j));
                // Now `result - lift(x mod b)` is divisibible by b
                *result_row.at_mut(j) = Zn.mul_ref_snd(divisble_by_b, b_inv);
            }
        }
    }

}

#[test]
fn test_rescale_partial() {
    let from = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    let to = vec![Zn::new(257), Zn::new(113)];
    let q = 17 * 97 * 113;

    let rescaling = RNSRescaling::new_with_alloc(
        from.clone(), 
        to.clone(),
        Global
    );

    for i in -(q/2)..=(q/2) {
        let input = from.iter().map(|Zn| Zn.int_hom().map(i)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map((i as f64 * 257. / 17. / 97.).round() as i32)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        rescaling.apply(Submatrix::from_1d(&input, 3, 1), SubmatrixMut::from_1d(&mut actual, 2, 1));

        for j in 0..expected.len() {
            assert!(
                to.at(j).smallest_lift(to.at(j).sub_ref(expected.at(j), actual.at(j))).abs() <= 1,
                "Expected {} to be {} +/- 1",
                to.at(j).format(actual.at(j)),
                to.at(j).format(expected.at(j))
            );
        }
    }
}

#[test]
fn test_rescale_larger_unordered() {
    let from = vec![Zn::new(17),  Zn::new(23), Zn::new(29), Zn::new(31), Zn::new(19)];
    let to = vec![Zn::new(19), Zn::new(17), Zn::new(5), Zn::new(23)];
    let q = 17 * 31 * 23 * 29 * 19;

    let rescaling = RNSRescaling::new_with_alloc(
        from.clone(), 
        to.clone(),
        Global
    );

    for i in (-(q/2)..=(q/2)).step_by(2907) {
        let input = from.iter().map(|Zn| Zn.int_hom().map(i)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map((i as f64 * 5. / 31. / 29.).round() as i32)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        rescaling.apply(Submatrix::from_1d(&input, 5, 1), SubmatrixMut::from_1d(&mut actual, 4, 1));

        for j in 0..expected.len() {
            assert!(
                to.at(j).smallest_lift(to.at(j).sub_ref(expected.at(j), actual.at(j))).abs() <= 1,
                "Expected {} to be {} +/- 1",
                to.at(j).format(actual.at(j)),
                to.at(j).format(expected.at(j))
            );
        }
    }
}

#[test]
fn test_rescale_larger() {
    let from = vec![Zn::new(17), Zn::new(31), Zn::new(23), Zn::new(29), Zn::new(19)];
    let to = vec![Zn::new(5), Zn::new(17), Zn::new(23), Zn::new(19)];
    let q = 17 * 31 * 23 * 29 * 19;

    let rescaling = RNSRescaling::new_with_alloc(
        from.clone(), 
        to.clone(),
        Global
    );

    for i in (-(q/2)..=(q/2)).step_by(2907) {
        let input = from.iter().map(|Zn| Zn.int_hom().map(i)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map((i as f64 * 5. / 31. / 29.).round() as i32)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        rescaling.apply(Submatrix::from_1d(&input, 5, 1), SubmatrixMut::from_1d(&mut actual, 4, 1));

        for j in 0..expected.len() {
            assert!(
                to.at(j).smallest_lift(to.at(j).sub_ref(expected.at(j), actual.at(j))).abs() <= 1,
                "Expected {} to be {} +/- 1",
                to.at(j).format(actual.at(j)),
                to.at(j).format(expected.at(j))
            );
        }
    }
}

#[test]
fn test_rescale_convert() {
    let from = vec![Zn::new(17), Zn::new(31), Zn::new(23), Zn::new(29), Zn::new(19)];
    let to = vec![Zn::new(31), Zn::new(29)];
    let q = 17 * 31 * 23 * 29 * 19;
    let rescaling = RNSRescalingConversion::new_with_alloc(
        from.clone(),
        to.clone(), 
        vec![Zn::new(5)], 
        vec![1, 3], 
        Global
    );

    // `RNSRescaling` only works up to `q/4`
    for i in (-(q/4)..(q/4 - 512)).step_by(512) {
        // `q/4` is quite large, so group stuff into matrices here
        let input = OwnedMatrix::from_fn(from.len(), 512, |k, j| from.at(k).int_hom().map(i + j as i32));
        let expected = OwnedMatrix::from_fn(to.len(), 512, |k, j| to.at(k).int_hom().map(((i + j as i32) as f64 * 5. / 31. / 29.).round() as i32));
        let mut actual = OwnedMatrix::from_fn(to.len(), 512, |k, _j| to.at(k).zero());

        rescaling.apply(input.data(), actual.data_mut());

        for k in 0..expected.row_count() {
            for j in 0..expected.col_count() {
                assert!(
                    to.at(k).smallest_lift(to.at(k).sub_ref(expected.at(k, j), actual.at(k, j))).abs() <= 1,
                    "Expected {} to be {} +/- 1",
                    to.at(k).format(actual.at(k, j)),
                    to.at(k).format(expected.at(k, j))
                );
            }
        }
    }
}

#[test]
fn test_rescale_small_num() {
    let from = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    let to = vec![Zn::new(19), Zn::new(23), Zn::new(113)];
    let q = 17 * 97 * 113;

    let rescaling = RNSRescaling::new_with_alloc(
        from.clone(), 
        to.clone(),
        Global
    );

    for i in -(q/2)..=(q/2) {
        let input = from.iter().map(|Zn| Zn.int_hom().map(i)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map((i as f64 * 19. * 23. / 17. / 97.).round() as i32)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        rescaling.apply(Submatrix::from_1d(&input, 3, 1), SubmatrixMut::from_1d(&mut actual, 3, 1));

        for j in 0..expected.len() {
            assert!(
                to.at(j).smallest_lift(to.at(j).sub_ref(expected.at(j), actual.at(j))).abs() <= 1,
                "Expected {} to be {} +/- 1",
                to.at(j).format(actual.at(j)),
                to.at(j).format(expected.at(j))
            );
        }
    }
}

#[test]
fn test_rescale_small() {
    let from = vec![Zn::new(17), Zn::new(19), Zn::new(23)];
    let to = vec![Zn::new(29)];
    let q = 17 * 19 * 23;

    let rescaling = RNSRescaling::new_with_alloc(
        from.clone(), 
        to.clone(),
        Global
    );

    // since Zm_intermediate has a very large modulus, we can ignore errors here at the moment (I think)
    for i in -(q/2)..=(q/2) {
        let input = from.iter().map(|Zn| Zn.int_hom().map(i)).collect::<Vec<_>>();
        let output = to.iter().map(|Zn| Zn.int_hom().map((i as f64 * 29. / q as f64).round() as i32)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        rescaling.apply(Submatrix::from_1d(&input, 3, 1), SubmatrixMut::from_1d(&mut actual, 1, 1));

        let Zk = to.at(0);
        assert!(Zk.eq_el(output.at(0), actual.at(0)) ||
            Zk.eq_el(output.at(0), &Zk.add_ref_fst(actual.at(0), Zk.one())) ||
            Zk.eq_el(output.at(0), &Zk.sub_ref_fst(actual.at(0), Zk.one()))
        );
    }
}
