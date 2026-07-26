use std::mem::MaybeUninit;

use feanor_math::matrix::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::zn_64::*;
use tracing::instrument;

use super::RNSOperation;
use crate::rns_conv::UsedBaseConversion;

/// Computes almost exact base conversion with a shared factor.
/// The exact map would be
/// ```text
///   Z/aqZ -> Z/aq'Z, x -> lift(x) mod aq'
/// ```
/// but as usual, we allow an error of `+/- aq`, unless the shortest
/// lift of the input is bounded by `aq/4`, in which case the result
/// is always correct.
///
/// The functionality is exactly as for [`RNSBaseConversion`],
/// except that it might be faster by reusing the shared factor `a`.
///
/// [`RNSBaseConversion`]: crate::rns_conv::bconv::RNSBaseConversion
pub struct RNSSharedBaseConversion {
    conversion: UsedBaseConversion,
    out_moduli: Vec<Zn>,
}

impl RNSSharedBaseConversion {
    /// Creates a new [`RNSSharedBaseConversion`], where
    ///  - `a` is the product of `shared_moduli`
    ///  - `q` is the product of `additional_in_moduli`
    ///  - `a'` is the product of `additional_out_moduli`
    ///
    /// The input resp. output moduli are ordered as in `shared_moduli`, followed
    /// by `additional_in_moduli` resp. `additional_out_moduli`. In other words, the
    /// additional moduli are appended at the end to the shared moduli.
    pub fn new(shared_moduli: Vec<Zn>, additional_in_moduli: Vec<Zn>, additional_out_moduli: Vec<Zn>) -> Self {
        let in_moduli = shared_moduli
            .iter()
            .cloned()
            .chain(additional_in_moduli.into_iter())
            .collect::<Vec<_>>();
        let out_moduli = shared_moduli
            .into_iter()
            .chain(additional_out_moduli.iter().cloned())
            .collect::<Vec<_>>();
        let conversion = UsedBaseConversion::new(in_moduli, additional_out_moduli);
        Self { out_moduli, conversion }
    }

    fn a_moduli_count(&self) -> usize { self.out_moduli.len() - self.conversion.output_rings().len() }
}

impl RNSOperation for RNSSharedBaseConversion {
    type Ring = Zn;
    type RingType = ZnBase;

    fn input_rings<'a>(&'a self) -> &'a [Self::Ring] { self.conversion.input_rings() }

    fn output_rings<'a>(&'a self) -> &'a [Self::Ring] { &self.out_moduli }

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
        assert_eq!(input.col_count(), output.col_count());
        assert_eq!(input.row_count(), self.input_rings().len());
        assert_eq!(output.row_count(), self.output_rings().len());

        _ = self.conversion.apply(
            input,
            output
                .reborrow()
                .restrict_rows(self.a_moduli_count()..self.output_rings().len()),
        );
        for i in 0..self.a_moduli_count() {
            for j in 0..input.col_count() {
                *output.at_mut(i, j) = MaybeUninit::new(self.output_rings()[i].clone_el(input.at(i, j)));
            }
        }
        // SAFETY: we just initialized it
        return unsafe { output.assume_init() };
    }
}

#[cfg(test)]
use feanor_math::homomorphism::*;

#[test]
fn test_rns_shared_base_conversion() {
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(17), Zn::new(97), Zn::new(113)];
    let to = vec![Zn::new(17), Zn::new(97), Zn::new(113), Zn::new(257)];
    let table = RNSSharedBaseConversion::new(from.clone(), Vec::new(), vec![to[3]]);

    for k in -(17 * 97 * 113 / 4)..=(17 * 97 * 113 / 4) {
        let x = from.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();
        let y = to.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|_| MaybeUninit::uninit()).collect::<Vec<_>>();

        let actual = table.apply(Submatrix::from_1d(&x, 3, 1), SubmatrixMut::from_1d(&mut actual, 4, 1));

        for i in 0..y.len() {
            assert!(to[i].eq_el(&y[i], actual.at(i, 0)));
        }
    }
}
