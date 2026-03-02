use std::alloc::Allocator;
use std::alloc::Global;

use feanor_math::matrix::*;
use feanor_math::rings::zn::*;
use feanor_math::ring::*;
use tracing::instrument;

use crate::NiceZn;
use crate::rns_conv::UsedBaseConversion;

use super::RNSOperation;

///
/// Computes almost exact base conversion with a shared factor.
/// The exact map would be
/// ```text
///   Z/aqZ -> Z/aq'Z, x -> lift(x) mod aq'
/// ```
/// but as usual, we allow an error of `+/- aq`, unless the shortest 
/// lift of the input is bounded by `aq/4`, in which case the result
/// is always correct.
/// 
/// The functionality is exactly as for [`RNSMatrixBaseConversion`],
/// except that it might be faster by reusing the shared factor `a`.
/// 
/// [`RNSMatrixBaseConversion`]: crate::rns_conv::matrix_lift::RNSMatrixBaseConversion
/// 
pub struct RNSSharedBaseConversion<A = Global, ZnTy = zn_64::Zn>
    where A: Allocator + Clone,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn
{
    conversion: UsedBaseConversion<A, ZnTy, ZnTy>,
    out_moduli: Vec<ZnTy>
}

impl RNSSharedBaseConversion {

    ///
    /// Creates a new [`RNSSharedBaseConversion`], where
    ///  - `a` is the product of `shared_moduli`
    ///  - `q` is the product of `additional_in_moduli`
    ///  - `a'` is the product of `additional_out_moduli`
    /// 
    /// The input resp. output moduli are ordered as in `shared_moduli`, followed
    /// by `additional_in_moduli` resp. `additional_out_moduli`. In other words, the
    /// additional moduli are appended at the end to the shared moduli.
    /// 
    pub fn new(shared_moduli: Vec<zn_64::Zn>, additional_in_moduli: Vec<zn_64::Zn>, additional_out_moduli: Vec<zn_64::Zn>) -> Self {
        Self::new_with_zn(shared_moduli, additional_in_moduli, additional_out_moduli, Global)
    }
}

impl<A, ZnTy> RNSSharedBaseConversion<A, ZnTy>
    where A: Allocator + Clone,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn
{
    ///
    /// Creates a new [`RNSSharedBaseConversion`], where
    ///  - `a` is the product of `shared_moduli`
    ///  - `q` is the product of `additional_in_moduli`
    ///  - `a'` is the product of `additional_out_moduli`
    /// 
    /// The input resp. output moduli are ordered as in `shared_moduli`, followed
    /// by `additional_in_moduli` resp. `additional_out_moduli`. In other words, the
    /// additional moduli are appended at the end to the shared moduli.
    /// 
    #[instrument(skip_all)]
    pub fn new_with_zn(shared_moduli: Vec<ZnTy>, additional_in_moduli: Vec<ZnTy>, additional_out_moduli: Vec<ZnTy>, allocator: A) -> Self
        where ZnTy: Clone
    {
        let in_moduli = shared_moduli.iter().cloned().chain(additional_in_moduli.into_iter()).collect::<Vec<_>>();
        let out_moduli = shared_moduli.into_iter().chain(additional_out_moduli.iter().cloned()).collect::<Vec<_>>();
        let conversion = UsedBaseConversion::new_with_zn(in_moduli, additional_out_moduli, allocator);
        Self {
            out_moduli: out_moduli,
            conversion: conversion
        }
    }

    fn a_moduli_count(&self) -> usize {
        self.out_moduli.len() - self.conversion.output_rings().len()
    }
}

impl<A, ZnTy> RNSOperation for RNSSharedBaseConversion<A, ZnTy>
    where A: Allocator + Clone,
        ZnTy: RingStore,
        ZnTy::Type: NiceZn
{
    type ZnIn = ZnTy;
    type ZnInBase = ZnTy::Type;
    type ZnOut = ZnTy;
    type ZnOutBase = ZnTy::Type;

    fn input_rings<'a>(&'a self) -> &'a [ZnTy] {
        self.conversion.input_rings()
    }

    fn output_rings<'a>(&'a self) -> &'a [ZnTy] {
        &self.out_moduli
    }

    #[instrument(skip_all)]
    fn apply<V1, V2>(&self, input: Submatrix<V1, El<ZnTy>>, mut output: SubmatrixMut<V2, El<ZnTy>>)
        where V1: AsPointerToSlice<El<ZnTy>>,
            V2: AsPointerToSlice<El<ZnTy>>
    {
        assert_eq!(input.col_count(), output.col_count());
        assert_eq!(input.row_count(), self.input_rings().len());
        assert_eq!(output.row_count(), self.output_rings().len());

        self.conversion.apply(input, output.reborrow().restrict_rows(self.a_moduli_count()..self.output_rings().len()));
        for i in 0..self.a_moduli_count() {
            for j in 0..input.col_count() {
                *output.at_mut(i, j) = self.output_rings()[i].clone_el(input.at(i, j));
            }
        }
    }
}

#[cfg(test)]
use feanor_math::homomorphism::*;
#[cfg(test)]
use feanor_math::seq::*;

#[test]
fn test_rns_shared_base_conversion() {
    let from = vec![zn_64::Zn::new(17), zn_64::Zn::new(97), zn_64::Zn::new(113)];
    let to = vec![zn_64::Zn::new(17), zn_64::Zn::new(97), zn_64::Zn::new(113), zn_64::Zn::new(257)];
    let table = RNSSharedBaseConversion::new_with_zn(from.clone(), Vec::new(), vec![to[3]], Global);

    for k in -(17 * 97 * 113 / 4)..=(17 * 97 * 113 / 4) {
        let x = from.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();
        let y = to.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.int_hom().map(k)).collect::<Vec<_>>();

        table.apply(
            Submatrix::from_1d(&x, 3, 1), 
            SubmatrixMut::from_1d(&mut actual, 4, 1)
        );
        
        for i in 0..y.len() {
            assert!(to[i].eq_el(&y[i], actual.at(i)));
        }
    }
}
