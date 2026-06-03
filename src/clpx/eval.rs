use crate::circuit::evaluator::CircuitEvaluator;
use crate::feanor_math::group::AbelianGroupStore;

use super::*;
use crate::circuit::{Coefficient, PlaintextCircuit};

pub trait AsCLPXPlaintext<Params: CLPXInstantiation>: RingBase {

    ///
    /// Computes a plaintext-ciphertext addition.
    /// 
    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params>;

    ///
    /// Computes a plaintext-ciphertext multiplication.
    /// 
    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params>;

    ///
    /// Computes a plaintext-ciphertext multiplication and adds the
    /// result to `dst`.
    /// 
    fn hom_fma(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        dst: Ciphertext<Params>,
        lhs: &Self::Element, 
        rhs: &Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add(C, dst, &self.hom_mul_to(P, C, lhs, Params::clone_ct(C, rhs)))
    }
}

impl<R, Params> AsCLPXPlaintext<Params> for R
    where R: NumberRingQuotient,
        Params: CLPXInstantiation,
        <PlaintextRing<Params> as RingStore>::Type: CanHomFrom<R>
{
    default fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain(P, C, &P.can_hom(RingValue::from_ref(self)).unwrap().map_ref(m), ct)
    }

    ///
    /// Computes a plaintext-ciphertext multiplication.
    /// 
    default fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain(P, C, &P.can_hom(RingValue::from_ref(self)).unwrap().map_ref(m), ct)
    }
}

impl<Params: CLPXInstantiation> AsCLPXPlaintext<Params> for StaticRingBase<i64> {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain(P, C, &P.inclusion().compose(P.base_ring().can_hom(&ZZi64).unwrap()).map(*m), ct)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain(P, C, &P.inclusion().compose(P.base_ring().can_hom(&ZZi64).unwrap()).map_ref(m), ct)
    }
}

impl<Params: CLPXInstantiation> AsCLPXPlaintext<Params> for BigIntRingBase {

    fn hom_add_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain(P, C, &P.inclusion().compose(P.base_ring().can_hom(&ZZbig).unwrap()).map_ref(m), ct)
    }

    fn hom_mul_to(
        &self, 
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        m: &Self::Element, 
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain(P, C, &P.inclusion().compose(P.base_ring().can_hom(&ZZbig).unwrap()).map_ref(m), ct)
    }
}
struct CLPXEvaluator<'a, R: ?Sized + AsCLPXPlaintext<Inst> , Inst: CLPXInstantiation> {
    galois_group: &'a CyclotomicGaloisGroup,
    ring: &'a R,
    P: &'a PlaintextRing<Inst>,
    C: &'a CiphertextRing<Inst>,
    C_mul: Option<&'a CiphertextRing<Inst>>,
    rk: Option<&'a RelinKey<Inst>>,
    gks: &'a [(GaloisGroupEl, KeySwitchKey<Inst>)]
}

impl<'a, 'b, R: ?Sized + AsCLPXPlaintext<Inst> , Inst: CLPXInstantiation> CircuitEvaluator<'b, Ciphertext<Inst>, R> for CLPXEvaluator<'a, R, Inst> {

    fn supports_gal(&self) -> bool {
        self.gks.len() > 0
    }

    fn supports_mul(&self) -> bool {
        self.C_mul.is_some() && self.rk.is_some()
    }

    fn add_constant(&mut self, val: Ciphertext<Inst>, constant: &'b Coefficient<R>) -> Ciphertext<Inst> {
        let ring = RingRef::new(self.ring);
        self.ring.hom_add_to(self.P, self.C, &constant.clone(ring).to_ring_el(ring), val)
    }

    fn gal(&mut self, val: Ciphertext<Inst>, gs: &'b [GaloisGroupEl]) -> Vec<Ciphertext<Inst>> {
        let gks = gs.as_fn().map_fn(|g| &self.gks.iter().filter(|(gk_g, _)| self.galois_group.eq_el(g, gk_g)).next().expect("galois key not present").1);
        if gs.len() == 1 {
            vec![Inst::hom_galois(self.P, self.C, val, &gs[0], gks.at(0))]
        } else {
            Inst::hom_galois_many(self.P, self.C, val, gs, &gks)
        }
    }

    fn inner_prod<'c, I>(&mut self, mut data: I) -> Ciphertext<Inst>
        where I: Iterator<Item = (&'b Coefficient<R>, &'c Ciphertext<Inst>)>,
            R: 'b,
            Ciphertext<Inst>: 'c
    {
        if let Some((coeff, ciphertext)) = data.next() {
            let mut result = if let Coefficient::One = coeff {
                Inst::clone_ct(self.C, ciphertext)
            } else if let Some(int) = coeff.as_integer() {
                <StaticRingBase<i64> as AsCLPXPlaintext<Inst>>::hom_mul_to(ZZi64.get_ring(), self.P, self.C, &(int as i64), Inst::clone_ct(self.C, ciphertext))
            } else if let Coefficient::Other(coeff) = coeff {
                self.ring.hom_mul_to(self.P, self.C, coeff, Inst::clone_ct(self.C, ciphertext))
            } else {
                unreachable!()
            };
            for (coeff, ciphertext) in data {
                if let Coefficient::One = coeff {
                    result = Inst::hom_add(self.C, result, ciphertext);
                } else if let Some(int) = coeff.as_integer() {
                    result = <StaticRingBase<i64> as AsCLPXPlaintext<Inst>>::hom_fma(ZZi64.get_ring(), self.P, self.C, result, &(int as i64), ciphertext);
                } else if let Coefficient::Other(coeff) = coeff {
                    result = self.ring.hom_fma(self.P, self.C, result, coeff, ciphertext);
                }
            }
            return result;
        } else {
            return Inst::transparent_zero(self.C);
        }
    }

    fn mul(&mut self, lhs: Ciphertext<Inst>, rhs: Ciphertext<Inst>) -> Ciphertext<Inst> {
        Inst::hom_mul(self.P, self.C, self.C_mul.unwrap(), lhs, rhs, self.rk.unwrap())
    }

    fn square(&mut self, val: Ciphertext<Inst>) -> Ciphertext<Inst> {
        Inst::hom_square(self.P, self.C, self.C_mul.unwrap(), val, self.rk.unwrap())
    }
}

impl<R: RingBase> PlaintextCircuit<R> {

    #[instrument(skip_all)]
    pub fn evaluate_clpx<Params, S>(&self, 
        ring: S,
        P: &PlaintextRing<Params>, 
        C: &CiphertextRing<Params>, 
        C_mul: Option<&CiphertextRing<Params>>,
        inputs: &[Ciphertext<Params>], 
        rk: Option<&RelinKey<Params>>, 
        gks: &[(GaloisGroupEl, KeySwitchKey<Params>)], 
        _debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<Ciphertext<Params>>
        where Params: CLPXInstantiation,
            R: AsCLPXPlaintext<Params>,
            S: RingStore<Type = R> + Copy
    {
        assert!(!self.has_multiplication_gates() || C_mul.is_some());
        assert_eq!(C_mul.is_some(), rk.is_some());
        let galois_group = C.acting_galois_group();
        return self.evaluate_generic(
            inputs,
            CLPXEvaluator {
                C: C,
                C_mul: C_mul,
                P: P,
                galois_group: galois_group.parent(),
                gks: gks,
                ring: ring.get_ring(),
                rk: rk
            }
        );
    }
}

#[cfg(test)]
use std::slice::from_ref;
#[cfg(test)]
use feanor_math::rings::poly::{dense_poly::DensePolyRing, PolyRingStore};
#[cfg(test)]
use crate::poly_eval::to_circuit::poly_to_circuit;

#[test]
fn test_hom_evaluate_circuit() {
    feanor_tracing::DelayedLogger::init_test();
    let (P, C, C_mul, sk, rk, m, ct) = test_setup_clpx(Pow2CLPX::new(1 << 8));
    let FpX = DensePolyRing::new(P.base_ring(), "X");
    let [f] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(7) - 3 * X.pow_ref(3) + 2 * X + 10]);
    let circuit = poly_to_circuit(&FpX, from_ref(&f))
        .change_ring_uniform(|x| x.change_ring(|x| FpX.base_ring().smallest_lift(x)));

    let res = circuit.evaluate_clpx::<Pow2CLPX, _>(ZZbig, &P, &C, Some(&C_mul), &[ct], Some(&rk), &[], None).into_iter().next().unwrap();
    assert_el_eq!(&P, P.inclusion().map(FpX.evaluate(&f, &P.wrt_canonical_basis(&m).at(0), FpX.base_ring().identity())), &Pow2CLPX::dec(&P, &C, res, &sk));
}