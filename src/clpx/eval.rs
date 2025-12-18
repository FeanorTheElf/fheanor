use crate::feanor_math::group::AbelianGroupStore;

use super::*;
use crate::circuit::{evaluator::DefaultCircuitEvaluator, Coefficient, PlaintextCircuit};

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

    ///
    /// Applies a Galois automorphism to a plaintext.
    /// 
    fn apply_galois_action_plain(
        &self,
        P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[GaloisGroupEl]
    ) -> Vec<Self::Element>;
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

    ///
    /// Applies a Galois automorphism to a plaintext.
    /// 
    default fn apply_galois_action_plain(
        &self,
        _P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[GaloisGroupEl]
    ) -> Vec<Self::Element> {
        self.apply_galois_action_many(x, gs)
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

    fn apply_galois_action_plain(
        &self,
        _P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[GaloisGroupEl]
    ) -> Vec<Self::Element> {
        gs.iter().map(|_| self.clone_el(x)).collect()
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

    fn apply_galois_action_plain(
        &self,
        _P: &PlaintextRing<Params>, 
        x: &Self::Element,
        gs: &[GaloisGroupEl]
    ) -> Vec<Self::Element> {
        gs.iter().map(|_| self.clone_el(x)).collect()
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
        key_switches: &mut usize,
        _debug_sk: Option<&SecretKey<Params>>
    ) -> Vec<Ciphertext<Params>>
        where Params: CLPXInstantiation,
            R: AsCLPXPlaintext<Params>,
            S: RingStore<Type = R> + Copy
    {
        assert!(!self.has_multiplication_gates() || C_mul.is_some());
        assert_eq!(C_mul.is_some(), rk.is_some());
        let galois_group = C.acting_galois_group();
        let key_switches = RefCell::new(key_switches);
        return self.evaluate_generic(
            inputs,
            DefaultCircuitEvaluator::<_, R, _, _, _, _, _, _>::new(
                |x| match x {
                    Coefficient::Zero => Params::transparent_zero(C),
                    x => ring.get_ring().hom_add_to(P, C, &x.clone(ring).to_ring_el(ring), Params::transparent_zero(C))
                },
                |dst, x, ct| match x {
                    Coefficient::Zero => dst,
                    Coefficient::One => Params::hom_add(C, dst, ct),
                    Coefficient::NegOne => Params::hom_sub(C, dst, ct),
                    Coefficient::Integer(x) => ring.get_ring().hom_fma(P, C, dst, &ring.int_hom().map(*x), ct),
                    Coefficient::Other(x) => ring.get_ring().hom_fma(P, C, dst, x, ct)
                }
            ).with_mul(|lhs, rhs| {
                **key_switches.borrow_mut() += 1;
                Params::hom_mul(P, C, C_mul.unwrap(), lhs, rhs, rk.unwrap())
            }).with_square(|x| {
                **key_switches.borrow_mut() += 1;
                Params::hom_square(P, C, C_mul.unwrap(), x, rk.unwrap())
            }).with_gal(|x, gs| if gs.len() == 1 {
                **key_switches.borrow_mut() += 1;
                vec![Params::hom_galois(P, C, x, &gs[0], &gks.iter().filter(|(g, _)| galois_group.eq_el(g, &gs[0])).next().unwrap().1)]
            } else {
                **key_switches.borrow_mut() += gs.iter().filter(|g| !galois_group.is_identity(*g)).count();
                Params::hom_galois_many(P, C, x, gs, gs.as_fn().map_fn(|expected_g| if let Some(gk) = gks.iter().filter(|(g, _)| galois_group.eq_el(g, expected_g)).next() {
                    &gk.1
                } else {
                    panic!("Galois key for {} not found", galois_group.underlying_ring().format(&galois_group.as_ring_el(expected_g)))
                }))
            })
        );
    }
}

use std::cell::RefCell;
#[cfg(test)]
use std::slice::from_ref;
#[cfg(test)]
use feanor_math::rings::poly::{dense_poly::DensePolyRing, PolyRingStore};
#[cfg(test)]
use crate::digit_extract::polys::poly_to_circuit;

#[test]
fn test_hom_evaluate_circuit() {
    let (P, C, C_mul, sk, rk, m, ct) = test_setup_clpx(Pow2CLPX::new(1 << 8));
    let FpX = DensePolyRing::new(P.base_ring(), "X");
    let [f] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(7) - 3 * X.pow_ref(3) + 2 * X + 10]);
    let circuit = poly_to_circuit(&FpX, from_ref(&f));

    let res = circuit.evaluate_clpx::<Pow2CLPX, _>(ZZbig, &P, &C, Some(&C_mul), &[ct], Some(&rk), &[], &mut 0, None).into_iter().next().unwrap();
    assert_el_eq!(&P, P.inclusion().map(FpX.evaluate(&f, &P.wrt_canonical_basis(&m).at(0), FpX.base_ring().identity())), &Pow2CLPX::dec(&P, &C, res, &sk));
}