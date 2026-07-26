use std::borrow::Borrow;

use feanor_math::assert_el_eq;
use feanor_math::delegate::*;
use feanor_math::group::*;
use feanor_math::homomorphism::*;
use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::poly::sparse_poly::SparsePolyRingBase;
use feanor_math::rings::poly::*;
use feanor_math::rings::zn::*;
use feanor_math::seq::*;
use tracing::instrument;

use crate::bfv::{BFVInstantiation, Ciphertext, CiphertextRing, KeySwitchKey, PlaintextRing, RelinKey, SecretKey};
use crate::circuit::evaluator::*;
use crate::circuit::*;
use crate::number_ring::galois::*;
use crate::number_ring::*;
use crate::prepared_mul::PreparedMultiplicationRing;
use crate::{ZZbig, ZZi64};

/// Trait for rings that can be used for plaintext-ciphertext
/// operations in BFV.
///
/// You will rarely use functions of this trait directly, it is
/// mainly a tool to support evaluating circuits with coefficients
/// from various rings on BFV ciphertexts. Furthermore, the
/// implementations of the function should not contain much logic,
/// but only delegate to the corresponding functions of
/// [`BFVInstantiation`].
pub trait AsBFVPlaintext<Params: BFVInstantiation>: RingBase {
    /// Computes a plaintext-ciphertext addition.
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params>;

    /// Computes a plaintext-ciphertext multiplication.
    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params>;

    /// Computes a plaintext-ciphertext inner product and adds the
    /// result to `dst`.
    fn hom_inner_prod<L, R, I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        dst: Ciphertext<Params>,
        it: I,
    ) -> Ciphertext<Params>
    where
        L: Borrow<Self::Element>,
        R: Borrow<Ciphertext<Params>>,
        I: Iterator<Item = (L, R)>,
    {
        it.fold(dst, |current, (l, r)| {
            Params::hom_add(
                C,
                current,
                &self.hom_mul_to(P, C, l.borrow(), Params::clone_ct(C, r.borrow())),
            )
        })
    }
}

impl<R, Params> AsBFVPlaintext<Params> for R
where
    R: NumberRingQuotient,
    Params: BFVInstantiation,
    Params::PlaintextRing: CanHomFrom<R>,
{
    default fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        Params::hom_add_plain(P, C, &P.can_hom(RingValue::from_ref(self)).unwrap().map_ref(m), ct)
    }

    default fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain(P, C, &P.can_hom(RingValue::from_ref(self)).unwrap().map_ref(m), ct)
    }
}

impl<Params: BFVInstantiation> AsBFVPlaintext<Params> for zn_64::ZnBase {
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        assert_eq!(
            int_cast(
                P.base_ring().integer_ring().clone_el(P.base_ring().modulus()),
                ZZi64,
                P.base_ring().integer_ring()
            ),
            *self.modulus()
        );
        Params::hom_add_plain(
            P,
            C,
            &P.inclusion()
                .compose(P.base_ring().can_hom(&ZZi64).unwrap())
                .map(self.smallest_lift(*m)),
            ct,
        )
    }

    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        assert_eq!(
            int_cast(
                P.base_ring().integer_ring().clone_el(P.base_ring().modulus()),
                ZZi64,
                P.base_ring().integer_ring()
            ),
            *self.modulus()
        );
        Params::hom_mul_plain_scalar(
            P,
            C,
            &P.base_ring().can_hom(&ZZi64).unwrap().map(self.smallest_lift(*m)),
            ct,
        )
    }
}

impl<Params: BFVInstantiation> AsBFVPlaintext<Params> for zn_big::ZnBase<BigIntRing> {
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        assert_el_eq!(
            ZZbig,
            int_cast(
                P.base_ring().integer_ring().clone_el(P.base_ring().modulus()),
                ZZbig,
                P.base_ring().integer_ring()
            ),
            self.modulus()
        );
        Params::hom_add_plain(
            P,
            C,
            &P.inclusion()
                .compose(P.base_ring().can_hom(&ZZbig).unwrap())
                .map(self.smallest_lift(self.clone_el(m))),
            ct,
        )
    }

    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        assert_el_eq!(
            ZZbig,
            int_cast(
                P.base_ring().integer_ring().clone_el(P.base_ring().modulus()),
                ZZbig,
                P.base_ring().integer_ring()
            ),
            self.modulus()
        );
        Params::hom_mul_plain_scalar(
            P,
            C,
            &P.base_ring()
                .can_hom(&ZZbig)
                .unwrap()
                .map(self.smallest_lift(self.clone_el(m))),
            ct,
        )
    }
}

impl<R, Params> AsBFVPlaintext<Params> for SparsePolyRingBase<R>
where
    Params: BFVInstantiation,
    R: RingStore<Type = Params::PlaintextZnRing>,
{
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        assert!(P.base_ring().get_ring() == self.base_ring().get_ring());
        Params::hom_add_plain(
            P,
            C,
            &P.from_canonical_basis_extended(
                (0..=self.degree(m).unwrap_or(0)).map(|i| self.base_ring().clone_el(self.coefficient_at(m, i))),
            ),
            ct,
        )
    }

    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        // TODO: once we get a function `mul_can_gen_power` or similar, use that here for improved
        // performance
        assert!(P.base_ring().get_ring() == self.base_ring().get_ring());
        Params::hom_mul_plain(
            P,
            C,
            &P.from_canonical_basis_extended(
                (0..=self.degree(m).unwrap_or(0)).map(|i| self.base_ring().clone_el(self.coefficient_at(m, i))),
            ),
            ct,
        )
    }
}

pub struct EncodedBFVPlaintextRingBase<Params: BFVInstantiation> {
    P: PlaintextRing<Params>,
    C: CiphertextRing<Params>,
}

pub type EncodedBFVPlaintextRing<Params> = RingValue<EncodedBFVPlaintextRingBase<Params>>;

pub struct EncodedBFVPlaintextRingEl<Params: BFVInstantiation> {
    el: El<PlaintextRing<Params>>,
    encoded: El<CiphertextRing<Params>>,
    prepared: <<CiphertextRing<Params> as RingStore>::Type as PreparedMultiplicationRing>::PreparedMultiplicant,
}

impl<Params: BFVInstantiation> EncodedBFVPlaintextRingBase<Params> {
    pub fn new(P: PlaintextRing<Params>, C: CiphertextRing<Params>) -> RingValue<Self> {
        RingValue::from(Self { P, C })
    }

    pub fn plaintext_ring(&self) -> &PlaintextRing<Params> { &self.P }

    pub fn ciphertext_ring(&self) -> &CiphertextRing<Params> { &self.C }
}

impl<Params: BFVInstantiation> PartialEq for EncodedBFVPlaintextRingBase<Params> {
    fn eq(&self, other: &Self) -> bool {
        self.P.get_ring() == other.P.get_ring() && self.C.get_ring() == other.C.get_ring()
    }
}

impl<Params: BFVInstantiation> DelegateRing for EncodedBFVPlaintextRingBase<Params> {
    type Element = EncodedBFVPlaintextRingEl<Params>;
    type Base = Params::PlaintextRing;

    fn get_delegate(&self) -> &Self::Base { self.P.get_ring() }

    fn rev_delegate(&self, el: <Self::Base as RingBase>::Element) -> Self::Element {
        let encoded = Params::encode_plain_multiplicant(&self.P, &self.C, &el);
        let prepared = self.C.get_ring().prepare_multiplicant(&encoded);
        EncodedBFVPlaintextRingEl { prepared, encoded, el }
    }

    fn delegate(&self, el: Self::Element) -> <Self::Base as RingBase>::Element { el.el }
    fn delegate_ref<'a>(&self, el: &'a Self::Element) -> &'a <Self::Base as RingBase>::Element { &el.el }
    fn delegate_mut<'a>(&self, el: &'a mut Self::Element) -> &'a mut <Self::Base as RingBase>::Element { &mut el.el }
}

impl<Params: BFVInstantiation> RingBase for EncodedBFVPlaintextRingBase<Params> {
    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        EncodedBFVPlaintextRingEl {
            el: self.P.clone_el(&val.el),
            encoded: self.C.clone_el(&val.encoded),
            prepared: self.C.get_ring().prepare_multiplicant(&val.encoded),
        }
    }
}

impl<Params: BFVInstantiation> AsBFVPlaintext<Params> for EncodedBFVPlaintextRingBase<Params> {
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &<Self as RingBase>::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        assert!(self.P.get_ring() == P.get_ring());
        Params::hom_add_plain(P, C, &m.el, ct)
    }

    #[instrument(skip_all)]
    fn hom_mul_to(
        &self,
        _P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &<Self as RingBase>::Element,
        ct: Ciphertext<Params>,
    ) -> Ciphertext<Params> {
        assert!(self.C.get_ring() == C.get_ring());
        (
            C.get_ring().mul_prepared(&ct.0, None, &m.encoded, Some(&m.prepared)),
            C.get_ring().mul_prepared(&ct.1, None, &m.encoded, Some(&m.prepared)),
        )
    }
}

struct BFVEvaluator<'a, R: ?Sized + AsBFVPlaintext<Inst>, Inst: BFVInstantiation> {
    galois_group: &'a CyclotomicGaloisGroup,
    ring: &'a R,
    P: &'a PlaintextRing<Inst>,
    C: &'a CiphertextRing<Inst>,
    C_mul: Option<&'a CiphertextRing<Inst>>,
    rk: Option<&'a RelinKey<Inst>>,
    gks: &'a [(GaloisGroupEl, KeySwitchKey<Inst>)],
}

impl<'a, 'b, R: ?Sized + AsBFVPlaintext<Inst>, Inst: BFVInstantiation> CircuitEvaluator<'b, Ciphertext<Inst>, R>
    for BFVEvaluator<'a, R, Inst>
{
    fn supports_gal(&self) -> bool { self.gks.len() > 0 }

    fn supports_mul(&self) -> bool { self.C_mul.is_some() && self.rk.is_some() }

    fn add_constant(&mut self, val: Ciphertext<Inst>, constant: &'b Coefficient<R>) -> Ciphertext<Inst> {
        let ring = RingRef::new(self.ring);
        self.ring
            .hom_add_to(self.P, self.C, &constant.clone(ring).to_ring_el(ring), val)
    }

    fn gal(&mut self, val: Ciphertext<Inst>, gs: &'b [GaloisGroupEl]) -> Vec<Ciphertext<Inst>> {
        let gks = gs.as_fn().map_fn(|g| {
            &self
                .gks
                .iter()
                .filter(|(gk_g, _)| self.galois_group.eq_el(g, gk_g))
                .next()
                .expect("galois key not present")
                .1
        });
        if gs.len() == 1 {
            vec![Inst::hom_galois(self.C, val, &gs[0], gks.at(0))]
        } else {
            Inst::hom_galois_many(self.C, val, gs, &gks)
        }
    }

    fn inner_prod<'c, I>(&mut self, data: I) -> Ciphertext<Inst>
    where
        I: Iterator<Item = (&'b Coefficient<R>, &'c Ciphertext<Inst>)>,
        R: 'b,
        Ciphertext<Inst>: 'c,
    {
        let mut simple_part = None;
        let main_part =
            self.ring.hom_inner_prod(
                self.P,
                self.C,
                Inst::transparent_zero(self.C),
                data.filter_map(|(l, r)| match l {
                    Coefficient::Zero => None,
                    Coefficient::One => {
                        simple_part = Some(
                            simple_part
                                .take()
                                .map(|x| Inst::hom_add(self.C, x, r))
                                .unwrap_or_else(|| Inst::clone_ct(self.C, r)),
                        );
                        None
                    }
                    Coefficient::NegOne => {
                        simple_part = Some(simple_part.take().map(|x| Inst::hom_sub(self.C, x, r)).unwrap_or_else(
                            || {
                                Inst::hom_mul_plain_scalar(
                                    self.P,
                                    self.C,
                                    &self.P.base_ring().neg_one(),
                                    Inst::clone_ct(self.C, r),
                                )
                            },
                        ));
                        None
                    }
                    Coefficient::Integer(scalar) => {
                        let scalar = self.P.base_ring().coerce(&ZZbig, ZZbig.clone_el(scalar));
                        simple_part = Some(
                            simple_part
                                .take()
                                .map(|x| Inst::hom_fma_plain_scalar(self.P, self.C, x, &scalar, r))
                                .unwrap_or_else(|| {
                                    Inst::hom_mul_plain_scalar(self.P, self.C, &scalar, Inst::clone_ct(self.C, r))
                                }),
                        );
                        None
                    }
                    Coefficient::Other(l) => Some((l, r)),
                }),
            );
        if let Some(simple_part) = simple_part.take() {
            return Inst::hom_add(self.C, main_part, &simple_part);
        } else {
            return main_part;
        }
    }

    fn mul(&mut self, lhs: Ciphertext<Inst>, rhs: Ciphertext<Inst>) -> Ciphertext<Inst> {
        Inst::hom_mul(self.P, self.C, self.C_mul.unwrap(), lhs, rhs, self.rk.unwrap())
    }

    fn square(&mut self, val: Ciphertext<Inst>) -> Ciphertext<Inst> {
        Inst::hom_square(self.P, self.C, self.C_mul.unwrap(), val, self.rk.unwrap())
    }
}

impl<R: ?Sized + RingBase> PlaintextCircuit<R> {
    #[instrument(skip_all)]
    pub fn evaluate_bfv<Params, S>(
        &self,
        ring: S,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        C_mul: Option<&CiphertextRing<Params>>,
        inputs: &[Ciphertext<Params>],
        rk: Option<&RelinKey<Params>>,
        gks: &[(GaloisGroupEl, KeySwitchKey<Params>)],
        _debug_sk: Option<&SecretKey<Params>>,
    ) -> Vec<Ciphertext<Params>>
    where
        Params: BFVInstantiation,
        R: AsBFVPlaintext<Params>,
        S: RingStore<Type = R> + Copy,
    {
        assert!(!self.has_multiplication_gates() || C_mul.is_some());
        assert_eq!(C_mul.is_some(), rk.is_some());
        let galois_group = C.acting_galois_group();
        let result = self.evaluate_generic(
            inputs,
            BFVEvaluator {
                C,
                P,
                C_mul,
                galois_group: galois_group.parent(),
                gks,
                ring: ring.get_ring(),
                rk,
            },
        );
        return result;
    }
}

#[cfg(test)]
use std::slice::from_ref;

#[cfg(test)]
use feanor_math::rings::finite::FiniteRingStore;
#[cfg(test)]
use feanor_math::rings::poly::dense_poly::DensePolyRing;
#[cfg(test)]
use feanor_math::rings::zn::ZnRingStore;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::*;

#[cfg(test)]
use crate::bfv::{Pow2BFV, test_setup_bfv};
#[cfg(test)]
use crate::poly_eval::to_circuit::poly_to_circuit;

#[test]
fn test_hom_evaluate_circuit() {
    feanor_tracing::DelayedLogger::init_test();
    let (P, C, C_mul, sk, rk, _, ct) = test_setup_bfv(Pow2BFV::new(1 << 8));
    let FpX = DensePolyRing::new(Zn::new(17), "X");
    let [f] = FpX.with_wrapped_indeterminate(|X| [X.pow_ref(7) - 3 * X.pow_ref(3) + 2 * X + 10]);
    let circuit = poly_to_circuit(&FpX, from_ref(&f));
    for x in FpX.base_ring().elements() {
        assert_el_eq!(
            FpX.base_ring(),
            FpX.evaluate(&f, &x, FpX.base_ring().identity()),
            &circuit.evaluate_generic(&[x], HomEvaluator::new(FpX.base_ring().identity()))[0]
        );
    }

    let res = circuit
        .evaluate_bfv::<Pow2BFV, _>(FpX.base_ring(), &P, &C, Some(&C_mul), &[ct], Some(&rk), &[], None)
        .into_iter()
        .next()
        .unwrap();
    assert_el_eq!(
        &P,
        P.inclusion()
            .map(FpX.evaluate(&f, &FpX.base_ring().int_hom().map(2), FpX.base_ring().identity())),
        &Pow2BFV::dec(&P, &C, res, &sk)
    );
}
