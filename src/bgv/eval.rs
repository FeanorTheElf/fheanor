
use std::borrow::Borrow;
use feanor_math::rings::zn::ZnRing;
use tracing::instrument;

use feanor_math::ring::*;
use feanor_math::integer::BigIntRingBase;
use feanor_math::delegate::*;

use super::noise_estimator::{BGVNoiseEstimator, CiphertextDescriptor};
use super::*;

///
/// Trait for rings whose elements can be used as plaintexts in plaintext-ciphertext
/// operations in BGV.
///
/// In particular, this includes
///  - the BGV plaintext ring `R/tR` (see the impl for [`BGVInstantiation::PlaintextRing`])
///  - integers (see the impl for [`BigIntRingBase`])
///  - "encoded" plaintexts, i.e. plaintexts that have already been lifted to the ciphertext
///    ring (and prepared for fast multiplication) to avoid this cost at operation time
///    (see [`EncodedBGVPlaintextRingBase`])
///
/// When implementing this trait, you usually shouldn't have nontrivial logic in the
/// functions, but only delegate to the appropriate functions of [`BGVInstantiation`] resp.
/// [`BGVNoiseEstimator`].
///
pub trait AsBGVPlaintext<Params: BGVInstantiation>: RingBase + CanHomFrom<BigIntRingBase> {

    ///
    /// Computes a plaintext-ciphertext addition, preserving the relinearization state.
    ///
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params>;

    ///
    /// Computes a plaintext-ciphertext multiplication, preserving the relinearization state.
    ///
    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params>;

    ///
    /// Computes the inner product `sum_i m_i * ct_i` of the given plaintexts and ciphertexts.
    ///
    /// The result is un-relinearized as soon as any of the summands is un-relinearized.
    ///
    /// # Implicit scale
    ///
    /// This function may assume that all inputs have the same implicit scale, and is encouraged
    /// to do so in cases where this can improve noise growth.
    ///
    fn hom_inner_product<'a, 'b, I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> Ciphertext<Params>
        where I: IntoIterator<Item = (Boo<'a, Self::Element>, Boo<'b, Ciphertext<Params>>)>,
            Params: 'a + 'b,
            Self: 'a + 'b
    {
        let mut acc: Option<Ciphertext<Params>> = None;
        for (m, ct) in summands {
            let term = self.hom_mul_to(P, C, &m, ct.to_owned(|ct| Params::clone_ct(P, C, ct)));
            acc = Some(match acc {
                None => term,
                Some(a) => Params::hom_add(P, C, a, term, ImplicitScalePolicy::AssertEqual)
            });
        }
        acc.unwrap_or_else(|| Params::transparent_zero(P, C))
    }

    ///
    /// Estimates the noise caused by [`AsBGVPlaintext::hom_add_to()`].
    ///
    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N>;

    ///
    /// Estimates the noise caused by [`AsBGVPlaintext::hom_mul_to()`].
    ///
    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N>;

    ///
    /// Estimates the noise caused by [`AsBGVPlaintext::hom_inner_product()`].
    ///
    fn hom_inner_product_noise<'a, 'b, N, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            I: IntoIterator<Item = (&'a Self::Element, &'b CiphertextDescriptor<Params, N>)>,
            Self: 'a,
            Params: 'b,
            N: 'b
    {
        let mut acc: Option<CiphertextDescriptor<Params, N>> = None;
        for (m, ct) in summands {
            let term = self.hom_mul_to_noise(estimator, P, C, m, ct);
            acc = Some(match acc {
                None => term,
                Some(a) => estimator.hom_add(P, C, &a, &term, ImplicitScalePolicy::AssertEqual)
            });
        }
        acc.unwrap_or_else(|| estimator.transparent_zero(P, C))
    }
}

// This is the impl for `Params::PlaintextRing`. We cannot write
// `impl<Params> AsBGVPlaintext<Params> for Params::PlaintextRing` literally (an associated-type
// projection in the self-type position is opaque to coherence). Instead we use a `NumberRingQuotient`
// type parameter `R` tied to `Params::PlaintextRing`; the `R: NumberRingQuotient` bound lets
// coherence rule out overlap with the (non-`NumberRingQuotient`) `BigIntRingBase` and
// `EncodedBGVPlaintextRingBase` impls below.
impl<Params, R> AsBGVPlaintext<Params> for R
    where Params: BGVInstantiation<PlaintextRing = R>,
        R: NumberRingQuotient + CanHomFrom<BigIntRingBase>
{
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_add_plain(P, C, m, ct)
    }

    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        Params::hom_mul_plain(P, C, m, ct)
    }

    fn hom_inner_product<'a, 'b, I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> Ciphertext<Params>
        where I: IntoIterator<Item = (Boo<'a, Self::Element>, Boo<'b, Ciphertext<Params>>)>,
            Params: 'a + 'b,
            Self: 'a
    {
        Params::hom_inner_product_plain(P, C, summands)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N> {
        estimator.hom_add_plain(P, C, m, ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N> {
        estimator.hom_mul_plain(P, C, m, ct)
    }

    fn hom_inner_product_noise<'a, 'b, N, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            I: IntoIterator<Item = (&'a Self::Element, &'b CiphertextDescriptor<Params, N>)>,
            Self: 'a,
            Params: 'b,
            N: 'b
    {
        estimator.hom_inner_product_plain(P, C, summands)
    }
}

impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for BigIntRingBase {

    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        let scalar = P.base_ring().coerce(&ZZbig, ZZbig.clone_el(m));
        Params::hom_add_plain_scalar(P, C, &scalar, ct)
    }

    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        let scalar = P.base_ring().coerce(&ZZbig, ZZbig.clone_el(m));
        Params::hom_mul_plain_scalar(P, C, &scalar, ct)
    }

    fn hom_inner_product<'a, 'b, I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> Ciphertext<Params>
        where I: IntoIterator<Item = (Boo<'a, Self::Element>, Boo<'b, Ciphertext<Params>>)>,
            Params: 'a + 'b,
            Self: 'a
    {
        let summands = summands.into_iter().map(|(m, ct)| (P.base_ring().coerce(&ZZbig, m.to_owned(|x| ZZbig.clone_el(x))), ct)).collect::<Vec<_>>();
        Params::hom_inner_product_plain_scalar(P, C, summands)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N> {
        estimator.hom_add_plain_scalar(P, C, &P.base_ring().coerce(&ZZbig, ZZbig.clone_el(m)), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N> {
        estimator.hom_mul_plain_int(P, C, m, ct)
    }

    fn hom_inner_product_noise<'a, 'b, N, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            I: IntoIterator<Item = (&'a Self::Element, &'b CiphertextDescriptor<Params, N>)>,
            Self: 'a,
            Params: 'b,
            N: 'b
    {
        let summands = summands.into_iter().map(|(m, ct)| (P.base_ring().coerce(&ZZbig, ZZbig.clone_el(m)), ct)).collect::<Vec<_>>();
        estimator.hom_inner_product_plain_scalar(P, C, summands)
    }
}

impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for ZnBase {

    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        ZZbig.get_ring().hom_add_to(P, C, &int_cast(self.smallest_lift(*m), ZZbig, ZZi64), ct)
    }

    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        ZZbig.get_ring().hom_mul_to(P, C, &int_cast(self.smallest_lift(*m), ZZbig, ZZi64), ct)
    }

    fn hom_inner_product<'a, 'b, I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> Ciphertext<Params>
        where I: IntoIterator<Item = (Boo<'a, Self::Element>, Boo<'b, Ciphertext<Params>>)>,
            Params: 'a + 'b,
            Self: 'a
    {
        ZZbig.get_ring().hom_inner_product(P, C, summands.into_iter().map(|(x, ct)| (Boo::Owned(int_cast(self.smallest_lift(*x), ZZbig, ZZi64)), ct)))
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N> {
        ZZbig.get_ring().hom_add_to_noise(estimator, P, C, &int_cast(self.smallest_lift(*m), ZZbig, ZZi64), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N> {
        ZZbig.get_ring().hom_mul_to_noise(estimator, P, C, &int_cast(self.smallest_lift(*m), ZZbig, ZZi64), ct)
    }

    fn hom_inner_product_noise<'a, 'b, N, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            I: IntoIterator<Item = (&'a Self::Element, &'b CiphertextDescriptor<Params, N>)>,
            Self: 'a,
            Params: 'b,
            N: 'b
    {
        let summands = summands.into_iter().map(|(x, ct)| (int_cast(self.smallest_lift(*x), ZZbig, ZZi64), ct)).collect::<Vec<_>>();
        ZZbig.get_ring().hom_inner_product_noise(estimator, P, C, summands.iter().map(|(x, ct)| (x, *ct)))
    }
}

///
/// A ring whose elements are BGV plaintexts (from `R/tR`) together with their "encoded"
/// representation in a fixed ciphertext ring (the result of [`BGVInstantiation::encode_plain()`])
/// and a prepared multiplicant for that encoded value.
///
/// In other words, this is the BGV plaintext ring again, but elements carry extra data that
/// speeds up plaintext-ciphertext multiplications.
///
pub struct EncodedBGVPlaintextRingBase<Params: BGVInstantiation> {
    P: PlaintextRing<Params>,
    C: CiphertextRing<Params>
}

pub type EncodedBGVPlaintextRing<Params> = RingValue<EncodedBGVPlaintextRingBase<Params>>;

pub struct EncodedBGVPlaintextRingEl<Params: BGVInstantiation> {
    el: El<PlaintextRing<Params>>,
    encoded: El<CiphertextRing<Params>>
}

impl<Params: BGVInstantiation> EncodedBGVPlaintextRingBase<Params> {

    pub fn new(P: PlaintextRing<Params>, C: CiphertextRing<Params>) -> RingValue<Self> {
        RingValue::from(Self { P, C })
    }

    pub fn plaintext_ring(&self) -> &PlaintextRing<Params> {
        &self.P
    }

    pub fn ciphertext_ring(&self) -> &CiphertextRing<Params> {
        &self.C
    }
}

impl<Params: BGVInstantiation> PartialEq for EncodedBGVPlaintextRingBase<Params> {
    fn eq(&self, other: &Self) -> bool {
        self.P.get_ring() == other.P.get_ring() && self.C.get_ring() == other.C.get_ring()
    }
}

impl<Params: BGVInstantiation> DelegateRing for EncodedBGVPlaintextRingBase<Params> {

    type Element = EncodedBGVPlaintextRingEl<Params>;
    type Base = Params::PlaintextRing;

    fn get_delegate(&self) -> &Self::Base {
        self.P.get_ring()
    }

    fn rev_delegate(&self, el: <Self::Base as RingBase>::Element) -> Self::Element {
        let encoded = Params::encode_plain(&self.P, &self.C, &el);
        EncodedBGVPlaintextRingEl {
            encoded: encoded,
            el: el
        }
    }

    fn delegate(&self, el: Self::Element) -> <Self::Base as RingBase>::Element { el.el }
    fn delegate_ref<'a>(&self, el: &'a Self::Element) -> &'a <Self::Base as RingBase>::Element { &el.el }
    fn delegate_mut<'a>(&self, el: &'a mut Self::Element) -> &'a mut <Self::Base as RingBase>::Element { &mut el.el }
}

impl<Params: BGVInstantiation> RingBase for EncodedBGVPlaintextRingBase<Params> {

    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        EncodedBGVPlaintextRingEl {
            el: self.P.clone_el(&val.el),
            encoded: self.C.clone_el(&val.encoded)
        }
    }
}

impl<Params: BGVInstantiation> CanHomFrom<BigIntRingBase> for EncodedBGVPlaintextRingBase<Params> {

    type Homomorphism = <Params::PlaintextZnRing as CanHomFrom<BigIntRingBase>>::Homomorphism;

    fn has_canonical_hom(&self, from: &BigIntRingBase) -> Option<Self::Homomorphism> {
        self.plaintext_ring().base_ring().get_ring().has_canonical_hom(from)
    }

    fn mul_assign_map_in(&self, from: &BigIntRingBase, lhs: &mut Self::Element, rhs: <BigIntRingBase as RingBase>::Element, hom: &Self::Homomorphism) {
        self.plaintext_ring().inclusion().mul_assign_map(self.delegate_mut(lhs), self.plaintext_ring().base_ring().get_ring().map_in(from, rhs, hom));
        self.postprocess_delegate_mut(lhs);
    }

    fn map_in(&self, from: &BigIntRingBase, el: <BigIntRingBase as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.rev_delegate(self.plaintext_ring().inclusion().map(self.plaintext_ring().base_ring().get_ring().map_in(from, el, hom)))
    }
}

impl<Params: BGVInstantiation> EncodedBGVPlaintextRingBase<Params> {

    ///
    /// Returns the encoded representation of `m`, defined over the ciphertext ring `C`. If
    /// `C` is the ring the element was encoded over, this just borrows the stored value;
    /// otherwise, `C` must be a "sub-ring" (obtained by dropping RNS factors) and the encoded
    /// value is adjusted accordingly.
    ///
    fn encoded_for(&self, C: &CiphertextRing<Params>, m: &EncodedBGVPlaintextRingEl<Params>) -> El<CiphertextRing<Params>> {
        if C.get_ring() == self.C.get_ring() {
            self.C.clone_el(&m.encoded)
        } else {
            let dropped = RNSFactorIndexList::missing_from_subset(C.base_ring(), self.C.base_ring()).unwrap();
            C.get_ring().drop_rns_factor_element(self.C.get_ring(), &dropped, &m.encoded)
        }
    }
}

impl<Params: BGVInstantiation> AsBGVPlaintext<Params> for EncodedBGVPlaintextRingBase<Params> {

    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &<Self as RingBase>::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        assert!(self.P.get_ring() == P.get_ring());
        let encoded = self.encoded_for(C, m);
        Params::hom_add_plain_encoded(P, C, &encoded, ct)
    }

    #[instrument(skip_all)]
    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &<Self as RingBase>::Element,
        ct: Ciphertext<Params>
    ) -> Ciphertext<Params> {
        assert!(self.P.get_ring() == P.get_ring());
        let encoded = self.encoded_for(C, m);
        Params::hom_mul_plain_encoded(P, C, &encoded, ct)
    }

    fn hom_inner_product<'a, 'b, I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> Ciphertext<Params>
        where I: IntoIterator<Item = (Boo<'a, Self::Element>, Boo<'b, Ciphertext<Params>>)>,
            Params: 'b,
            Self: 'a
    {
        assert!(self.P.get_ring() == P.get_ring());
        let summands = summands.into_iter().map(|(m, ct)| (Boo::Owned(self.encoded_for(C, &m)), ct)).collect::<Vec<_>>();
        Params::hom_inner_product_plain_encoded(P, C, summands, ImplicitScalePolicy::AssertEqual)
    }

    fn hom_add_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &<Self as RingBase>::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N> {
        estimator.hom_add_plain_encoded(P, C, &self.encoded_for(C, m), ct)
    }

    fn hom_mul_to_noise<N: BGVNoiseEstimator<Params>>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &<Self as RingBase>::Element,
        ct: &CiphertextDescriptor<Params, N>
    ) -> CiphertextDescriptor<Params, N> {
        estimator.hom_mul_plain_encoded(P, C, &self.encoded_for(C, m), ct)
    }

    fn hom_inner_product_noise<'a, 'b, N, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            I: IntoIterator<Item = (&'a Self::Element, &'b CiphertextDescriptor<Params, N>)>,
            Self: 'a,
            Params: 'b,
            N: 'b
    {
        let summands = summands.into_iter().map(|(m, ct)| (self.encoded_for(C, m), ct)).collect::<Vec<_>>();
        estimator.hom_inner_product_plain_encoded(P, C, summands.iter().map(|(m, ct)| (m, ct.borrow())), ImplicitScalePolicy::AssertEqual)
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;

#[test]
fn test_as_bgv_plaintext_ops() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);
    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);

    let ct = Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2);
    let res = P.get_ring().hom_add_to(&P, &C, &P.int_hom().map(5), P.get_ring().hom_mul_to(&P, &C, &P.int_hom().map(3), ct));
    assert_el_eq!(&P, &P.int_hom().map(11), &Pow2BGV::dec(&P, &C, res, &sk));

    // (b) integer constants (BigIntRingBase): 3 * Enc(2) + 5 = 11
    let ct = Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2);
    let res = ZZbig.get_ring().hom_add_to(&P, &C, &int_cast(5, ZZbig, ZZi64), ZZbig.get_ring().hom_mul_to(&P, &C, &int_cast(3, ZZbig, ZZi64), ct));
    assert_el_eq!(&P, &P.int_hom().map(11), &Pow2BGV::dec(&P, &C, res, &sk));

    // (d) relinearized inner product: 2 * Enc(2) + 3 * Enc(5) = 19
    let cts = [
        Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2),
        Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(5), &sk, 3.2)
    ];
    let coeffs = [P.int_hom().map(2), P.int_hom().map(3)];
    let res = P.get_ring().hom_inner_product(&P, &C, coeffs.into_iter().map(Boo::Owned).zip(cts.into_iter().map(Boo::Owned)));
    assert_el_eq!(&P, &P.int_hom().map(19), &Pow2BGV::dec(&P, &C, res, &sk));
}
