
use std::borrow::Borrow;
use tracing::instrument;

use feanor_math::ring::*;
use feanor_math::integer::BigIntRingBase;
use feanor_math::delegate::*;

use crate::prepared_mul::PreparedMultiplicationRing;

use super::noise_estimator::{BGVNoiseEstimator, CiphertextDescriptor};
use super::*;

///
/// Shorthand for the type of an implicit scale value, i.e. an element of `Z/tZ`.
///
type ImplicitScale<Params> = <<Params as BGVInstantiation>::PlaintextZnRing as RingBase>::Element;

///
/// A BGV ciphertext that may or may not have been relinearized; in other words, either a
/// [`Ciphertext`] or a [`CiphertextNoRelin`].
///
/// This is the operand type of all plaintext-ciphertext operations of [`AsBGVPlaintext`].
/// Plaintext-ciphertext operations preserve the relinearization state, and inner products
/// produce an un-relinearized result as soon as any of the summands is un-relinearized
/// (so that lazy relinearization can be propagated through linear combinations).
///
pub enum CiphertextOrNoRelin<Params: ?Sized + BGVInstantiation> {
    Relin(Ciphertext<Params>),
    NoRelin(CiphertextNoRelin<Params>)
}

impl<Params: BGVInstantiation> CiphertextOrNoRelin<Params> {

    ///
    /// Returns the implicit scale of this ciphertext, see [`Ciphertext::implicit_scale`].
    ///
    pub fn implicit_scale(&self) -> &ImplicitScale<Params> {
        match self {
            CiphertextOrNoRelin::Relin(ct) => &ct.implicit_scale,
            CiphertextOrNoRelin::NoRelin(ct) => &ct.implicit_scale
        }
    }

    ///
    /// Returns whether this ciphertext is un-relinearized, i.e. a [`CiphertextNoRelin`].
    ///
    pub fn is_norelin(&self) -> bool {
        matches!(self, CiphertextOrNoRelin::NoRelin(_))
    }

    ///
    /// Turns this into a [`CiphertextNoRelin`]; if it is a [`Ciphertext`], it is promoted by
    /// setting its `c2`-component to zero.
    ///
    pub fn into_norelin(self, C: &CiphertextRing<Params>) -> CiphertextNoRelin<Params> {
        match self {
            CiphertextOrNoRelin::NoRelin(ct) => ct,
            CiphertextOrNoRelin::Relin(ct) => CiphertextNoRelin {
                c0: ct.c0,
                c1: ct.c1,
                c2: C.zero(),
                implicit_scale: ct.implicit_scale
            }
        }
    }

    ///
    /// Unwraps a relinearized [`Ciphertext`], panicking if this is un-relinearized.
    ///
    pub fn unwrap_relin(self) -> Ciphertext<Params> {
        match self {
            CiphertextOrNoRelin::Relin(ct) => ct,
            CiphertextOrNoRelin::NoRelin(_) => panic!("expected a relinearized ciphertext")
        }
    }

    ///
    /// Copies this ciphertext, see [`BGVInstantiation::clone_ct()`].
    ///
    pub fn clone_ct(&self, P: &PlaintextRing<Params>, C: &CiphertextRing<Params>) -> Self {
        match self {
            CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Params::clone_ct(P, C, ct)),
            CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(Params::clone_ct_norelin(P, C, ct))
        }
    }
}

impl<Params: BGVInstantiation> From<Ciphertext<Params>> for CiphertextOrNoRelin<Params> {
    fn from(ct: Ciphertext<Params>) -> Self { CiphertextOrNoRelin::Relin(ct) }
}

impl<Params: BGVInstantiation> From<CiphertextNoRelin<Params>> for CiphertextOrNoRelin<Params> {
    fn from(ct: CiphertextNoRelin<Params>) -> Self { CiphertextOrNoRelin::NoRelin(ct) }
}

///
/// Computes the sum of two (possibly un-relinearized) ciphertexts; the result is
/// un-relinearized as soon as one of the summands is.
///
fn add_ct<Params: BGVInstantiation>(P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, lhs: CiphertextOrNoRelin<Params>, rhs: CiphertextOrNoRelin<Params>, policy: ImplicitScalePolicy) -> CiphertextOrNoRelin<Params> {
    match (lhs, rhs) {
        (CiphertextOrNoRelin::Relin(l), CiphertextOrNoRelin::Relin(r)) => CiphertextOrNoRelin::Relin(Params::hom_add(P, C, l, r, policy)),
        (l, r) => CiphertextOrNoRelin::NoRelin(Params::hom_add_norelin(P, C, l.into_norelin(C), r.into_norelin(C), policy))
    }
}

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
pub trait AsBGVPlaintext<Params: BGVInstantiation>: RingBase {

    ///
    /// Computes a plaintext-ciphertext addition, preserving the relinearization state.
    ///
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: CiphertextOrNoRelin<Params>
    ) -> CiphertextOrNoRelin<Params>;

    ///
    /// Computes a plaintext-ciphertext multiplication, preserving the relinearization state.
    ///
    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: CiphertextOrNoRelin<Params>
    ) -> CiphertextOrNoRelin<Params>;

    ///
    /// Computes the inner product `sum_i m_i * ct_i` of the given plaintexts and ciphertexts.
    ///
    /// The result is un-relinearized as soon as any of the summands is un-relinearized.
    ///
    fn hom_inner_product<I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextOrNoRelin<Params>
        where I: IntoIterator<Item = (Self::Element, CiphertextOrNoRelin<Params>)>
    {
        let mut acc: Option<CiphertextOrNoRelin<Params>> = None;
        for (m, ct) in summands {
            let term = self.hom_mul_to(P, C, &m, ct);
            acc = Some(match acc {
                None => term,
                Some(a) => add_ct(P, C, a, term, ImplicitScalePolicy::Merge)
            });
        }
        acc.unwrap_or_else(|| CiphertextOrNoRelin::Relin(Params::transparent_zero(P, C)))
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
    fn hom_inner_product_noise<N, L, R, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            L: Borrow<Self::Element>,
            R: Borrow<CiphertextDescriptor<Params, N>>,
            I: IntoIterator<Item = (L, R)>
    {
        let mut acc: Option<CiphertextDescriptor<Params, N>> = None;
        for (m, ct) in summands {
            let term = self.hom_mul_to_noise(estimator, P, C, m.borrow(), ct.borrow());
            acc = Some(match acc {
                None => term,
                Some(a) => estimator.hom_add(P, C, &a, &term, ImplicitScalePolicy::Merge)
            });
        }
        acc.unwrap_or_else(|| estimator.transparent_zero(P, C))
    }
}

// Note: this is the impl for `Params::PlaintextRing`. We cannot write
// `impl<Params> AsBGVPlaintext<Params> for Params::PlaintextRing` literally, because an
// associated-type projection in the self-type position is opaque to coherence and would
// be considered as possibly overlapping the `BigIntRingBase` and `EncodedBGVPlaintextRingBase`
// impls below. Instead we spell out the concrete plaintext ring type used by all current
// instantiations and tie it to `Params::PlaintextRing` via a where-clause; this is exactly
// `Params::PlaintextRing` for every `BGVInstantiation`.
impl<Params> AsBGVPlaintext<Params> for NumberRingQuotientByIntBase<NumberRing<Params>, Zn>
    where Params: BGVInstantiation<PlaintextRing = NumberRingQuotientByIntBase<NumberRing<Params>, Zn>>
{
    fn hom_add_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: CiphertextOrNoRelin<Params>
    ) -> CiphertextOrNoRelin<Params> {
        match ct {
            CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Params::hom_add_plain(P, C, m, ct)),
            CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(Params::hom_add_plain_norelin(P, C, m, ct))
        }
    }

    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: CiphertextOrNoRelin<Params>
    ) -> CiphertextOrNoRelin<Params> {
        match ct {
            CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Params::hom_mul_plain(P, C, m, ct)),
            CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(Params::hom_mul_plain_norelin(P, C, m, ct))
        }
    }

    fn hom_inner_product<I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextOrNoRelin<Params>
        where I: IntoIterator<Item = (Self::Element, CiphertextOrNoRelin<Params>)>
    {
        let summands = summands.into_iter().collect::<Vec<_>>();
        if summands.iter().any(|(_, ct)| ct.is_norelin()) {
            let summands = summands.into_iter().map(|(m, ct)| (m, ct.into_norelin(C))).collect::<Vec<_>>();
            CiphertextOrNoRelin::NoRelin(Params::hom_inner_product_plain_norelin(P, C, summands.iter().map(|(m, ct)| (m, ct))))
        } else {
            let summands = summands.into_iter().map(|(m, ct)| (m, ct.unwrap_relin())).collect::<Vec<_>>();
            CiphertextOrNoRelin::Relin(Params::hom_inner_product_plain(P, C, summands.iter().map(|(m, ct)| (m, ct))))
        }
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

    fn hom_inner_product_noise<N, L, R, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            L: Borrow<Self::Element>,
            R: Borrow<CiphertextDescriptor<Params, N>>,
            I: IntoIterator<Item = (L, R)>
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
        ct: CiphertextOrNoRelin<Params>
    ) -> CiphertextOrNoRelin<Params> {
        let scalar = P.base_ring().coerce(&ZZbig, ZZbig.clone_el(m));
        match ct {
            CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Params::hom_add_plain_scalar(P, C, &scalar, ct)),
            CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(Params::hom_add_plain_scalar_norelin(P, C, &scalar, ct))
        }
    }

    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &Self::Element,
        ct: CiphertextOrNoRelin<Params>
    ) -> CiphertextOrNoRelin<Params> {
        let scalar = P.base_ring().coerce(&ZZbig, ZZbig.clone_el(m));
        match ct {
            CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Params::hom_mul_plain_scalar(P, C, &scalar, ct)),
            CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(Params::hom_mul_plain_scalar_norelin(P, C, &scalar, ct))
        }
    }

    fn hom_inner_product<I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextOrNoRelin<Params>
        where I: IntoIterator<Item = (Self::Element, CiphertextOrNoRelin<Params>)>
    {
        let summands = summands.into_iter().map(|(m, ct)| (P.base_ring().coerce(&ZZbig, m), ct)).collect::<Vec<_>>();
        if summands.iter().any(|(_, ct)| ct.is_norelin()) {
            let summands = summands.into_iter().map(|(m, ct)| (m, ct.into_norelin(C))).collect::<Vec<_>>();
            CiphertextOrNoRelin::NoRelin(Params::hom_inner_product_plain_scalar_norelin(P, C, summands.iter().map(|(m, ct)| (m, ct))))
        } else {
            let summands = summands.into_iter().map(|(m, ct)| (m, ct.unwrap_relin())).collect::<Vec<_>>();
            CiphertextOrNoRelin::Relin(Params::hom_inner_product_plain_scalar(P, C, summands.iter().map(|(m, ct)| (m, ct))))
        }
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

    fn hom_inner_product_noise<N, L, R, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            L: Borrow<Self::Element>,
            R: Borrow<CiphertextDescriptor<Params, N>>,
            I: IntoIterator<Item = (L, R)>
    {
        let summands = summands.into_iter().map(|(m, ct)| (P.base_ring().coerce(&ZZbig, ZZbig.clone_el(m.borrow())), ct)).collect::<Vec<_>>();
        estimator.hom_inner_product_plain_scalar(P, C, summands.iter().map(|(m, ct)| (m, ct.borrow())))
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
    encoded: El<CiphertextRing<Params>>,
    prepared: <<CiphertextRing<Params> as RingStore>::Type as PreparedMultiplicationRing>::PreparedMultiplicant
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
        let prepared = self.C.get_ring().prepare_multiplicant(&encoded);
        EncodedBGVPlaintextRingEl {
            prepared: prepared,
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
            encoded: self.C.clone_el(&val.encoded),
            prepared: self.C.get_ring().prepare_multiplicant(&val.encoded)
        }
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
        ct: CiphertextOrNoRelin<Params>
    ) -> CiphertextOrNoRelin<Params> {
        assert!(self.P.get_ring() == P.get_ring());
        let encoded = self.encoded_for(C, m);
        match ct {
            CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Params::hom_add_plain_encoded(P, C, &encoded, ct)),
            CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(Params::hom_add_plain_encoded_norelin(P, C, &encoded, ct))
        }
    }

    #[instrument(skip_all)]
    fn hom_mul_to(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        m: &<Self as RingBase>::Element,
        ct: CiphertextOrNoRelin<Params>
    ) -> CiphertextOrNoRelin<Params> {
        if C.get_ring() == self.C.get_ring() {
            // fast path: use the prepared multiplicant
            let mul = |comp: &El<CiphertextRing<Params>>| C.get_ring().mul_prepared(comp, None, &m.encoded, Some(&m.prepared));
            match ct {
                CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Ciphertext {
                    c0: mul(&ct.c0),
                    c1: mul(&ct.c1),
                    implicit_scale: ct.implicit_scale
                }),
                CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(CiphertextNoRelin {
                    c0: mul(&ct.c0),
                    c1: mul(&ct.c1),
                    c2: mul(&ct.c2),
                    implicit_scale: ct.implicit_scale
                })
            }
        } else {
            let encoded = self.encoded_for(C, m);
            match ct {
                CiphertextOrNoRelin::Relin(ct) => CiphertextOrNoRelin::Relin(Params::hom_mul_plain_encoded(P, C, &encoded, ct)),
                CiphertextOrNoRelin::NoRelin(ct) => CiphertextOrNoRelin::NoRelin(Params::hom_mul_plain_encoded_norelin(P, C, &encoded, ct))
            }
        }
    }

    #[instrument(skip_all)]
    fn hom_inner_product<I>(
        &self,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextOrNoRelin<Params>
        where I: IntoIterator<Item = (Self::Element, CiphertextOrNoRelin<Params>)>
    {
        assert!(self.P.get_ring() == P.get_ring());
        let summands = summands.into_iter().map(|(m, ct)| (self.encoded_for(C, &m), ct)).collect::<Vec<_>>();
        if summands.iter().any(|(_, ct)| ct.is_norelin()) {
            let summands = summands.into_iter().map(|(m, ct)| (m, ct.into_norelin(C))).collect::<Vec<_>>();
            CiphertextOrNoRelin::NoRelin(Params::hom_inner_product_plain_encoded_norelin(P, C, summands.iter().map(|(m, ct)| (m, ct)), ImplicitScalePolicy::AssertEqual))
        } else {
            let summands = summands.into_iter().map(|(m, ct)| (m, ct.unwrap_relin())).collect::<Vec<_>>();
            CiphertextOrNoRelin::Relin(Params::hom_inner_product_plain_encoded(P, C, summands.iter().map(|(m, ct)| (m, ct)), ImplicitScalePolicy::AssertEqual))
        }
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

    fn hom_inner_product_noise<N, L, R, I>(
        &self,
        estimator: &N,
        P: &PlaintextRing<Params>,
        C: &CiphertextRing<Params>,
        summands: I
    ) -> CiphertextDescriptor<Params, N>
        where N: BGVNoiseEstimator<Params>,
            L: Borrow<Self::Element>,
            R: Borrow<CiphertextDescriptor<Params, N>>,
            I: IntoIterator<Item = (L, R)>
    {
        let summands = summands.into_iter().map(|(m, ct)| (self.encoded_for(C, m.borrow()), ct)).collect::<Vec<_>>();
        estimator.hom_inner_product_plain_encoded(P, C, summands.iter().map(|(m, ct)| (m, ct.borrow())), ImplicitScalePolicy::AssertEqual)
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::gadget_product::digits::RNSGadgetVectorDigitIndices;

#[test]
fn test_as_bgv_plaintext_ops() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();
    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);
    let sk = Pow2BGV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BGV::gen_rk(&P, &C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len()), 3.2);

    // (a) plaintext-ring constants: 3 * Enc(2) + 5 = 11
    let ct = CiphertextOrNoRelin::Relin(Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2));
    let res = P.get_ring().hom_add_to(&P, &C, &P.int_hom().map(5), P.get_ring().hom_mul_to(&P, &C, &P.int_hom().map(3), ct));
    assert!(!res.is_norelin());
    assert_el_eq!(&P, &P.int_hom().map(11), &Pow2BGV::dec(&P, &C, res.unwrap_relin(), &sk));

    // (b) integer constants (BigIntRingBase): 3 * Enc(2) + 5 = 11
    let ct = CiphertextOrNoRelin::Relin(Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2));
    let res = ZZbig.get_ring().hom_add_to(&P, &C, &int_cast(5, ZZbig, ZZi64), ZZbig.get_ring().hom_mul_to(&P, &C, &int_cast(3, ZZbig, ZZi64), ct));
    assert_el_eq!(&P, &P.int_hom().map(11), &Pow2BGV::dec(&P, &C, res.unwrap_relin(), &sk));

    // (c) un-relinearized operand stays un-relinearized: 3 * Enc(2)^2 = 12, relinearize at the end
    let base = Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2);
    let sq = CiphertextOrNoRelin::NoRelin(Pow2BGV::hom_square_norelin(&P, &C, &base));
    let res = P.get_ring().hom_mul_to(&P, &C, &P.int_hom().map(3), sq);
    assert!(res.is_norelin());
    let res = Pow2BGV::relinearize(&P, &C, &C, res.into_norelin(&C), &rk);
    assert_el_eq!(&P, &P.int_hom().map(12), &Pow2BGV::dec(&P, &C, res, &sk));

    // (d) relinearized inner product: 2 * Enc(2) + 3 * Enc(5) = 19
    let cts = [
        CiphertextOrNoRelin::Relin(Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2)),
        CiphertextOrNoRelin::Relin(Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(5), &sk, 3.2))
    ];
    let coeffs = [P.int_hom().map(2), P.int_hom().map(3)];
    let res = P.get_ring().hom_inner_product(&P, &C, coeffs.into_iter().zip(cts.into_iter()));
    assert!(!res.is_norelin());
    assert_el_eq!(&P, &P.int_hom().map(19), &Pow2BGV::dec(&P, &C, res.unwrap_relin(), &sk));

    // (e) inner product with a mix of relinearized and un-relinearized summands: Enc(2) + Enc(3)^2 = 11,
    // the result is un-relinearized
    let summands = vec![
        (P.int_hom().map(1), CiphertextOrNoRelin::Relin(Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2))),
        (P.int_hom().map(1), CiphertextOrNoRelin::NoRelin(Pow2BGV::hom_square_norelin(&P, &C, &Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(3), &sk, 3.2))))
    ];
    let res = P.get_ring().hom_inner_product(&P, &C, summands);
    assert!(res.is_norelin());
    let res = Pow2BGV::relinearize(&P, &C, &C, res.into_norelin(&C), &rk);
    assert_el_eq!(&P, &P.int_hom().map(11), &Pow2BGV::dec(&P, &C, res, &sk));

    // (f) encoded plaintext ring: 3 * Enc(2) = 6, using the prepared-multiplicant fast path
    let ER = EncodedBGVPlaintextRingBase::<Pow2BGV>::new(P.clone(), C.clone());
    let m_enc = ER.int_hom().map(3);
    let ct = CiphertextOrNoRelin::Relin(Pow2BGV::enc_sym(&P, &C, &mut rng, &P.int_hom().map(2), &sk, 3.2));
    let res = ER.get_ring().hom_mul_to(&P, &C, &m_enc, ct);
    assert_el_eq!(&P, &P.int_hom().map(6), &Pow2BGV::dec(&P, &C, res.unwrap_relin(), &sk));
}

#[test]
fn test_as_bgv_plaintext_noise() {
    feanor_tracing::DelayedLogger::init_test();
    use super::noise_estimator::{BGVNoiseEstimator, NaiveBGVNoiseEstimator, CiphertextDescriptor};

    let params = Pow2BGV::new(1 << 8);
    let P = params.create_plaintext_ring(int_cast(257, ZZbig, ZZi64));
    let C = params.create_ciphertext_ring(500..520);

    let estimator = NaiveBGVNoiseEstimator;
    let fresh: CiphertextDescriptor<Pow2BGV, _> = estimator.enc_sym(&P, &C, &P.int_hom().map(2), SecretKeyDistribution::UniformTernary);

    // plaintext-ciphertext multiplication increases noise, addition does not
    let after_mul = P.get_ring().hom_mul_to_noise(&estimator, &P, &C, &P.int_hom().map(3), &fresh);
    let after_add = P.get_ring().hom_add_to_noise(&estimator, &P, &C, &P.int_hom().map(5), &fresh);
    assert!(estimator.estimate_log2_relative_noise_level(&P, &C, &after_mul) > estimator.estimate_log2_relative_noise_level(&P, &C, &fresh));
    assert!(estimator.estimate_log2_relative_noise_level(&P, &C, &after_add) <= estimator.estimate_log2_relative_noise_level(&P, &C, &fresh) + 1e-9);

    // inner-product noise is finite and the descriptor is consistent
    let descriptors: [CiphertextDescriptor<Pow2BGV, _>; 2] = [
        estimator.enc_sym(&P, &C, &P.int_hom().map(2), SecretKeyDistribution::UniformTernary),
        estimator.enc_sym(&P, &C, &P.int_hom().map(5), SecretKeyDistribution::UniformTernary)
    ];
    let coeffs = [P.int_hom().map(2), P.int_hom().map(3)];
    let res = P.get_ring().hom_inner_product_noise(&estimator, &P, &C, coeffs.iter().zip(descriptors.iter()));
    assert!(estimator.estimate_log2_relative_noise_level(&P, &C, &res).is_finite());
}
