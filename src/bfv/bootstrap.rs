
use std::cell::LazyCell;
use tracing::Level;
use tracing::event;

use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::delegate::WrapHom;
use feanor_math::homomorphism::*;
use feanor_math::assert_el_eq;
use feanor_math::integer::{int_cast, IntegerRingStore};
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnRingStore;

use crate::bfv::eval::AsBFVPlaintext;
use crate::bfv::eval::EncodedBFVPlaintextRing;
use crate::bfv::eval::EncodedBFVPlaintextRingBase;
use crate::bgv::SecretKeyDistribution;
use crate::bgv::modswitch::compute_optimal_special_modulus;
use crate::circuit::create_circuit_cached;
use crate::poly_eval::digit_extract::DigitExtract;
use crate::lin_transform::composite;
use crate::lin_transform::pow2;

use super::*;

///
/// Precomputed public data that is required to bootstrap BFV ciphertexts
/// over a fixed plaintext and ciphertext ring.
/// 
/// # Example
/// 
/// ```rust
/// # use fheanor::bfv::*;
/// # use fheanor::bfv::bootstrap::*;
/// # use fheanor::gadget_product::digits::RNSGadgetVectorDigitIndices;
/// # use feanor_math::ring::*;
/// # use feanor_math::integer::*;
/// # use feanor_math::primitive_int::*;
/// # use feanor_math::homomorphism::*;
/// # use feanor_math::assert_el_eq;
/// # use feanor_math::seq::*;
/// # use rand::rng;
/// # let ZZbig = BigIntRing::RING;
/// # let ZZi64 = StaticRing::<i64>::RING;
/// // setting up the scheme
/// let params = Pow2BFV::new(1 << 10);
/// let P = params.create_plaintext_ring(int_cast(17, ZZbig, ZZi64));
/// let (C, C_mul) = params.create_ciphertext_rings(420..440);
/// let digits = RNSGadgetVectorDigitIndices::select_digits(5, C.base_ring().len());
/// let bootstrapper = ThinBootstrapper::build_pow2(&params, &P, &C, 2, None, 4, &digits, Some("."));
/// 
/// // creating keys
/// let sk = Pow2BFV::gen_sk(&C, rng(), SecretKeyDistribution::UniformTernary);
/// let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
///     let gk = Pow2BFV::gen_gk(&C, rng(), &sk, &g, &digits, 3.2);
///     (g, gk)
/// }).collect::<Vec<_>>();
/// let rk = Pow2BFV::gen_rk(&C, rng(), &sk, &digits, 3.2);
/// 
/// // sparse key encapsulation is optional, but can make bootstrapping work
/// // with much smaller parameters (e.g. here we use intermediate plaintext modulus
/// // p^v = 17, which wouldn't be possible without sparse key encapsulation).
/// let encaps = SparseKeyEncapsulationKey::new(bootstrapper.intermediate_plaintext_ring(), &C, &sk, 2, 16, rng(), 3.2);
/// 
/// let m = P.int_hom().map(2);
/// let ct = Pow2BFV::enc_sym(&P, &C, rng(), &m, &sk, 3.2);
/// let res_ct = bootstrapper.bootstrap_thin(
///     &C, 
///     &C_mul, 
///     &P, 
///     ct, 
///     &rk, 
///     &gk,
///     Some(&encaps),
///     Some(&sk)
/// );
/// assert_el_eq!(P, P.int_hom().map(2), Pow2BFV::dec(&P, &C, res_ct, &sk));
/// ```
/// 
pub struct ThinBootstrapper<Inst: BFVInstantiation> {
    digit_extract: DigitExtract<Inst::PlaintextRing>,
    slots_to_coeffs_thin: PlaintextCircuit<EncodedBFVPlaintextRingBase<Inst>>,
    coeffs_to_slots_thin: PlaintextCircuit<EncodedBFVPlaintextRingBase<Inst>>,
    /// The plaintext rings `R/p^kR` for every `r < k < e`, which all are used
    /// as intermediate plaintext rings during bootstrapping.
    plaintext_ring_hierarchy: Vec<PlaintextRing<Inst>>,
    slots_to_coeffs_plaintext_ring: EncodedBFVPlaintextRing<Inst>,
    intermediate_plaintext_ring: EncodedBFVPlaintextRing<Inst>
}

impl<Inst: BFVInstantiation> ThinBootstrapper<Inst> {

    ///
    /// Creates a new [`ThinBootstrapper`]. In many cases, it is easier to create
    /// a [`ThinBootstrapper`] using [`ThinBootstrapper::build_pow2()`] or
    /// [`ThinBootstrapper::build_odd()`].
    /// 
    /// Bootstrapping for BFV consists of the following steps.
    ///  - **Slots-to-Coeffs**: Move the values stored in the slots of the input
    ///    ciphertext into its coefficients
    ///  - **Mod-switch**: Modulus-switches the ciphertext to an intermediate
    ///    plaintext modulus `p^e`. This means the ciphertext now can be used
    ///    as a plaintext.
    ///  - **Noisy expansion**: Converts the modulus-switched ciphertext into
    ///    a low-noise ciphertext, which encrypts the same coefficients as the
    ///    the modulus-switched ciphertext, plus some noise. This requires an
    ///    encryption of the secret key.
    ///  - **Coeffs-to-Slots**: Moves the coefficients (with noise) into the
    ///    slots of the ciphertext.
    ///  - **Digit Extraction**: Removes the noise from the encoded values and
    ///    scales them down.
    /// 
    /// The parameters are as follows:
    ///  - `instantiation` describes the scheme whose ciphertexts are to be bootstrapped
    ///  - `C` is the ciphertext ring over which a to-be-bootstrapped input ciphertext 
    ///    should be defined
    ///  - `slots_to_coeffs_thin` is the circuit which is used to compute the 
    ///    Slots-to-Coeffs transform. The coefficients of this circuit should be
    ///    taken from the plaintext ring of the scheme with modulus `t`.
    ///  - `coeffs_to_slots_thin` is the circuit which is used to compute the
    ///    Coeffs-to-Slots transform. The coefficients of this circuit should be
    ///    taken from the plaintext ring of the scheme with modulus `p^e`.
    ///  - `digit_extract` is the function used for digit extraction.
    ///  - `slots_to_coeffs_ciphertext_ring` is a intermediate, reduced-modulus
    ///    ciphertext ring used for the Slots-to-Coeffs transform. More concretely,
    ///    since the result of the Slots-to-Coeffs transform does not have to have
    ///    any noise budget left, the input ciphertext can be mod-switched to a lower
    ///    modulus ciphertext ring before the Slots-to-Coeffs transform, which will
    ///    improve performance of the Slots-to-Coeffs transform. Note that the current
    ///    implementation of BFV does not use hybrid key switching (although it pretends
    ///    to in some cases), and this should be considered when calculating how large
    ///    the modulus of this ring should be.
    /// 
    /// The parameters corresponding to the plaintext space (i.e. `t = p^r`) are
    /// implicitly given through the `digit_extract` parameter.
    /// 
    /// For an example on how to do bootstrapping, see the top-level doc [`ThinBootstrapper`].
    /// 
    #[instrument(skip_all)]
    pub fn create(
        instantiation: &Inst,
        original_plaintext_ring: PlaintextRing<Inst>,
        intermediate_plaintext_ring: PlaintextRing<Inst>,
        C: CiphertextRing<Inst>,
        slots_to_coeffs_thin: PlaintextCircuit<Inst::PlaintextRing>, 
        coeffs_to_slots_thin: PlaintextCircuit<Inst::PlaintextRing>,
        digit_extract: DigitExtract<Inst::PlaintextRing>, 
        slots_to_coeffs_ciphertext_ring: CiphertextRing<Inst>
    ) -> Self {
        let p = digit_extract.p();
        let r = digit_extract.r();
        let e = digit_extract.e();
        let plaintext_ring_hierarchy = ((r + 1)..e).map(|k| instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), k))).collect();
        let slots_to_coeffs_plaintext_ring = EncodedBFVPlaintextRingBase::new(original_plaintext_ring, slots_to_coeffs_ciphertext_ring);
        let intermediate_plaintext_ring = EncodedBFVPlaintextRingBase::new(intermediate_plaintext_ring, C);
        let coeffs_to_slots_thin: PlaintextCircuit<EncodedBFVPlaintextRingBase<Inst>> = coeffs_to_slots_thin.change_ring_uniform(|x| 
            x.change_ring(|x| WrapHom::to_delegate_ring(intermediate_plaintext_ring.get_ring()).map(x))
        );
        let slots_to_coeffs_thin: PlaintextCircuit<EncodedBFVPlaintextRingBase<Inst>> = slots_to_coeffs_thin.change_ring_uniform(|x| 
            x.change_ring(|x| WrapHom::to_delegate_ring(slots_to_coeffs_plaintext_ring.get_ring()).map(x))
        );
        Self {
            digit_extract,
            coeffs_to_slots_thin,
            slots_to_coeffs_thin,
            intermediate_plaintext_ring,
            plaintext_ring_hierarchy,
            slots_to_coeffs_plaintext_ring
        }
    }

    ///
    /// Creates a new [`ThinBootstrapper`] for BFV instantiated over a power-of-two cyclotomic
    /// number ring. This function makes good default choices for the algorithms used in the
    /// various steps of bootstrapping.
    /// 
    /// Parameters:
    ///  - `instantiation` describes the scheme whose ciphertexts are to be bootstrapped.
    ///  - `P` is the plaintext ring which the input ciphertext encrypts an element from.
    ///    Its modulus `t` should be a power of a prime, i.e. `t = p^r`.
    ///  - `C` is the ciphertext ring over which a to-be-bootstrapped input ciphertext 
    ///    should be defined.
    ///  - `v` is the number of digits to remove. In other words, during bootstrapping the
    ///    noise is removed from an intermediate "noisy decryption" using a rounded division
    ///    by `p^v`. Hence, `p^v/2` should be larger than the expected magnitude of the noise,
    ///    after modulus-switching to `p^e` with `e = v + r`.
    ///  - `digit_extract_error_bound` allows to give a tighter bound on the noise. If `p` is
    ///    large, even with `v = 1` the bound on the noise `p^v/2` is often far from tight.
    ///    Setting this to a tighter bound will enable the use of more efficient digit extraction
    ///    polynomials. Note that if this is set, it is required that `v = 1`.
    ///  - `lin_transform_max_levels` maximal number of sequential plaintext-ciphertext multiplications
    ///    performed by the linear transform. Higher values can lead to better performance, while
    ///    lower values improve noise growth.
    ///  - `gk_digits` specifies the gadget vector used for Galois keys. This is required to
    ///    estimate the number of RNS factors used for the Slots-to-Coeffs transform.
    ///  - `cache_dir` specifies a directory to load and store precomputed data. If it is `None`,
    ///    no data will be read or written, but always computed from scratch.
    /// 
    /// For an example on how to do bootstrapping, see the top-level doc [`ThinBootstrapper`].
    /// 
    #[instrument(skip_all)]
    pub fn build_pow2(
        instantiation: &Inst,
        P: &PlaintextRing<Inst>,
        C: &CiphertextRing<Inst>, 
        v: usize,
        digit_extract_error_bound: Option<i64>,
        lin_transform_max_levels: usize,
        gk_digits: &RNSGadgetVectorDigitIndices, 
        cache_dir: Option<&str>
    ) -> Self
        where Inst::PlaintextRing: SerializableElementRing,
            Inst::CiphertextRing: Clone
    {
        let log2_m = ZZi64.abs_log2_ceil(&(instantiation.number_ring().galois_group().m() as i64)).unwrap();
        assert_eq!(instantiation.number_ring().galois_group().m(), 1 << log2_m);

        let t = int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZbig, P.base_ring().integer_ring());
        let (p, r) = is_prime_power(&ZZbig, &t).unwrap();
        let e = r + v;
        event!(Level::INFO, p = %&ZZbig.format(&p), e = e, r = r, v = v);

        let intermediate_plaintext_ring = instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), e));
        let base_plaintext_ring = instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r));
        let plaintext_ring_hierarchy = ((r + 1)..e).map(|k| instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), k))).collect::<Vec<_>>();
        let all_plaintext_rings = [&base_plaintext_ring].into_iter().chain(plaintext_ring_hierarchy.iter()).chain([&intermediate_plaintext_ring]).collect::<Vec<_>>();

        let hypercube = HypercubeStructure::default_pow2_hypercube(intermediate_plaintext_ring.acting_galois_group(), ZZbig.clone_el(&p));
        let H = LazyCell::new(|| HypercubeIsomorphism::new(&intermediate_plaintext_ring, &hypercube, cache_dir));
        let base_H = LazyCell::new(|| H.change_modulus(&base_plaintext_ring));

        let m = intermediate_plaintext_ring.number_ring().galois_group().m();
        let slots_to_coeffs = create_circuit_cached(&base_plaintext_ring, &filename_keys![slots2coeffs, m: m, p: &p, r: r, levels: lin_transform_max_levels], cache_dir, || pow2::slots_to_coeffs_thin(&base_H, lin_transform_max_levels));
        let coeffs_to_slots = create_circuit_cached(&intermediate_plaintext_ring, &filename_keys![coeffs2slots, m: m, p: &p, e: e, levels: lin_transform_max_levels], cache_dir, || pow2::coeffs_to_slots_thin(&H, lin_transform_max_levels));
        let digit_extract = DigitExtract::new_default(&all_plaintext_rings, &H, digit_extract_error_bound, cache_dir);

        // we estimate the noise growth of the slots-to-coeffs transform as `log2(|Gal|)` multiplications by
        // ring elements of size at most `t`
        let min_rns_factor_log2 = C.base_ring().as_iter().map(|rns_factor| *rns_factor.modulus() as i64).map(|rns_factor| (rns_factor as f64).log2()).min_by(f64::total_cmp).unwrap();
        let slots_to_coeffs_rns_factors = ((ZZbig.abs_log2_ceil(&t).unwrap() as f64 + P.number_ring().coeff_basis_product_expansion_factor().log2()) * (P.acting_galois_group().group_order() as f64).log2() / min_rns_factor_log2).ceil() as usize; 
        let slots_to_coeffs_ciphertext_ring = {
            let (drop_additional, special_modulus) = compute_optimal_special_modulus(C.get_ring(), RNSFactorIndexList::empty_ref(), C.base_ring().len().saturating_sub(slots_to_coeffs_rns_factors), gk_digits);
            RingValue::from(C.get_ring().drop_rns_factor(&drop_additional.subtract(&special_modulus)))
        };

        return Self::create(
            instantiation, 
            base_plaintext_ring,
            intermediate_plaintext_ring,
            C.clone(),
            slots_to_coeffs, 
            coeffs_to_slots,
            digit_extract, 
            slots_to_coeffs_ciphertext_ring
        );
    }

    ///
    /// Creates a new [`ThinBootstrapper`] for BFV instantiated over an odd cyclotomic
    /// number ring. This function makes good default choices for the algorithms used in the
    /// various steps of bootstrapping.
    /// 
    /// Parameters:
    ///  - `instantiation` describes the scheme whose ciphertexts are to be bootstrapped.
    ///  - `P` is the plaintext ring which the input ciphertext encrypts an element from.
    ///    Its modulus `t` should be a power of a prime, i.e. `t = p^r`.
    ///  - `C` is the ciphertext ring over which a to-be-bootstrapped input ciphertext 
    ///    should be defined.
    ///  - `v` is the number of digits to remove. In other words, during bootstrapping the
    ///    noise is removed from an intermediate "noisy decryption" using a rounded division
    ///    by `p^v`. Hence, `p^v/2` should be larger than the expected magnitude of the noise,
    ///    after modulus-switching to `p^e` with `e = v + r`.
    ///  - `digit_extract_error_bound` allows to give a tighter bound on the noise. If `p` is
    ///    large, even with `v = 1` the bound on the noise `p^v/2` is often far from tight.
    ///    Setting this to a tighter bound will enable the use of more efficient digit extraction
    ///    polynomials. Note that if this is set, it is required that `v = 1`.
    ///  - `lin_transform_max_levels` maximal number of sequential plaintext-ciphertext multiplications
    ///    performed by the linear transform. Higher values can lead to better performance, while
    ///    lower values improve noise growth.
    ///  - `gk_digits` specifies the gadget vector used for Galois keys. This is required to
    ///    estimate the number of RNS factors used for the Slots-to-Coeffs transform.
    ///  - `cache_dir` specifies a directory to load and store precomputed data. If it is `None`,
    ///    no data will be read or written, but always computed from scratch.
    /// 
    /// For an example on how to do bootstrapping, see the top-level doc [`ThinBootstrapper`].
    /// 
    #[instrument(skip_all)]
    pub fn build_odd(
        instantiation: &Inst,
        P: &PlaintextRing<Inst>,
        C: &CiphertextRing<Inst>, 
        v: usize,
        digit_extract_error_bound: Option<i64>,
        lin_transform_max_levels: usize,
        gk_digits: &RNSGadgetVectorDigitIndices, 
        cache_dir: Option<&str>
    ) -> Self
        where Inst::PlaintextRing: SerializableElementRing,
            Inst::CiphertextRing: Clone
    {
        assert!(instantiation.number_ring().galois_group().m() % 2 != 0);

        let t = int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZbig, P.base_ring().integer_ring());
        let (p, r) = is_prime_power(&ZZbig, &t).unwrap();
        let e = r + v;
        event!(Level::INFO, p = %&ZZbig.format(&p), e = e, r = r, v = v);

        let intermediate_plaintext_ring = instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), e));
        let base_plaintext_ring = instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r));
        let plaintext_ring_hierarchy = ((r + 1)..e).map(|k| instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), k))).collect::<Vec<_>>();
        let all_plaintext_rings = [&base_plaintext_ring].into_iter().chain(plaintext_ring_hierarchy.iter()).chain([&intermediate_plaintext_ring]).collect::<Vec<_>>();

        let hypercube = HypercubeStructure::halevi_shoup_hypercube(intermediate_plaintext_ring.acting_galois_group(), ZZbig.clone_el(&p));
        let H = LazyCell::new(|| HypercubeIsomorphism::new(&intermediate_plaintext_ring, &hypercube, cache_dir));
        let base_H = LazyCell::new(|| H.change_modulus(&base_plaintext_ring));

        let m = intermediate_plaintext_ring.number_ring().galois_group().m();
        let slots_to_coeffs = create_circuit_cached(&base_plaintext_ring, &filename_keys![slots2coeffs, m: m, p: &p, r: r, levels: lin_transform_max_levels], cache_dir, || composite::slots_to_powcoeffs_thin(&base_H, lin_transform_max_levels));
        let coeffs_to_slots = create_circuit_cached(&intermediate_plaintext_ring, &filename_keys![coeffs2slots, m: m, p: &p, e: e, levels: lin_transform_max_levels], cache_dir, || composite::powcoeffs_to_slots_thin(&H, lin_transform_max_levels));
        let digit_extract = DigitExtract::new_default(&all_plaintext_rings, &H, digit_extract_error_bound, cache_dir);

        // we estimate the noise growth of the slots-to-coeffs transform as `log2(m)` multiplications by
        // ring elements of size at most `t`
        let min_rns_factor_log2 = C.base_ring().as_iter().map(|rns_factor| *rns_factor.modulus() as i64).map(|rns_factor| (rns_factor as f64).log2()).min_by(f64::total_cmp).unwrap();
        let slots_to_coeffs_rns_factors = ((ZZbig.abs_log2_ceil(&t).unwrap() as f64 + P.number_ring().coeff_basis_product_expansion_factor().log2()) * (hypercube.dim_count() as f64 + 1.0) / min_rns_factor_log2).ceil() as usize; 
        let slots_to_coeffs_ciphertext_ring = {
            let (drop_additional, special_modulus) = compute_optimal_special_modulus(C.get_ring(), RNSFactorIndexList::empty_ref(), C.base_ring().len().saturating_sub(slots_to_coeffs_rns_factors), gk_digits);
            RingValue::from(C.get_ring().drop_rns_factor(&drop_additional.subtract(&special_modulus)))
        };

        return Self::create(
            instantiation, 
            base_plaintext_ring,
            intermediate_plaintext_ring,
            C.clone(),
            slots_to_coeffs, 
            coeffs_to_slots,
            digit_extract, 
            slots_to_coeffs_ciphertext_ring
        );
    }

    ///
    /// Replaces the digit extraction object used by this bootstrapper.
    /// 
    pub fn with_digit_extraction(self, new_digit_extraction: DigitExtract<Inst::PlaintextRing>) -> Self {
        assert_el_eq!(ZZbig, self.digit_extract.p(), new_digit_extraction.p());
        assert_eq!(self.digit_extract.r(), new_digit_extraction.r());
        assert_eq!(self.digit_extract.e(), new_digit_extraction.e());
        Self {
            coeffs_to_slots_thin: self.coeffs_to_slots_thin,
            digit_extract: new_digit_extraction,
            intermediate_plaintext_ring: self.intermediate_plaintext_ring,
            plaintext_ring_hierarchy: self.plaintext_ring_hierarchy,
            slots_to_coeffs_plaintext_ring: self.slots_to_coeffs_plaintext_ring,
            slots_to_coeffs_thin: self.slots_to_coeffs_thin
        }
    }
    
    pub fn r(&self) -> usize {
        self.digit_extract.e() - self.digit_extract.v()
    }

    pub fn e(&self) -> usize {
        self.digit_extract.e()
    }

    pub fn v(&self) -> usize {
        self.digit_extract.v()
    }

    pub fn p(&self) -> El<BigIntRing> {
        ZZbig.clone_el(self.digit_extract.p())
    }

    ///
    /// The plaintext ring w.r.t. which the output of noisy expansion is defined.
    /// This is also used for the coefficients-to-slots transform and at the beginning
    /// of digit extraction.
    /// 
    pub fn intermediate_plaintext_ring(&self) -> &PlaintextRing<Inst> {
        self.intermediate_plaintext_ring.get_ring().plaintext_ring()
    }

    ///
    /// The plaintext ring w.r.t. which the input ciphertext is defined.
    /// 
    pub fn base_plaintext_ring(&self) -> &PlaintextRing<Inst> {
        self.slots_to_coeffs_plaintext_ring.get_ring().plaintext_ring()
    }

    ///
    /// The ciphertext ring over which we perform the slots-to-coefficients
    /// transform. This is usually much smaller than the original ciphertext ring,
    /// since the slots-to-coefficients transform causes relatively low noise growth,
    /// and thus choosing a smaller ciphertext modulus can save performance.
    /// 
    pub fn slots_to_coeffs_ciphertext_ring(&self) -> &CiphertextRing<Inst> {
        self.slots_to_coeffs_plaintext_ring.get_ring().ciphertext_ring()
    }

    ///
    /// The ciphertext ring over which the output of bootstrapping will be defined.
    /// This is also the ciphertext ring used for the coefficients-to-slots transform
    /// and for digit extraction.
    /// 
    pub fn main_ciphertext_ring(&self) -> &CiphertextRing<Inst> {
        self.intermediate_plaintext_ring.get_ring().ciphertext_ring()
    }

    ///
    /// Returns the sequence of plaintext rings `R/p^rR`, ..., `R/p^eR`, which are
    /// all plaintext rings used at some point during bootstrapping.
    /// 
    pub fn complete_plaintext_ring_sequence<'a>(&'a self) -> Vec<&'a PlaintextRing<Inst>> {
        [self.base_plaintext_ring()].into_iter().chain(self.plaintext_ring_hierarchy.iter()).chain([self.intermediate_plaintext_ring()]).collect::<Vec<_>>()
    }

    pub fn required_galois_keys(&self, P: &PlaintextRing<Inst>) -> Vec<GaloisGroupEl> {
        let mut result = Vec::new();
        result.extend(self.slots_to_coeffs_thin.required_galois_keys(&P.acting_galois_group()).into_iter());
        result.extend(self.coeffs_to_slots_thin.required_galois_keys(&P.acting_galois_group()).into_iter());
        result.extend(self.digit_extract.required_galois_keys(&P.acting_galois_group()).into_iter());
        result.sort_by_key(|g| P.acting_galois_group().representative(g));
        result.dedup_by(|g, s| P.acting_galois_group().eq_el(g, s));
        return result;
    }

    #[instrument(skip_all)]
    fn perform_slots_to_coefficients(
        &self, 
        ct: Ciphertext<Inst>,
        gks: &[(GaloisGroupEl, KeySwitchKey<Inst>)],
        debug_sk: Option<&SecretKey<Inst>>
    ) -> Ciphertext<Inst> {
        let C = self.main_ciphertext_ring();
        let P = self.base_plaintext_ring();
        let C_input = self.slots_to_coeffs_ciphertext_ring();
        let ct_input = Inst::mod_switch_ct(P, &C_input, C, ct);
        let C_to_C_input_drop_factors = RNSFactorIndexList::missing_from(C_input.base_ring(), C.base_ring());

        let galois_group = P.acting_galois_group();
        let modswitched_gks = self.slots_to_coeffs_thin.required_galois_keys(&galois_group).iter().map(|g| {
            if let Some((_, gk)) = gks.iter().filter(|(provided_g, _)| galois_group.eq_el(g, provided_g)).next() {
                (g.clone(), (
                    gk.0.clone(C.get_ring()).modulus_switch(C_input.get_ring(), &C_to_C_input_drop_factors, C.get_ring()),
                    gk.1.clone(C.get_ring()).modulus_switch(C_input.get_ring(), &C_to_C_input_drop_factors, C.get_ring()), 
                ))
            } else {
                panic!("missing galois key for {}", galois_group.underlying_ring().format(galois_group.as_ring_el(g)))
            }
        }).collect::<Vec<_>>();
        let result = self.slots_to_coeffs_thin.evaluate_bfv::<Inst, _>(
            &self.slots_to_coeffs_plaintext_ring, 
            P, 
            &C_input, 
            None, 
            std::slice::from_ref(&ct_input), 
            None, 
            &modswitched_gks, 
            None
        );
        assert_eq!(1, result.len());
        let result = result.into_iter().next().unwrap();

        let sk_input = debug_sk.map(|sk| C_input.get_ring().drop_rns_factor_element(C.get_ring(), &C_to_C_input_drop_factors, &sk));
        if let Some(sk) = &sk_input {
            Inst::dec_println(P, &C_input, &result, sk);
        }
        return result;
    }

    #[instrument(skip_all)]
    fn perform_noisy_expansion(
        &self,
        ct: Ciphertext<Inst>,
        sk_encaps_data: Option<&SparseKeyEncapsulationKey<Inst>>,
        debug_sk: Option<&SecretKey<Inst>>
    ) -> Ciphertext<Inst> {
        let C_input = self.slots_to_coeffs_ciphertext_ring();
        let C = self.main_ciphertext_ring();
        let P = self.base_plaintext_ring();
        let P_main = self.intermediate_plaintext_ring();
        let result = if let Some(sk_encaps_data) = sk_encaps_data {
            let ct_with_sparse_key = {
                let ct_modswitched = Inst::mod_switch_ct(&P, &sk_encaps_data.C_sparse_sk, &C_input, ct);
                Inst::key_switch(&sk_encaps_data.C_sparse_sk, ct_modswitched, &sk_encaps_data.switch_to_sparse_key)
            };
            if let Some(sk) = &debug_sk {
                Inst::dec_println(P, &sk_encaps_data.C_sparse_sk, &ct_with_sparse_key, &Inst::mod_switch_sk(P, &sk_encaps_data.C_sparse_sk, C, sk));
            }
            let (c0, c1) = Inst::mod_switch_to_plaintext(P_main, &sk_encaps_data.C_sparse_sk, ct_with_sparse_key);
            Inst::hom_add_plain(P_main, C, &c0, Inst::hom_mul_plain(P_main, C, &c1, Inst::clone_ct(C, &sk_encaps_data.encapsulated_key)))
        } else {
            let (c0, c1) = Inst::mod_switch_to_plaintext(P_main, &C_input, ct);
            let enc_sk = Inst::enc_sk(P_main, C);
            Inst::hom_add_plain(P_main, C, &c0, Inst::hom_mul_plain(P_main, C, &c1, enc_sk))
        };
        if let Some(sk) = debug_sk {
            Inst::dec_println(P_main, C, &result, sk);
        }
        return result;
    }

    #[instrument(skip_all)]
    fn perform_coefficients_to_slots(
        &self, 
        ct: Ciphertext<Inst>,
        gks: &[(GaloisGroupEl, KeySwitchKey<Inst>)],
        debug_sk: Option<&SecretKey<Inst>>
    ) -> Ciphertext<Inst> {
        let P_main = self.intermediate_plaintext_ring();
        let result = self.coeffs_to_slots_thin.evaluate_bfv::<Inst, _>(
            &self.intermediate_plaintext_ring, 
            P_main, 
            self.main_ciphertext_ring(),
            None, 
            std::slice::from_ref(&ct), 
            None, 
            gks, 
            None
        );
        assert_eq!(1, result.len());
        let result = result.into_iter().next().unwrap();
        if let Some(sk) = debug_sk {
            Inst::dec_println_slots(P_main, self.main_ciphertext_ring(), &result, sk, None);
        }
        return result;
    }

    #[instrument(skip_all)]
    fn perform_digit_extraction(
        &self, 
        C_mul: &CiphertextRing<Inst>,
        ct: Ciphertext<Inst>,
        rk: &RelinKey<Inst>,
        debug_sk: Option<&SecretKey<Inst>>
    ) -> Ciphertext<Inst> {
        let C = self.main_ciphertext_ring();
        let plaintext_rings = self.complete_plaintext_ring_sequence();
        self.digit_extract.evaluate_bfv::<_, Inst>(&plaintext_rings, &plaintext_rings, C, C_mul, ct, rk, debug_sk).0
    }

    ///
    /// Performs bootstrapping on thinly packed ciphertexts.
    /// 
    /// Parameters are as follows:
    ///  - `C` is the ciphertext ring w.r.t. which both input and output ciphertexts are defined
    ///  - `C_mul` is the extended ciphertext ring used for multiplications
    ///  - `ct` is the ciphertext to bootstrap; It must be thinly packed (i.e. each slot may only
    ///    contain an element of `Z/(t)`), otherwise this function will cause immediate noise overflow.
    ///  - `rk` is a relinearization key, to be used for computing products
    ///  - `gks` is a list of Galois keys, to be used for applying Galois automorphisms. This list
    ///    must contain a Galois key for each Galois automorphism listed in [`ThinBootstrapper::required_galois_keys()`],
    ///    but may contain additional Galois keys
    ///  - `sparse_key_encapsulation` optionally contains all data required to temporarily switch
    ///    to a sparse secret key before bootstrapping. If used, this can make bootstrapping work
    ///    with significantly smaller parameters.
    ///  - `debug_sk` can be a reference to a secret key, which is used to print out decryptions
    ///    of intermediate results for debugging purposes. May only be set if `LOG == true`.
    /// 
    /// For an example on how to do bootstrapping, see the top-level doc [`ThinBootstrapper`].
    /// 
    #[instrument(skip_all)]
    pub fn bootstrap_thin(
        &self,
        C: &CiphertextRing<Inst>, 
        C_mul: &CiphertextRing<Inst>, 
        ct: Ciphertext<Inst>,
        rk: &RelinKey<Inst>,
        gks: &[(GaloisGroupEl, KeySwitchKey<Inst>)],
        sk_encaps_data: Option<&SparseKeyEncapsulationKey<Inst>>,
        debug_sk: Option<&SecretKey<Inst>>
    ) -> Ciphertext<Inst> {
        assert!(self.main_ciphertext_ring().get_ring() == C.get_ring());

        let values_in_coefficients = self.perform_slots_to_coefficients(ct, gks, debug_sk);

        let noisy_decryption = self.perform_noisy_expansion(values_in_coefficients, sk_encaps_data, debug_sk);

        let noisy_decryption_in_slots = self.perform_coefficients_to_slots(noisy_decryption, gks, debug_sk);
        
        return self.perform_digit_extraction(C_mul, noisy_decryption_in_slots, rk, debug_sk);
    }
}

///
/// Data required for performing thin bootstrapping with sparse key encapsulation.
/// 
/// Sparse key encapsulation refers to key-switching a ciphertext to a sparse secret key
/// just before homomorphic decryption (which happens at a very low ciphertext modulus,
/// which can offset the security loss due to key sparsity), and thus introduce much less
/// noise that has to be homomorphically removed.
/// 
pub struct SparseKeyEncapsulationKey<Inst: BFVInstantiation> {
    ///
    /// Ciphertext ring with small modulus, over which encryptions with the
    /// sparse key remain secure.
    /// 
    pub C_sparse_sk: CiphertextRing<Inst>,
    ///
    /// Key-switch key to switch a ciphertext encrypted by the standard key
    /// to a ciphertext encrypted by the sparse key.
    /// 
    /// This is defined w.r.t. the switch-to-sparse ciphertext ring, which has
    /// a significantly smaller modulus than the standard ciphertext ring. This
    /// is necessary for security.
    /// 
    pub switch_to_sparse_key: KeySwitchKey<Inst>,
    ///
    /// An encryption of the sparse secret key (mapped into the plaintext ring
    /// by taking a shortest lift to `R`) w.r.t. the standard secret key.
    /// 
    pub encapsulated_key: Ciphertext<Inst>
}

impl<Params> SparseKeyEncapsulationKey<Params>
    where Params: BFVInstantiation, 
        Params::PlaintextRing: AsBFVPlaintext<Params>
{
    pub fn create<R: CryptoRng + Rng>(P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_sparse_sk: CiphertextRing<Params>, sparse_sk: SecretKey<Params>, standard_sk: &SecretKey<Params>, mut rng: R, noise_sigma: f64) -> Self {
        let switch_to_sparse_key = Params::gen_switch_key(
            &C_sparse_sk, 
            &mut rng,
            &Params::mod_switch_sk(P, &C_sparse_sk, C, standard_sk),
            &sparse_sk,
            &RNSGadgetVectorDigitIndices::select_digits(C_sparse_sk.base_ring().len(), C_sparse_sk.base_ring().len()),
            noise_sigma
        );
        let ZZ_to_Pbase = P.base_ring().can_hom(P.base_ring().integer_ring()).unwrap().compose(P.base_ring().integer_ring().can_hom(&ZZbig).unwrap());
        let sparse_sk_as_plain = P.from_canonical_basis(C_sparse_sk.wrt_canonical_basis(&sparse_sk).iter().map(|x| ZZ_to_Pbase.map(C_sparse_sk.base_ring().smallest_lift(x))));
        let encapsulated_key = Params::enc_sym(P, C, &mut rng, &sparse_sk_as_plain, standard_sk, noise_sigma);
        SparseKeyEncapsulationKey { 
            switch_to_sparse_key: switch_to_sparse_key, 
            encapsulated_key: encapsulated_key,
            C_sparse_sk: C_sparse_sk
        }
    }

    pub fn new<R: CryptoRng + Rng>(P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, standard_sk: &SecretKey<Params>, C_sparse_rns_factor_count: usize, hwt: usize, mut rng: R, noise_sigma: f64) -> Self {
        let C_sparse_sk = RingValue::from(C.get_ring().drop_rns_factor(&RNSFactorIndexList::from(C_sparse_rns_factor_count..C.base_ring().len(), C.base_ring().len())));
        let sparse_sk = Params::gen_sk(&C_sparse_sk, &mut rng, SecretKeyDistribution::SparseWithHwt(hwt));
        return Self::create(P, C, C_sparse_sk, sparse_sk, standard_sk, rng, noise_sigma);
    }
}

impl<R: ?Sized + RingBase> DigitExtract<R> {
    
    ///
    /// Evaluates the digit extraction function on a BFV-encrypted input.
    /// 
    /// For details on how the digit extraction function looks like, see
    /// [`DigitExtract`] and [`DigitExtract::evaluate_generic()`].
    /// 
    pub fn evaluate_bfv<S, Inst>(&self, 
        rings: &[S],
        P: &[&PlaintextRing<Inst>],
        C: &CiphertextRing<Inst>, 
        C_mul: &CiphertextRing<Inst>, 
        input: Ciphertext<Inst>, 
        rk: &RelinKey<Inst>,
        debug_sk: Option<&SecretKey<Inst>>
    ) -> (Ciphertext<Inst>, Ciphertext<Inst>)
        where Inst: BFVInstantiation,
            R: AsBFVPlaintext<Inst>,
            S: RingStore<Type = R> + Copy
    {
        let ZZ = P[0].base_ring().integer_ring();
        let (p, actual_r) = is_prime_power(ZZ, P[0].base_ring().modulus()).unwrap();
        assert!(actual_r >= self.r());
        assert_eq!(self.v() + 1, P.len());
        assert_eq!(self.v() + 1, rings.len());
        assert_el_eq!(ZZbig, self.p(), int_cast(ZZ.clone_el(&p), ZZbig, ZZ));
        for i in 0..=self.v() {
            assert_el_eq!(ZZbig, ZZbig.pow(ZZbig.clone_el(self.p()), actual_r + i), int_cast(ZZ.clone_el(P[i].base_ring().modulus()), ZZbig, ZZ));
        }

        let result = self.evaluate_generic(
            input,
            |exp, params, circuit| {
                circuit.evaluate_bfv::<Inst, _>(
                    &rings[exp - self.r()],
                    P[exp - self.r()],
                    C,
                    Some(C_mul),
                    params,
                    Some(rk),
                    &[],
                    debug_sk
                )
            },
            |exp_from, _, x| {
                if let Some(sk) = debug_sk {
                    Inst::dec_println_slots(P[exp_from - self.r()], C, &x, sk, Some("."));
                }
                return x;
            }
        );
        return result;
    }
}

#[test]
fn test_digit_extract_homomorphic() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();

    let params = Pow2BFV::new(1 << 7);
    let P1 = params.create_plaintext_ring(int_cast(17 * 17, ZZbig, ZZi64));
    let P2 = params.create_plaintext_ring(int_cast(17 * 17 * 17, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(790..800);

    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(7, C.base_ring().len()), 3.2);
    let m = P2.int_hom().map(17 * 17 + 2 * 17 + 5);
    let ct = Pow2BFV::enc_sym(&P2, &C, &mut rng, &m, &sk, 3.2);

    let digitextract = DigitExtract::new_digit_retain_based(&[P1.base_ring(), P2.base_ring()]);
    let (ct_high, ct_low) = digitextract.evaluate_bfv::<_, Pow2BFV>(&[P1.base_ring(), P2.base_ring()], &[&P1, &P2], &C, &C_mul, ct, &rk, Some(&sk));
    let m_high = Pow2BFV::dec(&P1, &C, Pow2BFV::clone_ct(&C, &ct_high), &sk);
    assert!(P1.wrt_canonical_basis(&m_high).iter().skip(1).all(|x| P1.base_ring().is_zero(&x)));
    let m_high = P1.base_ring().smallest_lift(P1.wrt_canonical_basis(&m_high).at(0));
    assert_eq!(17 + 2, m_high);
    
    let m_low = Pow2BFV::dec(&P2, &C, Pow2BFV::clone_ct(&C, &ct_low), &sk);
    assert!(P2.wrt_canonical_basis(&m_low).iter().skip(1).all(|x| P2.base_ring().is_zero(&x)));
    let m_low = P2.base_ring().smallest_lift(P2.wrt_canonical_basis(&m_low).at(0));
    assert_eq!(5, m_low);
}

#[test]
fn test_pow2_bfv_thin_bootstrapping_17() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();
    
    // 8 slots of rank 16
    let params = Pow2BFV::new(1 << 8);
    let t = 17;
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(790..800);
    let digits = RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_pow2(&params, &P, &C, 2, None, 4, &digits, Some("."));
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BFV::gen_gk(&C, &mut rng, &sk, &g, &digits, 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &digits, 3.2);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin(
        &C, 
        &C_mul, 
        ct, 
        &rk, 
        &gk,
        None,
        Some(&sk)
    );

    Pow2BFV::dec_println_slots(&P, &C, &res_ct, &sk, Some("."));

    assert_el_eq!(P, P.int_hom().map(2), Pow2BFV::dec(&P, &C, res_ct, &sk));
}

#[test]
fn test_pow2_bfv_thin_bootstrapping_23() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();
    
    // 4 slots of rank 32
    let params = Pow2BFV::new(1 << 8);
    let t = 23;
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(790..800);
    let digits = RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_pow2(&params, &P, &C, 2, None, 4, &digits, Some("."));
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BFV::gen_gk(&C, &mut rng, &sk, &g, &digits, 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &digits, 3.2);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin(
        &C, 
        &C_mul, 
        ct, 
        &rk, 
        &gk,
        None,
        None
    );

    assert_el_eq!(P, P.int_hom().map(2), Pow2BFV::dec(&P, &C, res_ct, &sk));
}

#[test]
fn test_pow2_bfv_thin_bootstrapping_sparse_key_encapsulation() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();
    
    let params = Pow2BFV::new(1 << 8);
    let t = 17;
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(790..800);
    let digits = RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_pow2(&params, &P, &C, 2, None, 4, &digits, Some("."));
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BFV::gen_gk(&C, &mut rng, &sk, &g, &digits, 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &digits, 3.2);
    let encaps = SparseKeyEncapsulationKey::new(bootstrapper.intermediate_plaintext_ring(), &C, &sk, 2, 16, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin(
        &C, 
        &C_mul, 
        ct, 
        &rk, 
        &gk,
        Some(&encaps),
        Some(&sk)
    );

    assert_el_eq!(P, P.int_hom().map(2), Pow2BFV::dec(&P, &C, res_ct, &sk));
}

#[test]
fn test_composite_bfv_thin_bootstrapping_2() {
    feanor_tracing::DelayedLogger::init_test();
    let mut rng = rand::rng();
    
    let params = CompositeBFV::new(31, 11);
    let t = 8;
    
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(685..700);
    let digits = RNSGadgetVectorDigitIndices::select_digits(3, C.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_odd(&params, &P, &C, 9, None, 4, &digits, Some("."));
    
    let sk = CompositeBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeBFV::gen_gk(&C, &mut rng, &sk, &g, &digits, 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = CompositeBFV::gen_rk(&C, &mut rng, &sk, &digits, 3.2);
    
    let m = P.int_hom().map(2);
    let ct = CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin(
        &C, 
        &C_mul, 
        ct, 
        &rk, 
        &gk,
        None,
        None
    );

    assert_el_eq!(P, P.int_hom().map(2), CompositeBFV::dec(&P, &C, res_ct, &sk));
}

#[test]
#[ignore]
fn measure_time_double_rns_composite_bfv_thin_bootstrapping() {
    feanor_tracing::DelayedLogger::init_test();
    
    let mut rng = rand::rng();
    
    let params = CompositeBFV::new(37, 949);
    let t = 4;
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(805..820);
    let gk_digits = RNSGadgetVectorDigitIndices::select_digits(7, C.base_ring().len());
    let rk_digits = RNSGadgetVectorDigitIndices::select_digits(5, C.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_odd(&params, &P, &C, 6, None, 4, &gk_digits, Some("."));
    
    let sk = CompositeBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeBFV::gen_gk(&C, &mut rng, &sk, &g, &gk_digits, 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = CompositeBFV::gen_rk(&C, &mut rng, &sk, &rk_digits, 3.2);
    let encaps = SparseKeyEncapsulationKey::new(bootstrapper.intermediate_plaintext_ring(), &C, &sk, 2, 32, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin(
        &C, 
        &C_mul, 
        ct, 
        &rk, 
        &gk,
        Some(&encaps),
        None
    );

    println!("final noise budget: {}", CompositeBFV::noise_budget(&P, &C, &res_ct, &sk));
    assert_el_eq!(P, P.int_hom().map(2), CompositeBFV::dec(&P, &C, res_ct, &sk));
}

#[test]
#[ignore]
fn measure_time_double_rns_pow2_bfv_thin_bootstrapping_t257_sqr() {
    feanor_tracing::DelayedLogger::init_test();
    
    let mut rng = rand::rng();
    
    let params = Pow2BFV::new(1 << 16);
    let t = 257 * 257;
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(805..820);
    let gk_digits = RNSGadgetVectorDigitIndices::select_digits(C.base_ring().len().div_ceil(2), C.base_ring().len());
    let rk_digits = RNSGadgetVectorDigitIndices::select_digits(5, C.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_pow2(&params, &P, &C, 1, Some(6), 4, &gk_digits, Some("."));
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::SparseWithHwt(128));
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BFV::gen_gk(&C, &mut rng, &sk, &g, &gk_digits, 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &rk_digits, 3.2);
    let encaps = SparseKeyEncapsulationKey::new(bootstrapper.intermediate_plaintext_ring(), &C, &sk, 2, 32, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin(
        &C, 
        &C_mul, 
        ct, 
        &rk, 
        &gk,
        Some(&encaps),
        None
    );

    println!("final noise budget: {}", Pow2BFV::noise_budget(&P, &C, &res_ct, &sk));
    assert_el_eq!(P, P.int_hom().map(2), Pow2BFV::dec(&P, &C, res_ct, &sk));
}

#[test]
#[ignore]
fn measure_time_double_rns_pow2_bfv_thin_bootstrapping_t65537() {
    feanor_tracing::DelayedLogger::init_test();
    
    let mut rng = rand::rng();
    
    let params = Pow2BFV::new(1 << 16);
    let t = 65537;
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(805..820);
    let gk_digits = RNSGadgetVectorDigitIndices::select_digits(C.base_ring().len().div_ceil(2), C.base_ring().len());
    let rk_digits = RNSGadgetVectorDigitIndices::select_digits(5, C.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_pow2(&params, &P, &C, 1, Some(6), 4, &gk_digits, Some("."));
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::SparseWithHwt(128));
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BFV::gen_gk(&C, &mut rng, &sk, &g, &gk_digits, 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &rk_digits, 3.2);
    let encaps = SparseKeyEncapsulationKey::new(bootstrapper.intermediate_plaintext_ring(), &C, &sk, 2, 32, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);

    let res_ct = bootstrapper.bootstrap_thin(
        &C, 
        &C_mul, 
        ct, 
        &rk, 
        &gk,
        Some(&encaps),
        None
    );

    println!("final noise budget: {}", Pow2BFV::noise_budget(&P, &C, &res_ct, &sk));
    assert_el_eq!(P, P.int_hom().map(2), Pow2BFV::dec(&P, &C, res_ct, &sk));
}

#[test]
#[ignore]
fn measure_time_single_rns_composite_bfv_thin_bootstrapping() {
    feanor_tracing::DelayedLogger::init_test();
    // let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    // let filtered_chrome_layer = tracing_subscriber::Layer::with_filter(chrome_layer, tracing_subscriber::filter::filter_fn(|metadata| !["small_basis_to_mult_basis", "mult_basis_to_small_basis", "small_basis_to_coeff_basis", "coeff_basis_to_small_basis"].contains(&metadata.name())));
    // tracing_subscriber::util::SubscriberInitExt::init(tracing_subscriber::prelude::__tracing_subscriber_SubscriberExt::with(tracing_subscriber::registry(), filtered_chrome_layer));
    
    let mut rng = rand::rng();
    
    let params = CompositeSingleRNSBFV::new(37, 949);
    let t = 4;
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(805..820);
    let gk_digits = RNSGadgetVectorDigitIndices::select_digits(7, C.base_ring().len());
    let rk_digits = RNSGadgetVectorDigitIndices::select_digits(5, C.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_odd(&params, &P, &C, 6, None, 4, &gk_digits, Some("."));
    
    let sk = CompositeSingleRNSBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeSingleRNSBFV::gen_gk(&C, &mut rng, &sk, &g, &gk_digits, 3.2);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = CompositeSingleRNSBFV::gen_rk(&C, &mut rng, &sk, &rk_digits, 3.2);
    let encaps = SparseKeyEncapsulationKey::new(bootstrapper.intermediate_plaintext_ring(), &C, &sk, 2, 32, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = CompositeSingleRNSBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin(
        &C, 
        &C_mul, 
        ct, 
        &rk, 
        &gk,
        Some(&encaps),
        None
    );

    println!("final noise budget: {}", CompositeSingleRNSBFV::noise_budget(&P, &C, &res_ct, &sk));
    assert_el_eq!(P, P.int_hom().map(2), CompositeSingleRNSBFV::dec(&P, &C, res_ct, &sk));
}
