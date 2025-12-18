use std::cell::LazyCell;

use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::group::AbelianGroupStore;
use feanor_math::ring::*;
use feanor_math::assert_el_eq;
use feanor_math::serialization::SerializableElementRing;

use crate::bgv::modswitch::DefaultModswitchStrategy;
use crate::circuit::*;
use crate::filename_keys;
use crate::log_time;
use crate::digit_extract::DigitExtract;

use crate::lin_transform::composite;
use crate::number_ring::galois::*;
use crate::lin_transform::pow2;

use super::modswitch::*;
use super::*;

///
/// Precomputed public data that is required to bootstrap BGV ciphertexts
/// over a fixed plaintext and ciphertext ring.
/// 
pub struct ThinBootstrapper<Params, Strategy>
    where Params: BGVInstantiation, 
        Strategy: BGVModswitchStrategy<Params>,
        <CiphertextRing<Params> as RingStore>::Type: AsBGVPlaintext<Params>
{
    modswitch_strategy: Strategy,
    digit_extract: DigitExtract,
    slots_to_coeffs_thin: PlaintextCircuit<<CiphertextRing<Params> as RingStore>::Type>,
    coeffs_to_slots_thin: PlaintextCircuit<<CiphertextRing<Params> as RingStore>::Type>,
    plaintext_ring_hierarchy: Vec<PlaintextRing<Params>>,
    original_plaintext_ring: PlaintextRing<Params>,
    intermediate_plaintext_ring: PlaintextRing<Params>,
    tmp_coprime_modulus_plaintext: PlaintextRing<Params>,
    slots_to_coeffs_rns_factors: usize,
    master_ciphertext_ring: CiphertextRing<Params>
}

impl<Params, Strategy> ThinBootstrapper<Params, Strategy>
    where Params: BGVInstantiation, 
        Strategy: BGVModswitchStrategy<Params>,
        <CiphertextRing<Params> as RingStore>::Type: AsBGVPlaintext<Params>
{
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
    ///  - `slots_to_coeffs_rns_factors` is the number of RNS factors to use
    ///    when computing the Slots-to-Coeffs transform. More concretely,
    ///    since the result of the Slots-to-Coeffs transform does not have to have
    ///    any noise budget left, the input ciphertext can be mod-switched to a lower
    ///    modulus ciphertext ring before the Slots-to-Coeffs transform, which will
    ///    improve performance of the Slots-to-Coeffs transform. Since BGV uses hybrid
    ///    key-switching, this can be quite low, and just has to be large enough to
    ///    accomodate the noise growth caused by the Slots-to-Coeffs transform.
    /// 
    /// The parameters corresponding to the plaintext space (i.e. `t = p^r`) are
    /// implicitly given through the `digit_extract` parameter.
    /// 
    pub fn create(
        instantiation: &Params, 
        original_plaintext_ring: PlaintextRing<Params>,
        intermediate_plaintext_ring: PlaintextRing<Params>,
        C_master: CiphertextRing<Params>,
        slots_to_coeffs_thin: PlaintextCircuit<Params::PlaintextRing>, 
        coeffs_to_slots_thin: PlaintextCircuit<Params::PlaintextRing>,
        digit_extract: DigitExtract, 
        modswitch_strategy: Strategy,
        slots_to_coeffs_rns_factors: usize
    ) -> Self {
        let p = digit_extract.p();
        let r = digit_extract.r();
        let e = digit_extract.e();
        let plaintext_ring_hierarchy = ((r + 1)..e).map(|k| instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), k))).collect();
        let coeffs_to_slots_thin = coeffs_to_slots_thin.change_ring_uniform(|x| x.change_ring(|x| Params::encode_plain(&intermediate_plaintext_ring, &C_master, &x)));
        let slots_to_coeffs_thin = slots_to_coeffs_thin.change_ring_uniform(|x| x.change_ring(|x| Params::encode_plain(&original_plaintext_ring, &C_master, &x)));
        let tmp_coprime_modulus_plaintext = instantiation.create_plaintext_ring(ZZbig.add(ZZbig.pow(ZZbig.clone_el(&p), e), ZZbig.one())); 
        Self {
            digit_extract,
            coeffs_to_slots_thin,
            slots_to_coeffs_thin,
            plaintext_ring_hierarchy,
            slots_to_coeffs_rns_factors,
            modswitch_strategy,
            original_plaintext_ring,
            intermediate_plaintext_ring,
            tmp_coprime_modulus_plaintext,
            master_ciphertext_ring: C_master
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
    ///  - `gk_digits` specifies the gadget vector used for Galois keys. This is required to
    ///    estimate the number of RNS factors used for the Slots-to-Coeffs transform.
    ///  - `strategy` is the modulus-switching strategy to use when evaluating the digit
    ///    extraction circuits during bootstrapping.
    ///  - `cache_dir` specifies a directory to load and store precomputed data. If it is `None`,
    ///    no data will be read or written, but always computed from scratch.
    /// 
    pub fn build_pow2<const LOG: bool>(
        instantiation: &Params,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>, 
        v: usize,
        digit_extract_error_bound: Option<usize>,
        _gk_digits: &RNSGadgetVectorDigitIndices, 
        strategy: Strategy,
        cache_dir: Option<&str>
    ) -> Self
        where Params::PlaintextRing: SerializableElementRing,
            Params::CiphertextRing: Clone
    {
        let log2_m = ZZi64.abs_log2_ceil(&(instantiation.number_ring().galois_group().m() as i64)).unwrap();
        assert_eq!(instantiation.number_ring().galois_group().m(), 1 << log2_m);

        let t = int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZbig, P.base_ring().integer_ring());
        let (p, r) = is_prime_power(&ZZbig, &t).unwrap();
        let e = r + v;
        if LOG {
            println!("Setting up bootstrapping for plaintext modulus p^r = {}^{} = {} within the cyclotomic ring {:?}", ZZbig.format(&p), r, ZZbig.format(&t), instantiation.number_ring());
            println!("Using e = r + v = {} + {}", r, v);
        }

        let plaintext_ring = instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), e));
        // we don't use P here, but recreate the plaintext ring through modulus-switching, since we need the
        // structure of `plaintext_ring` and `original_plaintext_ring` to be compatible. Since we only take
        // encrypted plaintexts embedded into the ciphertext ring as input, this is fine.
        let original_plaintext_ring = instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r));

        let digit_extract = if let Some(B) = digit_extract_error_bound {
            assert_eq!(1, v, "if `digit_extract_error_bound` is set, `v` must be 1");
            DigitExtract::new_bounded_error(int_cast(ZZbig.clone_el(&p), ZZi64, ZZbig), e, B as i64)
        } else {
            DigitExtract::new_default(int_cast(ZZbig.clone_el(&p), ZZi64, ZZbig), e, r)
        };

        let H = LazyCell::new(|| {
            let hypercube = HypercubeStructure::default_pow2_hypercube(plaintext_ring.acting_galois_group(), ZZbig.clone_el(&p));
            HypercubeIsomorphism::new::<LOG>(&&plaintext_ring, &hypercube, cache_dir)
        });
        let original_H = LazyCell::new(|| H.change_modulus(&original_plaintext_ring));

        let m = plaintext_ring.number_ring().galois_group().m();
        let slots_to_coeffs = create_circuit_cached::<_, _, LOG>(&original_plaintext_ring, &filename_keys![slots2coeffs, m: m, p: &p, r: r], cache_dir, || pow2::slots_to_coeffs_thin(&original_H));
        let coeffs_to_slots = create_circuit_cached::<_, _, LOG>(&plaintext_ring, &filename_keys![coeffs2slots, m: m, p: &p, e: e], cache_dir, || pow2::coeffs_to_slots_thin(&H));
        
        // we estimate the noise growth of the slots-to-coeffs transform as `log2_m` multiplications by
        // ring elements of size at most `t`
        let min_rns_factor_log2 = C_master.base_ring().as_iter().map(|rns_factor| *rns_factor.modulus() as i64).map(|rns_factor| (rns_factor as f64).log2()).min_by(f64::total_cmp).unwrap();
        let slots_to_coeffs_rns_factors = ((ZZbig.abs_log2_ceil(&t).unwrap() as f64 + P.number_ring().coeff_basis_product_expansion_factor().log2()) * (P.acting_galois_group().group_order() as f64).log2() / min_rns_factor_log2).ceil() as usize; 

        return Self::create(instantiation, original_plaintext_ring, plaintext_ring, C_master.clone(), slots_to_coeffs, coeffs_to_slots, digit_extract, strategy, slots_to_coeffs_rns_factors);
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
    ///  - `gk_digits` specifies the gadget vector used for Galois keys. This is required to
    ///    estimate the number of RNS factors used for the Slots-to-Coeffs transform.
    ///  - `strategy` is the modulus-switching strategy to use when evaluating the digit
    ///    extraction circuits during bootstrapping.
    ///  - `cache_dir` specifies a directory to load and store precomputed data. If it is `None`,
    ///    no data will be read or written, but always computed from scratch.
    /// 
    pub fn build_odd<const LOG: bool>(
        instantiation: &Params,
        P: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>, 
        v: usize,
        digit_extract_error_bound: Option<usize>,
        _gk_digits: &RNSGadgetVectorDigitIndices,
        strategy: Strategy, 
        cache_dir: Option<&str>
    ) -> Self
        where Params::PlaintextRing: SerializableElementRing,
            Params::CiphertextRing: Clone
    {
        assert!(instantiation.number_ring().galois_group().m() % 2 != 0);

        let t = int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZbig, P.base_ring().integer_ring());
        let (p, r) = is_prime_power(&ZZbig, &t).unwrap();
        let e = r + v;
        if LOG {
            println!("Setting up bootstrapping for plaintext modulus p^r = {}^{} = {} within the cyclotomic ring {:?}", ZZbig.format(&p), r, ZZbig.format(&t), instantiation.number_ring());
            println!("Using e = r + v = {} + {}", r, v);
        }

        let plaintext_ring = instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), e));
        let original_plaintext_ring = instantiation.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r));

        let p_i64 = int_cast(ZZbig.clone_el(&p), ZZi64, ZZbig);
        let digit_extract = if p_i64 == 2 && e <= 23 && digit_extract_error_bound.is_none() {
            DigitExtract::new_precomputed_p_is_2(p_i64, e, r)
        } else if let Some(B) = digit_extract_error_bound {
            assert_eq!(1, v, "if `digit_extract_error_bound` is set, `v` must be 1");
            DigitExtract::new_bounded_error(int_cast(ZZbig.clone_el(&p), ZZi64, ZZbig), e, B as i64)
        } else {
            DigitExtract::new_default(p_i64, e, r)
        };

        let hypercube = HypercubeStructure::halevi_shoup_hypercube(plaintext_ring.acting_galois_group(), ZZbig.clone_el(&p));
        let H = LazyCell::new(|| HypercubeIsomorphism::new::<LOG>(&&plaintext_ring, &hypercube, cache_dir));
        let original_H = LazyCell::new(|| H.change_modulus(&original_plaintext_ring));

        let m = plaintext_ring.number_ring().galois_group().m();
        let slots_to_coeffs =  create_circuit_cached::<_, _, LOG>(&original_plaintext_ring, &filename_keys![slots2coeffs, m: m, p: &p, r: r], cache_dir, || composite::slots_to_powcoeffs_thin(&original_H));
        let coeffs_to_slots = create_circuit_cached::<_, _, LOG>(&plaintext_ring, &filename_keys![coeffs2slots, m: m, p: &p, e: e], cache_dir, || composite::powcoeffs_to_slots_thin(&H));
        
        // we estimate the noise growth of the slots-to-coeffs transform as `log2_m` multiplications by
        // ring elements of size at most `t`
        let min_rns_factor_log2 = C_master.base_ring().as_iter().map(|rns_factor| *rns_factor.modulus() as i64).map(|rns_factor| (rns_factor as f64).log2()).min_by(f64::total_cmp).unwrap();
        let slots_to_coeffs_rns_factors = ((ZZbig.abs_log2_ceil(&t).unwrap() as f64 + P.number_ring().coeff_basis_product_expansion_factor().log2()) * (hypercube.dim_count() as f64 + 1.0) / min_rns_factor_log2).ceil() as usize;
        
        return Self::create(instantiation, original_plaintext_ring, plaintext_ring, C_master.clone(), slots_to_coeffs, coeffs_to_slots, digit_extract, strategy, slots_to_coeffs_rns_factors);
    }

    ///
    /// Replaces the digit extraction object used by this bootstrapper.
    /// 
    pub fn with_digit_extraction(self, new_digit_extraction: DigitExtract) -> Self {
        assert_el_eq!(ZZbig, self.digit_extract.p(), new_digit_extraction.p());
        assert_eq!(self.digit_extract.r(), new_digit_extraction.r());
        assert_eq!(self.digit_extract.e(), new_digit_extraction.e());
        Self {
            coeffs_to_slots_thin: self.coeffs_to_slots_thin,
            digit_extract: new_digit_extraction,
            intermediate_plaintext_ring: self.intermediate_plaintext_ring,
            plaintext_ring_hierarchy: self.plaintext_ring_hierarchy,
            master_ciphertext_ring: self.master_ciphertext_ring,
            modswitch_strategy: self.modswitch_strategy,
            original_plaintext_ring: self.original_plaintext_ring,
            slots_to_coeffs_rns_factors: self.slots_to_coeffs_rns_factors,
            tmp_coprime_modulus_plaintext: self.tmp_coprime_modulus_plaintext,
            slots_to_coeffs_thin: self.slots_to_coeffs_thin
        }
    }

    fn r(&self) -> usize {
        self.digit_extract.e() - self.digit_extract.v()
    }

    fn e(&self) -> usize {
        self.digit_extract.e()
    }

    fn v(&self) -> usize {
        self.digit_extract.v()
    }

    fn p(&self) -> &El<BigIntRing> {
        self.digit_extract.p()
    }

    pub fn intermediate_plaintext_ring(&self) -> &PlaintextRing<Params> {
        &self.intermediate_plaintext_ring
    }

    pub fn base_plaintext_ring(&self) -> &PlaintextRing<Params> {
        &self.original_plaintext_ring
    }

    pub fn required_galois_keys(&self, P: &PlaintextRing<Params>) -> Vec<GaloisGroupEl> {
        let mut result = Vec::new();
        result.extend(self.slots_to_coeffs_thin.required_galois_keys(&P.acting_galois_group()).into_iter());
        result.extend(self.coeffs_to_slots_thin.required_galois_keys(&P.acting_galois_group()).into_iter());
        result.sort_by_key(|g| P.acting_galois_group().representative(g));
        result.dedup_by(|g, s| P.acting_galois_group().eq_el(g, s));
        return result;
    }

    ///
    /// Performs bootstrapping on thinly packed ciphertexts.
    /// 
    /// Parameters are as follows:
    ///  - `C_master` is the ciphertext ring over the largest RNS base, both relinearization and
    ///    Galois keys must be defined w.r.t. `C_master`
    ///  - `P_base` is the current plaintext ring; `ct` must be a valid BGV ciphertext encrypting
    ///    a message from `P_base`
    ///  - `ct_dropped_moduli` contains all RNS factor indices of `C_master` that aren't used by `ct`
    ///    (anymore); More concrete, `ct` lives over the ciphertext ring one obtains by dropping the
    ///    RNS factors with these indices from the RNS base of `C_master`
    ///  - `ct` is the ciphertext to bootstrap; It must be thinly packed (i.e. each slot may only
    ///    contain an element of `Z/(t)`), otherwise this function will cause immediate noise overflow.
    ///  - `rk` is a relinearization key, to be used for computing products
    ///  - `gks` is a list of Galois keys, to be used for applying Galois automorphisms. This list
    ///    must contain a Galois key for each Galois automorphism listed in [`ThinBootstrapper::required_galois_keys()`],
    ///    but may contain additional Galois keys
    ///  - `debug_sk` can be a reference to a secret key, which is used to print out decryptions
    ///    of intermediate results for debugging purposes. May only be set if `LOG == true`.
    /// 
    #[instrument(skip_all)]
    pub fn bootstrap_thin<'a, const LOG: bool>(
        &self,
        C_master: &CiphertextRing<Params>, 
        P_base: &PlaintextRing<Params>,
        ct_dropped_moduli: &RNSFactorIndexList,
        ct: Ciphertext<Params>,
        rk: &RelinKey<Params>,
        gks: &[(GaloisGroupEl, KeySwitchKey<Params>)],
        used_sk: SecretKeyDistribution,
        sk_encaps_data: Option<&SparseKeyEncapsulationKey<Params>>,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Strategy>
        where Params: 'a
    {
        assert!(LOG || debug_sk.is_none());
        assert!(ZZbig.eq_el(&ZZbig.pow(ZZbig.clone_el(self.p()), self.r()), &int_cast(P_base.base_ring().integer_ring().clone_el(P_base.base_ring().modulus()), ZZbig, P_base.base_ring().integer_ring())));
        assert!(self.base_plaintext_ring().get_ring() == P_base.get_ring());
        assert!(self.master_ciphertext_ring.get_ring() == C_master.get_ring());
        
        log_time::<_, _, LOG, _>("Performing thin bootstrapping", |[]| {

            // First, we mod-switch the input ciphertext so that it only has `self.slots_to_coeffs_rns_factors` many RNS factors
            let input_dropped_rns_factors = {
                assert!(C_master.base_ring().len() - ct_dropped_moduli.len() >= self.slots_to_coeffs_rns_factors);
                let gk_digits = gks[0].1.gadget_vector_digits();
                let (drop_additional, _) = compute_optimal_special_modulus(
                    C_master.get_ring(),
                    ct_dropped_moduli,
                    C_master.base_ring().len() - ct_dropped_moduli.len() - self.slots_to_coeffs_rns_factors,
                    gk_digits
                );
                drop_additional.union(&ct_dropped_moduli)
            };
            let C_input = Params::mod_switch_down_C(C_master, &input_dropped_rns_factors);
            let ct_input = Params::mod_switch_ct(P_base, &C_input, &Params::mod_switch_down_C(C_master, ct_dropped_moduli), ct);
            assert_eq!(C_input.base_ring().len(), self.slots_to_coeffs_rns_factors);

            let sk_input = debug_sk.map(|sk| Params::mod_switch_sk(&C_input, &C_master, sk));
            if let Some(sk) = &sk_input {
                Params::dec_println_slots(P_base, &C_input, &ct_input, sk, Some("."));
            }

            let values_in_coefficients = log_time::<_, _, LOG, _>("1. Computing Slots-to-Coeffs transform", |[key_switches]| {
                let result = DefaultModswitchStrategy::never_modswitch().evaluate_circuit(
                    &self.slots_to_coeffs_thin, 
                    C_master,
                    P_base, 
                    C_master, 
                    &[ModulusAwareCiphertext {
                        data: ct_input, 
                        info: (), 
                        dropped_rns_factor_indices: input_dropped_rns_factors.clone(),
                        sk: used_sk
                    }], 
                    None, 
                    gks,
                    key_switches,
                    debug_sk
                );
                assert_eq!(1, result.len());
                let result = result.into_iter().next().unwrap();
                debug_assert_eq!(result.dropped_rns_factor_indices, input_dropped_rns_factors);
                return result.data;
            });
            if let Some(sk) = &sk_input {
                Params::dec_println(P_base, &C_input, &values_in_coefficients, sk);
            }

            let P_main = &self.intermediate_plaintext_ring;
            assert!(ZZbig.eq_el(&ZZbig.pow(ZZbig.clone_el(self.p()), self.e()), &int_cast(P_main.base_ring().integer_ring().clone_el(P_main.base_ring().modulus()), ZZbig, P_main.base_ring().integer_ring())));

            // this is slightly more complicated than in BFV, since we cannot mod-switch to a ciphertext modulus that is not coprime to `t = p^r`.
            // Instead, we first multiply by `p^v`, then mod-switch to `p^e + 1`, and then reduce the shortest lift of the result modulo `p^e`.
            // This will introduce the overflow modulo `p^e + 1` as error in the lower bits, which we will later remove during digit extraction
            let perform_noisy_expansion = |C: &CiphertextRing<Params>, ct: Ciphertext<Params>, enc_sk: Ciphertext<Params>| {
                let ZZbig_to_C = C.inclusion().compose(C.base_ring().can_hom(&ZZbig).unwrap());
                let values_scaled = Ciphertext {
                    c0: ZZbig_to_C.mul_map(ct.c0, ZZbig.pow(ZZbig.clone_el(self.p()), self.v())),
                    c1: ZZbig_to_C.mul_map(ct.c1, ZZbig.pow(ZZbig.clone_el(self.p()), self.v())),
                    implicit_scale: ct.implicit_scale
                };
                // change to `p^e + 1`
                let (c0, c1) = Params::mod_switch_to_plaintext(P_main, &self.tmp_coprime_modulus_plaintext, &C, values_scaled);
                // reduce modulo `p^e`, which will introduce additional error in the lower digits
                let mod_pe = P_main.base_ring().can_hom(self.tmp_coprime_modulus_plaintext.base_ring().integer_ring()).unwrap();
                let (c0, c1) = (
                    P_main.from_canonical_basis(self.tmp_coprime_modulus_plaintext.wrt_canonical_basis(&c0).iter().map(|x| mod_pe.map(self.tmp_coprime_modulus_plaintext.base_ring().smallest_lift(x)))),
                    P_main.from_canonical_basis(self.tmp_coprime_modulus_plaintext.wrt_canonical_basis(&c1).iter().map(|x| mod_pe.map(self.tmp_coprime_modulus_plaintext.base_ring().smallest_lift(x))))
                );
                return ModulusAwareCiphertext {
                    data: Params::hom_add_plain(P_main, C_master, &c0, Params::hom_mul_plain(P_main, C_master, &c1, enc_sk)),
                    info: self.modswitch_strategy.info_for_fresh_encryption(P_main, C_master, used_sk),
                    dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                    sk: used_sk
                };
            };
            let noisy_decryption = if let Some(sparse_sk_encaps) = sk_encaps_data {
                let ct_keyswitched = log_time::<_, _, LOG, _>("2.1 Switching to sparse key", |[]| {
                    let ct_modswitched = Params::mod_switch_ct(P_base, &sparse_sk_encaps.C_sparse_sk, &C_input, values_in_coefficients);
                    Params::key_switch(P_base, &sparse_sk_encaps.C_sparse_sk, &sparse_sk_encaps.C_sparse_sk, ct_modswitched, &sparse_sk_encaps.switch_to_sparse_key)
                });
                log_time::<_, _, LOG, _>("2.2 Computing noisy decryption c0 + c1 * s", |[]| {
                    perform_noisy_expansion(&sparse_sk_encaps.C_sparse_sk, ct_keyswitched, Params::clone_ct(P_main, C_master, &sparse_sk_encaps.encapsulated_key))
                })
            } else {
                log_time::<_, _, LOG, _>("2. Computing noisy decryption c0 + c1 * s", |[]| {
                    perform_noisy_expansion(&C_input, values_in_coefficients, Params::enc_sk(P_main, C_master))
                })
            };
            if let Some(sk) = debug_sk {
                Params::dec_println(P_main, &C_master, &noisy_decryption.data, sk);
            }

            let noisy_decryption_in_slots = log_time::<_, _, LOG, _>("3. Computing Coeffs-to-Slots transform", |[key_switches]| {
                let result = self.modswitch_strategy.evaluate_circuit(
                    &self.coeffs_to_slots_thin, 
                    C_master,
                    P_main, 
                    C_master, 
                    &[noisy_decryption], 
                    None, 
                    gks,
                    key_switches,
                    debug_sk
                );
                assert_eq!(1, result.len());
                return result.into_iter().next().unwrap();
            });
            if let Some(sk) = debug_sk {
                let C_current = Params::mod_switch_down_C(C_master, &noisy_decryption_in_slots.dropped_rns_factor_indices);
                Params::dec_println_slots(P_main, &C_current, &noisy_decryption_in_slots.data, &Params::mod_switch_sk(&C_current, C_master, sk), Some("."));
            }

            let final_result = log_time::<_, _, LOG, _>("4. Computing digit extraction", |[key_switches]| {

                let C_current = Params::mod_switch_down_C(C_master, &noisy_decryption_in_slots.dropped_rns_factor_indices);
                let rounding_divisor_half = C_current.base_ring().coerce(&ZZbig, ZZbig.rounded_div(ZZbig.pow(ZZbig.clone_el(self.p()), self.v()), &ZZbig.int_hom().map(2)));
                let digit_extraction_input = ModulusAwareCiphertext {
                    data: Params::hom_add_plain_encoded(P_main, &C_current, &C_current.inclusion().map(rounding_divisor_half), noisy_decryption_in_slots.data),
                    info: noisy_decryption_in_slots.info,
                    dropped_rns_factor_indices: noisy_decryption_in_slots.dropped_rns_factor_indices,
                    sk: noisy_decryption_in_slots.sk
                };
        
                if let Some(sk) = debug_sk {
                    self.modswitch_strategy.print_info(P_main, &C_current, &digit_extraction_input);
                    Params::dec_println_slots(P_main, &C_current, &digit_extraction_input.data, &Params::mod_switch_sk(&C_current, C_master, sk), Some("."));
                }

                return self.digit_extract.evaluate_bgv::<Params, Strategy, LOG>(
                    &self.modswitch_strategy,
                    P_base,
                    &self.plaintext_ring_hierarchy,
                    P_main,
                    C_master,
                    digit_extraction_input,
                    rk,
                    key_switches,
                    debug_sk
                ).0;
            });
            return final_result;
        })
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
pub struct SparseKeyEncapsulationKey<Params: BGVInstantiation> {
    ///
    /// Ciphertext ring with small modulus, over which encryptions with the
    /// sparse key remain secure.
    /// 
    pub C_sparse_sk: CiphertextRing<Params>,
    ///
    /// Key-switch key to switch a ciphertext encrypted by the standard key
    /// to a ciphertext encrypted by the sparse key.
    /// 
    /// This is defined w.r.t. the switch-to-sparse ciphertext ring, which has
    /// a significantly smaller modulus than the standard ciphertext ring. This
    /// is necessary for security.
    /// 
    pub switch_to_sparse_key: KeySwitchKey<Params>,
    ///
    /// An encryption of the sparse secret key (mapped into the plaintext ring
    /// by taking a shortest lift to `R`) w.r.t. the standard secret key.
    /// 
    pub encapsulated_key: Ciphertext<Params>
}

impl<Params> SparseKeyEncapsulationKey<Params>
    where Params: BGVInstantiation, 
        Params::PlaintextRing: AsBGVPlaintext<Params>
{
    pub fn create<R: CryptoRng + Rng>(P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_sparse_sk: CiphertextRing<Params>, sparse_sk: SecretKey<Params>, standard_sk: &SecretKey<Params>, mut rng: R, noise_sigma: f64) -> Self {
        let switch_to_sparse_key = Params::gen_switch_key(
            P,
            &C_sparse_sk, 
            &mut rng,
            &Params::mod_switch_sk(&C_sparse_sk, C, standard_sk),
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

impl DigitExtract {

    pub fn evaluate_bgv<Params: BGVInstantiation, Strategy: BGVModswitchStrategy<Params>, const LOG: bool>(
        &self,
        modswitch_strategy: &Strategy, 
        P_base: &PlaintextRing<Params>, 
        P_intermediate: &[PlaintextRing<Params>], 
        P_main: &PlaintextRing<Params>,
        C_master: &CiphertextRing<Params>, 
        input: ModulusAwareCiphertext<Params, Strategy>, 
        rk: &RelinKey<Params>,
        key_switches: &mut usize,
        debug_sk: Option<&SecretKey<Params>>
    ) -> (ModulusAwareCiphertext<Params, Strategy>, ModulusAwareCiphertext<Params, Strategy>) {
        assert!(LOG || debug_sk.is_none());

        let (p, _) = is_prime_power(ZZbig, &int_cast(P_base.base_ring().integer_ring().clone_el(P_base.base_ring().modulus()), ZZbig, P_base.base_ring().integer_ring())).unwrap();
        assert_el_eq!(ZZbig, self.p(), &p);
        assert_el_eq!(ZZbig, ZZbig.pow(ZZbig.clone_el(self.p()), self.r()), int_cast(P_base.base_ring().integer_ring().clone_el(P_base.base_ring().modulus()), ZZbig, P_base.base_ring().integer_ring()));
        assert_el_eq!(ZZbig, ZZbig.pow(ZZbig.clone_el(self.p()), self.e()), int_cast(P_main.base_ring().integer_ring().clone_el(P_main.base_ring().modulus()), ZZbig, P_main.base_ring().integer_ring()));
        for i in (self.r() + 1)..self.e() {
            let P_current = &P_intermediate[i - self.r() - 1];
            assert!(P_base.base_ring().integer_ring().get_ring() == P_current.base_ring().integer_ring().get_ring());
            assert_el_eq!(ZZbig, ZZbig.pow(ZZbig.clone_el(self.p()), i), int_cast(P_current.base_ring().integer_ring().clone_el(P_current.base_ring().modulus()), ZZbig, P_current.base_ring().integer_ring()));
        }
        let get_P = |exp: usize| if exp == self.r() {
            P_base
        } else if exp == self.e() {
            P_main
        } else {
            &P_intermediate[exp - self.r() - 1]
        };
        return self.evaluate_generic(
            input,
            |exp, inputs, circuit| {
                let digit_extracted = modswitch_strategy.evaluate_circuit(circuit, ZZi64, get_P(exp), C_master, inputs, Some(rk), &[], key_switches, debug_sk);
                if LOG && /* don't log if the circuit is just adding/cloning elements */ circuit.has_multiplication_gates() {
                    println!("Digit extraction modulo p^{} done", exp);
                    if let Some(sk) = debug_sk {
                        for ct in &digit_extracted {
                            modswitch_strategy.print_info(get_P(exp), C_master, ct);
                            let Clocal = Params::mod_switch_down_C(C_master, &ct.dropped_rns_factor_indices);
                            let sk_local = Params::mod_switch_sk(&Clocal, C_master, sk);
                            Params::dec_println_slots(get_P(exp), &Clocal, &ct.data, &sk_local, Some("."));
                            println!();
                        }
                    }
                }
                return digit_extracted;
            },
            |exp_old, exp_new, input| {
                let C_current = Params::mod_switch_down_C(C_master, &input.dropped_rns_factor_indices);
                let result = ModulusAwareCiphertext {
                    data: Params::change_plaintext_modulus(get_P(exp_new), get_P(exp_old), &C_current, input.data),
                    dropped_rns_factor_indices: input.dropped_rns_factor_indices.clone(),
                    info: input.info,
                    sk: input.sk
                };
                return result;
            }
        );
    }
}

#[cfg(test)]
use crate::bgv::noise_estimator::NaiveBGVNoiseEstimator;

#[test]
fn test_pow2_bgv_thin_bootstrapping_17() {
    let mut rng = StdRng::from_seed([0; 32]);
    
    // 8 slots of rank 16
    let params = Pow2BGV::new(1 << 7);
    let t = int_cast(17, ZZbig, ZZi64);
    let P = params.create_plaintext_ring(t);
    let C_master = params.create_ciphertext_ring(790..800);
    let key_switch_params = RNSGadgetVectorDigitIndices::select_digits(5, C_master.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_pow2::<true>(&params, &P, &C_master, 2, None, &key_switch_params, DefaultModswitchStrategy::<_, _, true>::new(NaiveBGVNoiseEstimator), None);
    
    let sk = Pow2BGV::gen_sk(&C_master, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BGV::gen_gk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &g, &key_switch_params, 3.2);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = Pow2BGV::gen_rk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &key_switch_params, 3.2);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BGV::enc_sym(&P, &C_master, &mut rng, &m, &sk, 3.2);
    let ct_result = bootstrapper.bootstrap_thin::<true>(
        &C_master, 
        &P, 
        &RNSFactorIndexList::empty(),
        ct, 
        &rk, 
        &gk,
        SecretKeyDistribution::UniformTernary,
        None,
        Some(&sk)
    );
    let C_result = Pow2BGV::mod_switch_down_C(&C_master, &ct_result.dropped_rns_factor_indices);
    let sk_result = Pow2BGV::mod_switch_sk(&C_result, &C_master, &sk);

    assert_el_eq!(P, P.int_hom().map(2), Pow2BGV::dec(&P, &C_result, ct_result.data, &sk_result));
}

#[test]
fn test_composite_bgv_thin_bootstrapping_2_sparse_key_encapsulation() {
    let mut rng = StdRng::from_seed([0; 32]);
    
    // 8 slots of rank 16
    let params = CompositeBGV::new(31, 11);
    let t = int_cast(8, ZZbig, ZZi64);
    let P = params.create_plaintext_ring(t);
    let C_master = params.create_ciphertext_ring(790..800);
    let key_switch_params = RNSGadgetVectorDigitIndices::select_digits(5, C_master.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_odd::<true>(&params, &P, &C_master, 4, None, &key_switch_params, DefaultModswitchStrategy::<_, _, true>::new(NaiveBGVNoiseEstimator), None);
    
    let sk = CompositeBGV::gen_sk(&C_master, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeBGV::gen_gk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &g, &key_switch_params, 3.2);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = CompositeBGV::gen_rk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &key_switch_params, 3.2);
    let encaps = SparseKeyEncapsulationKey::new(bootstrapper.intermediate_plaintext_ring(), &C_master, &sk, 2, 16, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = CompositeBGV::enc_sym(&P, &C_master, &mut rng, &m, &sk, 3.2);
    let ct_result = bootstrapper.bootstrap_thin::<true>(
        &C_master, 
        &P, 
        &RNSFactorIndexList::empty(),
        ct, 
        &rk, 
        &gk,
        SecretKeyDistribution::UniformTernary,
        Some(&encaps),
        Some(&sk)
    );
    let C_result = CompositeBGV::mod_switch_down_C(&C_master, &ct_result.dropped_rns_factor_indices);
    let sk_result = CompositeBGV::mod_switch_sk(&C_result, &C_master, &sk);

    assert_el_eq!(P, P.int_hom().map(2), CompositeBGV::dec(&P, &C_result, ct_result.data, &sk_result));
}

#[ignore]
#[test]
fn measure_time_double_rns_composite_bgv_thin_bootstrapping() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    let filtered_chrome_layer = chrome_layer.with_filter(tracing_subscriber::filter::filter_fn(|metadata| !["small_basis_to_mult_basis", "mult_basis_to_small_basis", "small_basis_to_coeff_basis", "coeff_basis_to_small_basis"].contains(&metadata.name())));
    tracing_subscriber::registry().with(filtered_chrome_layer).init();
    
    let mut rng = StdRng::from_seed([0; 32]);

    let t = int_cast(4, ZZbig, ZZi64);
    let sk_distr = SecretKeyDistribution::SparseWithHwt(256);
    let params = CompositeBGV::new(37, 949);
    let P = params.create_plaintext_ring(t);
    let C_master = params.create_ciphertext_ring(805..820);
    assert_eq!(15, C_master.base_ring().len());
    let key_switch_params = RNSGadgetVectorDigitIndices::select_digits(7, C_master.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_odd::<true>(&params, &P, &C_master, 7, None, &key_switch_params, DefaultModswitchStrategy::<_, _, false>::new(NaiveBGVNoiseEstimator), Some("."));
    
    let sk = CompositeBGV::gen_sk(&C_master, &mut rng, sk_distr);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeBGV::gen_gk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &g, &key_switch_params, 3.2);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = CompositeBGV::gen_rk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &key_switch_params, 3.2);
    
    let m = P.int_hom().map(2);
    let ct = CompositeBGV::enc_sym(&P, &C_master, &mut rng, &m, &sk, 3.2);
    let ct_result = bootstrapper.bootstrap_thin::<true>(
        &C_master, 
        &P, 
        &RNSFactorIndexList::empty(),
        ct, 
        &rk, 
        &gk,
        sk_distr,
        None,
        None
    );
    let C_result = CompositeBGV::mod_switch_down_C(&C_master, &ct_result.dropped_rns_factor_indices);
    let sk_result = CompositeBGV::mod_switch_sk(&C_result, &C_master, &sk);
    println!("final noise budget: {}", CompositeBGV::noise_budget(&P, &C_result, &ct_result.data, &sk_result));
    let result = CompositeBGV::dec(&P, &C_result, ct_result.data, &sk_result);
    assert_el_eq!(P, P.int_hom().map(2), result);
}

#[ignore]
#[test]
fn measure_time_double_rns_pow2_bgv_thin_bootstrapping() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    let filtered_chrome_layer = chrome_layer.with_filter(tracing_subscriber::filter::filter_fn(|metadata| !["small_basis_to_mult_basis", "mult_basis_to_small_basis", "small_basis_to_coeff_basis", "coeff_basis_to_small_basis"].contains(&metadata.name())));
    tracing_subscriber::registry().with(filtered_chrome_layer).init();
    
    let mut rng = StdRng::from_seed([0; 32]);

    let t = int_cast(17, ZZbig, ZZi64);
    let sk_distr = SecretKeyDistribution::SparseWithHwt(256);
    let params = Pow2BGV::new(1 << 16);
    let P = params.create_plaintext_ring(t);
    let C_master = params.create_ciphertext_ring(805..820);
    assert_eq!(15, C_master.base_ring().len());
    let gk_params = RNSGadgetVectorDigitIndices::select_digits(7, C_master.base_ring().len());
    let rk_params = RNSGadgetVectorDigitIndices::select_digits(3, C_master.base_ring().len());
    let bootstrapper = ThinBootstrapper::build_pow2::<true>(&params, &P, &C_master, 2, None, &gk_params, DefaultModswitchStrategy::<_, _, false>::new(NaiveBGVNoiseEstimator), Some("."));
    
    let sk = Pow2BGV::gen_sk(&C_master, &mut rng, sk_distr);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BGV::gen_gk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &g, &gk_params, 3.2);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = Pow2BGV::gen_rk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &rk_params, 3.2);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BGV::enc_sym(&P, &C_master, &mut rng, &m, &sk, 3.2);
    let ct_result = bootstrapper.bootstrap_thin::<true>(
        &C_master, 
        &P, 
        &RNSFactorIndexList::empty(),
        ct, 
        &rk, 
        &gk,
        sk_distr,
        None,
        Some(&sk)
    );
    let C_result = Pow2BGV::mod_switch_down_C(&C_master, &ct_result.dropped_rns_factor_indices);
    let sk_result = Pow2BGV::mod_switch_sk(&C_result, &C_master, &sk);
    println!("final noise budget: {}", Pow2BGV::noise_budget(&P, &C_result, &ct_result.data, &sk_result));
    let result = Pow2BGV::dec(&P, &C_result, ct_result.data, &sk_result);
    assert_el_eq!(P, P.int_hom().map(2), result);
}
