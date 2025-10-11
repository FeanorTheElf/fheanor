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

#[derive(Clone, Debug)]
pub struct ThinBootstrapParams<Params: BGVInstantiation> {
    /// Parameters of the scheme to be bootstrapped.
    pub scheme_params: Params,
    /// The additional exponent of the intermediate bootstrapping plaintext modulus.
    /// 
    /// When bootstrapping, we convert the input ciphertext into a ciphertext modulo
    /// `p^(r + v)`, where the original plaintext modulus is `p^r`. This fits into a
    /// plaintext with plaintext modulus `p^(r + v)`, so we can homomorphically evaluate
    /// the decryption here. For this to work, we require that modulus-switching to
    /// `p^(r + v)` does not cause noise overflow, hence `v` must scale with the `l_1`-norm
    /// of the secret key.
    pub v: usize,
    /// The plaintext modulus w.r.t. which the bootstrapped input is defined. 
    /// Must be a power of a prime 
    pub t: El<BigIntRing>,
    /// The first step of thin bootstrapping is the Slots-to-Coeffs transform, which
    /// is still applied to the original ciphertext. Since the ciphertext is homomorphically
    /// decrypted directly afterwards, we don't need much precision at this point anymore.
    /// Hence, we modulus-switch it to a modulus with this many RNS factors, to save
    /// time during the Slots-to-Coeffs transform.
    pub pre_bootstrap_rns_factors: usize
}

impl<Params> ThinBootstrapParams<Params>
    where Params: BGVInstantiation, 
        <CiphertextRing<Params> as RingStore>::Type: AsBGVPlaintext<Params>,
        Params::PlaintextRing: SerializableElementRing
{
    pub fn build_pow2<M: BGVModswitchStrategy<Params>, const LOG: bool>(&self, C: &CiphertextRing<Params>, modswitch_strategy: M, cache_dir: Option<&str>) -> ThinBootstrapData<Params, M> {
        let log2_m = ZZi64.abs_log2_ceil(&(self.scheme_params.number_ring().galois_group().m() as i64)).unwrap();
        assert_eq!(self.scheme_params.number_ring().galois_group().m(), 1 << log2_m);

        let (p, r) = is_prime_power(ZZbig, &self.t).unwrap();
        let v = self.v;
        let e = r + v;
        if LOG {
            println!("Setting up bootstrapping for plaintext modulus p^r = {}^{} = {} within the cyclotomic ring Q[X]/(Phi_{})", ZZbig.format(&p), r, ZZbig.format(&self.t), self.scheme_params.number_ring().galois_group().m());
            println!("Using e = r + v = {} + {}", r, v);
        }

        let plaintext_ring = self.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), e));
        let original_plaintext_ring = self.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r));

        let digit_extract = DigitExtract::new_default(int_cast(ZZbig.clone_el(&p), ZZi64, ZZbig), e, r);

        let H = LazyCell::new(|| {
            let hypercube = HypercubeStructure::default_pow2_hypercube(plaintext_ring.acting_galois_group(), ZZbig.clone_el(&p));
            HypercubeIsomorphism::new::<LOG>(&&plaintext_ring, &hypercube, cache_dir)
        });
        let original_H = LazyCell::new(|| H.change_modulus(&original_plaintext_ring));

        let m = plaintext_ring.number_ring().galois_group().m();
        let slots_to_coeffs = create_circuit_cached::<_, _, LOG>(&original_plaintext_ring, &filename_keys![slots2coeffs, m: m, p: &p, r: r], cache_dir, || pow2::slots_to_coeffs_thin(&original_H));
        let coeffs_to_slots = create_circuit_cached::<_, _, LOG>(&plaintext_ring, &filename_keys![coeffs2slots, m: m, p: &p, e: e], cache_dir, || pow2::coeffs_to_slots_thin(&H));
        
        return ThinBootstrapData::new_with_digit_extract_and_lin_transform(self, C, digit_extract, slots_to_coeffs, coeffs_to_slots, modswitch_strategy);
    }

    pub fn build_odd<M: BGVModswitchStrategy<Params>, const LOG: bool>(&self, C: &CiphertextRing<Params>, modswitch_strategy: M, cache_dir: Option<&str>) -> ThinBootstrapData<Params, M> {
        assert!(self.scheme_params.number_ring().galois_group().m() % 2 != 0);

        let (p, r) = is_prime_power(ZZbig, &self.t).unwrap();
        let v = self.v;
        let e = r + v;
        if LOG {
            println!("Setting up bootstrapping for plaintext modulus p^r = {}^{} = {} within the cyclotomic ring Q[X]/(Phi_{})", ZZbig.format(&p), r, ZZbig.format(&self.t), self.scheme_params.number_ring().galois_group().m());
            println!("Using e = r + v = {} + {}", r, v);
        }

        let plaintext_ring = self.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), e));
        let original_plaintext_ring = self.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r));

        let p_i64 = int_cast(ZZbig.clone_el(&p), ZZi64, ZZbig);
        let digit_extract = if p_i64 == 2 && e <= 23 {
            DigitExtract::new_precomputed_p_is_2(p_i64, e, r)
        } else {
            DigitExtract::new_default(p_i64, e, r)
        };

        let H = LazyCell::new(|| {
            let hypercube = HypercubeStructure::halevi_shoup_hypercube(plaintext_ring.acting_galois_group(), ZZbig.clone_el(&p));
            HypercubeIsomorphism::new::<LOG>(&&plaintext_ring, &hypercube, cache_dir)
        });
        let original_H = LazyCell::new(|| H.change_modulus(&original_plaintext_ring));

        let m = plaintext_ring.number_ring().galois_group().m();
        let slots_to_coeffs =  create_circuit_cached::<_, _, LOG>(&original_plaintext_ring, &filename_keys![slots2coeffs, m: m, p: &p, r: r], cache_dir, || composite::slots_to_powcoeffs_thin(&original_H));
        let coeffs_to_slots = create_circuit_cached::<_, _, LOG>(&plaintext_ring, &filename_keys![coeffs2slots, m: m, p: &p, e: e], cache_dir, || composite::powcoeffs_to_slots_thin(&H));
        
        return ThinBootstrapData::new_with_digit_extract_and_lin_transform(self, C, digit_extract, slots_to_coeffs, coeffs_to_slots, modswitch_strategy);
    }
}

pub struct ThinBootstrapData<Params, Strategy>
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
    tmp_coprime_modulus_plaintext: PlaintextRing<Params>,
    pre_bootstrap_rns_factors: usize
}

impl<Params, Strategy> ThinBootstrapData<Params, Strategy>
    where Params: BGVInstantiation, 
        Strategy: BGVModswitchStrategy<Params>,
        <CiphertextRing<Params> as RingStore>::Type: AsBGVPlaintext<Params>
{
    pub fn new_with_digit_extract_and_lin_transform(
        params: &ThinBootstrapParams<Params>, 
        C: &CiphertextRing<Params>,
        digit_extract: DigitExtract, 
        slots_to_coeffs_thin: PlaintextCircuit<Params::PlaintextRing>, 
        coeffs_to_slots_thin: PlaintextCircuit<Params::PlaintextRing>,
        modswitch_strategy: Strategy
    ) -> Self {
        let (p, r) = is_prime_power(&ZZbig, &params.t).unwrap();
        let v = params.v;
        let e = r + v;
        assert!(ZZbig.eq_el(&p, digit_extract.p()));
        assert_eq!(r, digit_extract.r());
        assert_eq!(e, digit_extract.e());
        let plaintext_ring_hierarchy: Vec<_> = ((r + 1)..=e).map(|k| params.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), k))).collect();
        let original_plaintext_ring = params.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r));
        Self {
            modswitch_strategy: modswitch_strategy,
            tmp_coprime_modulus_plaintext: params.scheme_params.create_plaintext_ring(ZZbig.add(ZZbig.pow(ZZbig.clone_el(&p), e), ZZbig.one())),
            coeffs_to_slots_thin: coeffs_to_slots_thin.change_ring_uniform(|x| x.change_ring(|x| Params::encode_plain(plaintext_ring_hierarchy.last().unwrap(), C, &x))),
            slots_to_coeffs_thin: slots_to_coeffs_thin.change_ring_uniform(|x| x.change_ring(|x| Params::encode_plain(&original_plaintext_ring, C, &x))),
            digit_extract: digit_extract,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy,
            pre_bootstrap_rns_factors: params.pre_bootstrap_rns_factors,
            original_plaintext_ring: original_plaintext_ring
        }
    }
    
    pub fn with_lin_transform(self, C: &CiphertextRing<Params>, new_slots_to_coeffs: PlaintextCircuit<Params::PlaintextRing>, new_coeffs_to_slots: PlaintextCircuit<Params::PlaintextRing>) -> Self {
        Self {
            coeffs_to_slots_thin: new_coeffs_to_slots.change_ring_uniform(|x| x.change_ring(|x| Params::encode_plain(self.intermediate_plaintext_ring(), C, &x))),
            slots_to_coeffs_thin: new_slots_to_coeffs.change_ring_uniform(|x| x.change_ring(|x| Params::encode_plain(&self.original_plaintext_ring, C, &x))),
            digit_extract: self.digit_extract,
            original_plaintext_ring: self.original_plaintext_ring,
            plaintext_ring_hierarchy: self.plaintext_ring_hierarchy,
            pre_bootstrap_rns_factors: self.pre_bootstrap_rns_factors,
            modswitch_strategy: self.modswitch_strategy,
            tmp_coprime_modulus_plaintext: self.tmp_coprime_modulus_plaintext
        }
    }
}

impl<Params, Strategy> ThinBootstrapData<Params, Strategy>
    where Params: BGVInstantiation, 
        Strategy: BGVModswitchStrategy<Params>,
        <CiphertextRing<Params> as RingStore>::Type: AsBGVPlaintext<Params>
{
    pub fn create(
        params: &ThinBootstrapParams<Params>, 
        digit_extract: DigitExtract, 
        slots_to_coeffs_thin: PlaintextCircuit<<CiphertextRing<Params> as RingStore>::Type>, 
        coeffs_to_slots_thin: PlaintextCircuit<<CiphertextRing<Params> as RingStore>::Type>,
        modswitch_strategy: Strategy
    ) -> Self {
        let (p, r) = is_prime_power(&ZZbig, &params.t).unwrap();
        let v = params.v;
        let e = r + v;
        assert!(ZZbig.eq_el(&p, digit_extract.p()));
        assert_eq!(r, digit_extract.r());
        assert_eq!(e, digit_extract.e());
        let plaintext_ring_hierarchy: Vec<_> = ((r + 1)..=e).map(|k| params.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), k))).collect();
        let original_plaintext_ring = params.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r));
        Self {
            modswitch_strategy: modswitch_strategy,
            tmp_coprime_modulus_plaintext: params.scheme_params.create_plaintext_ring(ZZbig.add(ZZbig.pow(ZZbig.clone_el(&p), e), ZZbig.one())),
            coeffs_to_slots_thin: coeffs_to_slots_thin,
            slots_to_coeffs_thin: slots_to_coeffs_thin,
            digit_extract: digit_extract,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy,
            pre_bootstrap_rns_factors: params.pre_bootstrap_rns_factors,
            original_plaintext_ring: original_plaintext_ring
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
        self.plaintext_ring_hierarchy.last().unwrap()
    }

    pub fn base_plaintext_ring(&self) -> &PlaintextRing<Params> {
        &self.original_plaintext_ring
    }

    pub fn with_digit_extraction(self, new: DigitExtract) -> Self {
        assert!(ZZbig.eq_el(&self.p(), new.p()));
        assert_eq!(self.r(), new.r());
        assert_eq!(self.e(), new.e());
        Self {
            coeffs_to_slots_thin: self.coeffs_to_slots_thin,
            digit_extract: new,
            original_plaintext_ring: self.original_plaintext_ring,
            plaintext_ring_hierarchy: self.plaintext_ring_hierarchy,
            pre_bootstrap_rns_factors: self.pre_bootstrap_rns_factors,
            slots_to_coeffs_thin: self.slots_to_coeffs_thin,
            modswitch_strategy: self.modswitch_strategy,
            tmp_coprime_modulus_plaintext: self.tmp_coprime_modulus_plaintext
        }
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
    ///    must contain a Galois key for each Galois automorphism listed in [`ThinBootstrapData::required_galois_keys()`],
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
        rk: &RelinKey<'a, Params>,
        gks: &[(GaloisGroupEl, KeySwitchKey<'a, Params>)],
        used_sk: SecretKeyDistribution,
        debug_sk: Option<&SecretKey<Params>>
    ) -> ModulusAwareCiphertext<Params, Strategy>
        where Params: 'a
    {
        assert!(LOG || debug_sk.is_none());
        assert!(ZZbig.eq_el(&ZZbig.pow(ZZbig.clone_el(self.p()), self.r()), &int_cast(P_base.base_ring().integer_ring().clone_el(P_base.base_ring().modulus()), ZZbig, P_base.base_ring().integer_ring())));
        if LOG {
            println!("Starting Bootstrapping")
        }

        // First, we mod-switch the input ciphertext so that it only has `self.pre_bootstrap_rns_factors` many RNS factors
        let input_dropped_rns_factors = {
            assert!(C_master.base_ring().len() - ct_dropped_moduli.len() >= self.pre_bootstrap_rns_factors);
            let gk_digits = gks[0].1.gadget_vector_digits();
            let (drop_additional, _) = compute_optimal_special_modulus(
                C_master.get_ring(),
                ct_dropped_moduli,
                C_master.base_ring().len() - ct_dropped_moduli.len() - self.pre_bootstrap_rns_factors,
                gk_digits
            );
            drop_additional.union(&ct_dropped_moduli)
        };
        let C_input = Params::mod_switch_down_C(C_master, &input_dropped_rns_factors);
        let ct_input = Params::mod_switch_ct(P_base, &C_input, &Params::mod_switch_down_C(C_master, ct_dropped_moduli), ct);
        assert_eq!(C_input.base_ring().len(), self.pre_bootstrap_rns_factors);

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

        let P_main = self.plaintext_ring_hierarchy.last().unwrap();
        assert!(ZZbig.eq_el(&ZZbig.pow(ZZbig.clone_el(self.p()), self.e()), &int_cast(P_main.base_ring().integer_ring().clone_el(P_main.base_ring().modulus()), ZZbig, P_main.base_ring().integer_ring())));

        let noisy_decryption = log_time::<_, _, LOG, _>("2. Computing noisy decryption c0 + c1 * s", |[]| {
            // this is slightly more complicated than in BFV, since we cannot mod-switch to a ciphertext modulus that is not coprime to `t = p^r`.
            // Instead, we first multiply by `p^v`, then mod-switch to `p^e + 1`, and then reduce the shortest lift of the result modulo `p^e`.
            // This will introduce the overflow modulo `p^e + 1` as error in the lower bits, which we will later remove during digit extraction
            let ZZbig_to_C_input = C_input.inclusion().compose(C_input.base_ring().can_hom(&ZZbig).unwrap());
            let values_scaled = Ciphertext {
                c0: ZZbig_to_C_input.mul_map(values_in_coefficients.c0, ZZbig.pow(ZZbig.clone_el(self.p()), self.v())),
                c1: ZZbig_to_C_input.mul_map(values_in_coefficients.c1, ZZbig.pow(ZZbig.clone_el(self.p()), self.v())),
                implicit_scale: values_in_coefficients.implicit_scale
            };
            // change to `p^e + 1`
            let (c0, c1) = Params::mod_switch_to_plaintext(P_main, &self.tmp_coprime_modulus_plaintext, &C_input, values_scaled);

            // reduce modulo `p^e`, which will introduce additional error in the lower digits
            let mod_pe = P_main.base_ring().can_hom(self.tmp_coprime_modulus_plaintext.base_ring().integer_ring()).unwrap();
            let (c0, c1) = (
                P_main.from_canonical_basis(self.tmp_coprime_modulus_plaintext.wrt_canonical_basis(&c0).iter().map(|x| mod_pe.map(self.tmp_coprime_modulus_plaintext.base_ring().smallest_lift(x)))),
                P_main.from_canonical_basis(self.tmp_coprime_modulus_plaintext.wrt_canonical_basis(&c1).iter().map(|x| mod_pe.map(self.tmp_coprime_modulus_plaintext.base_ring().smallest_lift(x))))
            );

            let enc_sk = Params::enc_sk(P_main, C_master);
            return ModulusAwareCiphertext {
                data: Params::hom_add_plain(P_main, C_master, &c0, Params::hom_mul_plain(P_main, C_master, &c1, enc_sk)),
                info: self.modswitch_strategy.info_for_fresh_encryption(P_main, C_master, used_sk),
                dropped_rns_factor_indices: RNSFactorIndexList::empty(),
                sk: used_sk
            };
        });
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
                C_master,
                digit_extraction_input,
                rk,
                key_switches,
                debug_sk
            ).0;
        });
        return final_result;
    }
}

impl DigitExtract {

    pub fn evaluate_bgv<'a, Params: BGVInstantiation, Strategy: BGVModswitchStrategy<Params>, const LOG: bool>(
        &self,
        modswitch_strategy: &Strategy, 
        P_base: &PlaintextRing<Params>, 
        P: &[PlaintextRing<Params>], 
        C_master: &CiphertextRing<Params>, 
        input: ModulusAwareCiphertext<Params, Strategy>, 
        rk: &RelinKey<'a, Params>,
        key_switches: &mut usize,
        debug_sk: Option<&SecretKey<Params>>
    ) -> (ModulusAwareCiphertext<Params, Strategy>, ModulusAwareCiphertext<Params, Strategy>) {
        assert!(LOG || debug_sk.is_none());

        let (p, actual_r) = is_prime_power(ZZbig, &int_cast(P_base.base_ring().integer_ring().clone_el(P_base.base_ring().modulus()), ZZbig, P_base.base_ring().integer_ring())).unwrap();
        assert_el_eq!(ZZbig, self.p(), &p);
        assert!(actual_r >= self.r());
        for i in 0..(self.e() - self.r()) {
            assert!(P_base.base_ring().integer_ring().get_ring() == P[i].base_ring().integer_ring().get_ring());
            assert_el_eq!(ZZbig, ZZbig.pow(ZZbig.clone_el(self.p()), actual_r + i + 1), int_cast(P[i].base_ring().integer_ring().clone_el(P[i].base_ring().modulus()), ZZbig, P[i].base_ring().integer_ring()));
        }
        let get_P = |exp: usize| if exp == self.r() {
            P_base
        } else {
            &P[exp - self.r() - 1]
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
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 2,
        t: ZZbig.clone_el(&t),
        pre_bootstrap_rns_factors: 2
    };
    let P = params.create_plaintext_ring(t);
    let C_master = params.create_ciphertext_ring(790..800);
    let key_switch_params = RNSGadgetVectorDigitIndices::select_digits(5, C_master.base_ring().len());

    let bootstrapper = bootstrap_params.build_pow2::<_, true>(&C_master, DefaultModswitchStrategy::<_, _, true>::new(NaiveBGVNoiseEstimator), None);
    
    let sk = Pow2BGV::gen_sk(&C_master, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BGV::gen_gk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &g, &key_switch_params);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = Pow2BGV::gen_rk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &key_switch_params);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BGV::enc_sym(&P, &C_master, &mut rng, &m, &sk);
    let ct_result = bootstrapper.bootstrap_thin::<true>(
        &C_master, 
        &P, 
        &RNSFactorIndexList::empty(),
        ct, 
        &rk, 
        &gk,
        SecretKeyDistribution::UniformTernary,
        Some(&sk)
    );
    let C_result = Pow2BGV::mod_switch_down_C(&C_master, &ct_result.dropped_rns_factor_indices);
    let sk_result = Pow2BGV::mod_switch_sk(&C_result, &C_master, &sk);

    assert_el_eq!(P, P.int_hom().map(2), Pow2BGV::dec(&P, &C_result, ct_result.data, &sk_result));
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
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 7,
        t: ZZbig.clone_el(&t),
        pre_bootstrap_rns_factors: 2
    };
    let P = params.create_plaintext_ring(t);
    let C_master = params.create_ciphertext_ring(805..820);
    assert_eq!(15, C_master.base_ring().len());
    let key_switch_params = RNSGadgetVectorDigitIndices::select_digits(7, C_master.base_ring().len());

    let bootstrapper = bootstrap_params.build_odd::<_, true>(&C_master, DefaultModswitchStrategy::<_, _, false>::new(NaiveBGVNoiseEstimator), Some("."));
    
    let sk = CompositeBGV::gen_sk(&C_master, &mut rng, sk_distr);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeBGV::gen_gk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &g, &key_switch_params);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = CompositeBGV::gen_rk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &key_switch_params);
    
    let m = P.int_hom().map(2);
    let ct = CompositeBGV::enc_sym(&P, &C_master, &mut rng, &m, &sk);
    let ct_result = bootstrapper.bootstrap_thin::<true>(
        &C_master, 
        &P, 
        &RNSFactorIndexList::empty(),
        ct, 
        &rk, 
        &gk,
        sk_distr,
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
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 2,
        t: ZZbig.clone_el(&t),
        pre_bootstrap_rns_factors: 2
    };
    let P = params.create_plaintext_ring(t);
    let C_master = params.create_ciphertext_ring(805..820);
    assert_eq!(15, C_master.base_ring().len());
    let gk_params = RNSGadgetVectorDigitIndices::select_digits(7, C_master.base_ring().len());
    let rk_params = RNSGadgetVectorDigitIndices::select_digits(3, C_master.base_ring().len());

    let bootstrapper = bootstrap_params.build_pow2::<_, true>(&C_master, DefaultModswitchStrategy::<_, _, false>::new(NaiveBGVNoiseEstimator), Some("."));
    
    let sk = Pow2BGV::gen_sk(&C_master, &mut rng, sk_distr);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BGV::gen_gk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &g, &gk_params);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = Pow2BGV::gen_rk(bootstrapper.intermediate_plaintext_ring(), &C_master, &mut rng, &sk, &rk_params);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BGV::enc_sym(&P, &C_master, &mut rng, &m, &sk);
    let ct_result = bootstrapper.bootstrap_thin::<true>(
        &C_master, 
        &P, 
        &RNSFactorIndexList::empty(),
        ct, 
        &rk, 
        &gk,
        sk_distr,
        None
    );
    let C_result = Pow2BGV::mod_switch_down_C(&C_master, &ct_result.dropped_rns_factor_indices);
    let sk_result = Pow2BGV::mod_switch_sk(&C_result, &C_master, &sk);
    println!("final noise budget: {}", Pow2BGV::noise_budget(&P, &C_result, &ct_result.data, &sk_result));
    let result = Pow2BGV::dec(&P, &C_result, ct_result.data, &sk_result);
    assert_el_eq!(P, P.int_hom().map(2), result);
}
