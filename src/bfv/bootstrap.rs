
use std::cell::LazyCell;

use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::homomorphism::*;
use feanor_math::assert_el_eq;
use feanor_math::integer::{int_cast, IntegerRingStore};
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnRingStore;

use crate::bfv::eval::AsBFVPlaintext;
use crate::bgv::modswitch::compute_optimal_special_modulus;
use crate::circuit::create_circuit_cached;
use crate::digit_extract::DigitExtract;
use crate::lin_transform::composite;
use crate::lin_transform::pow2;

use super::*;

///
/// Parameters for an instantiation of BFV bootstrapping.
/// 
#[derive(Clone, Debug)]
pub struct ThinBootstrapParams<Params: BFVInstantiation> {
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
    /// The number of RNS factors required to evaluate the Slots-to-Coeffs transform
    /// without noise overflow, assuming hybrid key-switching is used for the Galois
    /// automorphisms.
    /// 
    /// The first step of thin bootstrapping is the Slots-to-Coeffs transform, which
    /// is still applied to the original ciphertext. Since the ciphertext is homomorphically
    /// decrypted directly afterwards, we don't need much precision at this point anymore.
    /// Hence, we modulus-switch it to a modulus with this many RNS factors, to save
    /// time during the Slots-to-Coeffs transform.
    /// 
    /// Note that the Slots-to-Coeffs transform explicitly uses hybrid key-switching, hence
    /// it will use some additional RNS factors to offset the noise added by the linear
    /// transform. In other words, this number should be large enough for a modulus-switch
    /// to an RNS base of this many moduli not to cause a noise overflow, but does not have
    /// to consider additional noise caused by the Slots-to-Coeffs transform. 
    pub pre_bootstrap_rns_factors: usize
}

impl<Params> ThinBootstrapParams<Params>
    where Params: BFVInstantiation, 
        Params::PlaintextRing: SerializableElementRing,
        NumberRing<Params>: Clone,
        Params::PlaintextRing: AsBFVPlaintext<Params>
{
    pub fn build_pow2<const LOG: bool>(&self, cache_dir: Option<&str>) -> ThinBootstrapData<Params> {
        let log2_m = ZZi64.abs_log2_ceil(&(self.scheme_params.number_ring().galois_group().m() as i64)).unwrap();
        assert_eq!(self.scheme_params.number_ring().galois_group().m(), 1 << log2_m);

        let (p, r) = is_prime_power(&ZZbig, &self.t).unwrap();
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

        return ThinBootstrapData::create(self, digit_extract, slots_to_coeffs, coeffs_to_slots);
    }

    pub fn build_odd<const LOG: bool>(&self, cache_dir: Option<&str>) -> ThinBootstrapData<Params> {
        assert!(self.scheme_params.number_ring().galois_group().m() % 2 != 0);

        let (p, r) = is_prime_power(&ZZbig, &self.t).unwrap();
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
        let slots_to_coeffs = create_circuit_cached::<_, _, LOG>(&original_plaintext_ring, &filename_keys![slots2coeffs, m: m, p: &p, r: r], cache_dir, || composite::slots_to_powcoeffs_thin(&original_H));
        let coeffs_to_slots = create_circuit_cached::<_, _, LOG>(&plaintext_ring, &filename_keys![coeffs2slots, m: m, p: &p, e: e], cache_dir, || composite::powcoeffs_to_slots_thin(&H));

        return ThinBootstrapData::create(self, digit_extract, slots_to_coeffs, coeffs_to_slots);
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
pub struct SparseKeyEncapsulationData<Params: BFVInstantiation> {
    /// A reduced-modulus ciphertext ring `R/q'R`, where we can publish a key-switching key
    /// from the standard secret key to the sparse secret key. 
    /// 
    /// Such a key-switching key (or indeed any ciphertext encrypted with the sparse secret key)
    /// usually cannot be published for the normal ciphertext ring `R/qR` since a sparse secret key
    /// provides less security at the same ciphertext modulus. However, for a reduced ciphertext
    /// modulus, a sparse secret key can still be secure.
    pub C_switch_to_sparse: CiphertextRing<Params>,
    /// A key-switch key for switching from the standard secret key to the sparse secret
    /// key. This should be defined over the ciphertext ring [`SparseKeyEncapsulationData::C_switch_to_sparse`].
    pub switch_to_sparse_key: KeySwitchKey<Params>,
    /// An encryption of the sparse secret key w.r.t. the standard secret key. This should be
    /// defined over the standard BFV ciphertext ring.
    pub encapsulated_key: Ciphertext<Params>,
    /// The plaintext modulus w.r.t. which the sparse key is encrypted to get the
    /// [`SparseKeyEncapsulationData::encapsulated_key`]
    pub encapsulated_key_plaintext_modulus: El<BigIntRing>
}

impl<Params> SparseKeyEncapsulationData<Params>
    where Params: BFVInstantiation, 
        Params::PlaintextRing: AsBFVPlaintext<Params>
{
    pub fn create<R: CryptoRng + Rng>(P: &PlaintextRing<Params>, C: &CiphertextRing<Params>, C_switch_to_sparse: CiphertextRing<Params>, sparse_sk: SecretKey<Params>, standard_sk: &SecretKey<Params>, mut rng: R, noise_sigma: f64) -> Self {
        let switch_to_sparse_key = Params::gen_switch_key(
            &C_switch_to_sparse, 
            &mut rng,
            &Params::mod_switch_sk(P, &C_switch_to_sparse, C, standard_sk),
            &Params::mod_switch_sk(P, &C_switch_to_sparse, C, &sparse_sk),
            &RNSGadgetVectorDigitIndices::select_digits(C_switch_to_sparse.base_ring().len(), C_switch_to_sparse.base_ring().len()),
            noise_sigma
        );
        let ZZ_to_Pbase = P.base_ring().can_hom(P.base_ring().integer_ring()).unwrap().compose(P.base_ring().integer_ring().can_hom(&ZZbig).unwrap());
        let sparse_sk_as_plain = P.from_canonical_basis(C.wrt_canonical_basis(&sparse_sk).iter().map(|x| ZZ_to_Pbase.map(C.base_ring().smallest_lift(x))));
        let encapsulated_key = Params::enc_sym(P, C, &mut rng, &sparse_sk_as_plain, standard_sk, noise_sigma);
        SparseKeyEncapsulationData { 
            C_switch_to_sparse: C_switch_to_sparse, 
            switch_to_sparse_key: switch_to_sparse_key, 
            encapsulated_key: encapsulated_key,
            encapsulated_key_plaintext_modulus: int_cast(P.base_ring().integer_ring().clone_el(P.base_ring().modulus()), ZZbig, P.base_ring().integer_ring())
        }
    }
}

///
/// Precomputed data required to perform BFV bootstrapping.
/// 
/// The standard way to create this data is to use [`ThinBootstrapParams::build_pow2()`]
/// or [`ThinBootstrapParams::build_odd()`], but note that the involved computation is very expensive.
/// 
pub struct ThinBootstrapData<Params: BFVInstantiation> {
    /// The [`DigitExtract`] object used to compute the digit extraction step
    /// of BFV bootstrapping
    digit_extract: DigitExtract,
    /// The circuit used to compute the (thin) Slots-to-Coeffs linear transform
    /// of BFV bootstrapping
    slots_to_coeffs_thin: PlaintextCircuit<Params::PlaintextRing>,
    /// The circuit used to compute the (thin) Coeffs-to-Slots linear transform
    /// of BFV bootstrapping
    coeffs_to_slots_thin: PlaintextCircuit<Params::PlaintextRing>,
    /// The plaintext rings `R/p^kR` for every `r <= k <= e`, which all are used
    /// as intermediate plaintext rings during bootstrapping
    plaintext_ring_hierarchy: Vec<PlaintextRing<Params>>,
    original_plaintext_ring: PlaintextRing<Params>,
    /// The number of RNS factors required to evaluate the Slots-to-Coeffs transform
    /// without noise overflow, assuming hybrid key-switching is used for the Galois
    /// automorphisms. 
    /// 
    /// See [`ThinBootstrapParams::pre_bootstrap_rns_factors`] for more details.
    pre_bootstrap_rns_factors: usize
}

impl<Params> ThinBootstrapData<Params>
    where Params: BFVInstantiation, 
        Params::PlaintextRing: AsBFVPlaintext<Params>
{
    pub fn create(
        params: &ThinBootstrapParams<Params>, 
        digit_extract: DigitExtract, 
        slots_to_coeffs_thin: PlaintextCircuit<Params::PlaintextRing>, 
        coeffs_to_slots_thin: PlaintextCircuit<Params::PlaintextRing>
    ) -> Self {
        let (p, r) = is_prime_power(&ZZbig, &params.t).unwrap();
        let v = params.v;
        let e = r + v;
        assert!(ZZbig.eq_el(&p, digit_extract.p()));
        assert_eq!(r, digit_extract.r());
        assert_eq!(e, digit_extract.e());
        let plaintext_ring_hierarchy = ((r + 1)..=e).map(|k| params.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), k))).collect();
        Self {
            coeffs_to_slots_thin: coeffs_to_slots_thin,
            digit_extract: digit_extract,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy,
            pre_bootstrap_rns_factors: params.pre_bootstrap_rns_factors,
            slots_to_coeffs_thin: slots_to_coeffs_thin,
            original_plaintext_ring: params.scheme_params.create_plaintext_ring(ZZbig.pow(ZZbig.clone_el(&p), r))
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

    fn p(&self) -> El<BigIntRing> {
        ZZbig.clone_el(self.digit_extract.p())
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
            slots_to_coeffs_thin: self.slots_to_coeffs_thin
        }
    }

    pub fn with_lin_transform(self, new_slots_to_coeffs: PlaintextCircuit<Params::PlaintextRing>, new_coeffs_to_slots: PlaintextCircuit<Params::PlaintextRing>) -> Self {
        Self {
            coeffs_to_slots_thin: new_coeffs_to_slots,
            digit_extract: self.digit_extract,
            original_plaintext_ring: self.original_plaintext_ring,
            plaintext_ring_hierarchy: self.plaintext_ring_hierarchy,
            pre_bootstrap_rns_factors: self.pre_bootstrap_rns_factors,
            slots_to_coeffs_thin: new_slots_to_coeffs
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
    ///  - `C` is the ciphertext ring w.r.t. which both input and output ciphertexts are defined
    ///  - `C_mul` is the extended ciphertext ring used for multiplications
    ///  - `P_base` is the current plaintext ring; `ct` must be a valid BGV ciphertext encrypting
    ///    a message from `P_base`
    ///  - `ct` is the ciphertext to bootstrap; It must be thinly packed (i.e. each slot may only
    ///    contain an element of `Z/(t)`), otherwise this function will cause immediate noise overflow.
    ///  - `rk` is a relinearization key, to be used for computing products
    ///  - `gks` is a list of Galois keys, to be used for applying Galois automorphisms. This list
    ///    must contain a Galois key for each Galois automorphism listed in [`ThinBootstrapData::required_galois_keys()`],
    ///    but may contain additional Galois keys
    ///  - `sparse_key_encapsulation` optionally contains all data required to temporarily switch
    ///    to a sparse secret key before bootstrapping. If used, this can make bootstrapping work
    ///    with significantly smaller parameters.
    ///  - `debug_sk` can be a reference to a secret key, which is used to print out decryptions
    ///    of intermediate results for debugging purposes. May only be set if `LOG == true`.
    /// 
    #[instrument(skip_all)]
    pub fn bootstrap_thin<const LOG: bool>(
        &self,
        C: &CiphertextRing<Params>, 
        C_mul: &CiphertextRing<Params>, 
        P_base: &PlaintextRing<Params>,
        ct: Ciphertext<Params>,
        rk: &RelinKey<Params>,
        gks: &[(GaloisGroupEl, KeySwitchKey<Params>)],
        sk_encaps_data: Option<&SparseKeyEncapsulationData<Params>>,
        debug_sk: Option<&SecretKey<Params>>
    ) -> Ciphertext<Params> {

        assert!(LOG || debug_sk.is_none());
        let ZZ = P_base.base_ring().integer_ring();
        assert_el_eq!(ZZbig, ZZbig.pow(self.p(), self.r()), int_cast(ZZ.clone_el(P_base.base_ring().modulus()), ZZbig, ZZ));
        log_time::<_, _, LOG, _>("Performing thin bootstrapping", |[]| {

            if let Some(sk) = debug_sk {
                Params::dec_println_slots(P_base, C, &ct, sk, None);
            }

            // First, we mod-switch the input ciphertext so that subsequent operations that less time; Note that we mod-switch it
            // to `self.pre_bootstrap_rns_factors` + special moduli RNS factors, where the special moduli are designed to take care
            // of the noise caused by the slots-to-coeffs transform 
            let input_dropped_rns_factors = {
                assert!(C.base_ring().len() >= self.pre_bootstrap_rns_factors);
                let gk_digits = gks[0].1.0.gadget_vector_digits();
                let (to_drop, special_modulus) = compute_optimal_special_modulus(
                    C.get_ring(),
                    RNSFactorIndexList::empty_ref(),
                    C.base_ring().len() - self.pre_bootstrap_rns_factors,
                    gk_digits
                );
                to_drop.subtract(&special_modulus)
            };
            let C_input = RingValue::from(C.get_ring().drop_rns_factor(&input_dropped_rns_factors));
            let ct_input = Params::mod_switch_ct(P_base, &C_input, C, ct);
            let sk_input = debug_sk.map(|sk| C_input.get_ring().drop_rns_factor_element(C.get_ring(), &input_dropped_rns_factors, &sk));
            if let Some(sk) = &sk_input {
                Params::dec_println_slots(P_base, &C_input, &ct_input, sk, None);
            }

            let values_in_coefficients = log_time::<_, _, LOG, _>("1. Computing Slots-to-Coeffs transform", |[key_switches]| {
                let galois_group = P_base.acting_galois_group();
                let modswitched_gks = self.slots_to_coeffs_thin.required_galois_keys(&galois_group).iter().map(|g| {
                    if let Some((_, gk)) = gks.iter().filter(|(provided_g, _)| galois_group.eq_el(g, provided_g)).next() {
                        (g.clone(), (
                            gk.0.clone(C.get_ring()).modulus_switch(C_input.get_ring(), &input_dropped_rns_factors, C.get_ring()),
                            gk.1.clone(C.get_ring()).modulus_switch(C_input.get_ring(), &input_dropped_rns_factors, C.get_ring()), 
                        ))
                    } else {
                        panic!("missing galois key for {}", galois_group.underlying_ring().format(galois_group.as_ring_el(g)))
                    }
                }).collect::<Vec<_>>();
                let result = self.slots_to_coeffs_thin.evaluate_bfv::<Params, _>(P_base, P_base, &C_input, None, std::slice::from_ref(&ct_input), None, &modswitched_gks, key_switches, None);
                assert_eq!(1, result.len());
                return result.into_iter().next().unwrap();
            });
            if let Some(sk) = &sk_input {
                Params::dec_println(P_base, &C_input, &values_in_coefficients, sk);
            }

            let P_main = self.plaintext_ring_hierarchy.last().unwrap();
            assert_el_eq!(ZZbig, ZZbig.pow(self.p(), self.e()), int_cast(ZZ.clone_el(P_main.base_ring().modulus()), ZZbig, ZZ));

            let noisy_decryption = if let Some(sk_encaps_data) = sk_encaps_data {
                let ct_with_sparse_key = log_time::<_, _, LOG, _>("2.1. Switching to sparse key", |[]| {
                    let ct_modswitched = Params::mod_switch_ct(&P_base, &sk_encaps_data.C_switch_to_sparse, &C_input, values_in_coefficients);
                    Params::key_switch(&sk_encaps_data.C_switch_to_sparse, ct_modswitched, &sk_encaps_data.switch_to_sparse_key)
                });
                log_time::<_, _, LOG, _>("2.2. Computing noisy decryption c0 + c1 * s", |[]| {
                    let (c0, c1) = Params::mod_switch_to_plaintext(P_main, &sk_encaps_data.C_switch_to_sparse, ct_with_sparse_key);
                    return Params::hom_add_plain(P_main, C, &c0, Params::hom_mul_plain(P_main, C, &c1, Params::clone_ct(C, &sk_encaps_data.encapsulated_key)));
                })
            } else {
                log_time::<_, _, LOG, _>("2. Computing noisy decryption c0 + c1 * s", |[]| {
                    let (c0, c1) = Params::mod_switch_to_plaintext(P_main, &C_input, values_in_coefficients);
                    let enc_sk = Params::enc_sk(P_main, C);
                    return Params::hom_add_plain(P_main, C, &c0, Params::hom_mul_plain(P_main, C, &c1, enc_sk));
                })
            };
            if let Some(sk) = debug_sk {
                Params::dec_println(P_main, C, &noisy_decryption, sk);
            }

            let noisy_decryption_in_slots = log_time::<_, _, LOG, _>("3. Computing Coeffs-to-Slots transform", |[key_switches]| {
                let result = self.coeffs_to_slots_thin.evaluate_bfv::<Params, _>(P_main, P_main, C, None, std::slice::from_ref(&noisy_decryption), None, gks, key_switches, None);
                assert_eq!(1, result.len());
                return result.into_iter().next().unwrap();
            });
            if let Some(sk) = debug_sk {
                Params::dec_println_slots(P_main, C, &noisy_decryption_in_slots, sk, None);
            }

            let result = log_time::<_, _, LOG, _>("4. Performing digit extraction", |[key_switches]| {
                let rounding_divisor_half = P_main.base_ring().coerce(&ZZbig, ZZbig.rounded_div(ZZbig.pow(self.p(), self.v()), &ZZbig.int_hom().map(2)));
                let digit_extraction_input = Params::hom_add_plain(P_main, C, &P_main.inclusion().map(rounding_divisor_half), noisy_decryption_in_slots);
                self.digit_extract.evaluate_bfv::<Params>(P_base, &self.plaintext_ring_hierarchy, C, C_mul, digit_extraction_input, rk, key_switches, debug_sk).0
            });
            return result;
        })
    }
}

impl DigitExtract {
    
    ///
    /// Evaluates the digit extraction function on a BFV-encrypted input.
    /// 
    /// For details on how the digit extraction function looks like, see
    /// [`DigitExtract`] and [`DigitExtract::evaluate_generic()`].
    /// 
    pub fn evaluate_bfv<Params: BFVInstantiation>(&self, 
        P_base: &PlaintextRing<Params>, 
        P: &[PlaintextRing<Params>], 
        C: &CiphertextRing<Params>, 
        C_mul: &CiphertextRing<Params>, 
        input: Ciphertext<Params>, 
        rk: &RelinKey<Params>,
        key_switches: &mut usize,
        debug_sk: Option<&SecretKey<Params>>
    ) -> (Ciphertext<Params>, Ciphertext<Params>) {
        let ZZ = P_base.base_ring().integer_ring();
        let (p, actual_r) = is_prime_power(ZZ, P_base.base_ring().modulus()).unwrap();
        assert_el_eq!(ZZbig, self.p(), int_cast(ZZ.clone_el(&p), ZZbig, ZZ));
        assert!(actual_r >= self.r());
        for i in 0..(self.e() - self.r()) {
            assert_el_eq!(ZZbig, ZZbig.pow(ZZbig.clone_el(self.p()), actual_r + i + 1), int_cast(ZZ.clone_el(P[i].base_ring().modulus()), ZZbig, ZZ));
        }
        let get_P = |exp: usize| if exp == self.r() {
            P_base
        } else {
            &P[exp - self.r() - 1]
        };
        let result = self.evaluate_generic(
            input,
            |exp, params, circuit| {
                circuit.evaluate_bfv::<Params, _>(
                    ZZi64,
                    get_P(exp),
                    C,
                    Some(C_mul),
                    params,
                    Some(rk),
                    &[],
                    key_switches,
                    debug_sk
                )
            },
            |exp_from, _, x| {
                if let Some(sk) = debug_sk {
                    Params::dec_println_slots(get_P(exp_from), C, &x, sk, Some("."));
                }
                return x;
            }
        );
        return result;
    }
}

#[test]
fn test_pow2_bfv_thin_bootstrapping_17() {
    let mut rng = rand::rng();
    
    // 8 slots of rank 16
    let params = Pow2BFV::new(1 << 8);
    let t = 17;
    let digits = 3;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 2,
        t: int_cast(t, ZZbig, ZZi64),
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_pow2::<true>(Some("."));
    
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(790..800);
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BFV::gen_gk(&C, &mut rng, &sk, &g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
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
    let mut rng = rand::rng();
    
    // 4 slots of rank 32
    let params = Pow2BFV::new(1 << 8);
    let t = 23;
    let digits = 3;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 2,
        t: int_cast(t, ZZbig, ZZi64),
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_pow2::<true>(Some("."));
    
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(790..800);
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BFV::gen_gk(&C, &mut rng, &sk, &g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
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
    let mut rng = rand::rng();
    
    let params = Pow2BFV::new(1 << 8);
    let t = 17;
    let digits = 3;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 2,
        t: int_cast(t, ZZbig, ZZi64),
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_pow2::<true>(Some("."));
    
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(790..800);
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = Pow2BFV::gen_gk(&C, &mut rng, &sk, &g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
    let sparse_sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::SparseWithHwt(16));
    let C_switch_to_sparse = RingValue::from(C.get_ring().drop_rns_factor(RNSFactorIndexList::from_ref(&[0, 3, 4], C.base_ring().len())));
    let encaps = SparseKeyEncapsulationData::create(bootstrapper.plaintext_ring_hierarchy.last().unwrap(), &C, C_switch_to_sparse, sparse_sk, &sk, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
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
    let mut rng = rand::rng();
    
    let params = CompositeBFV::new(31, 11);
    let t = 8;
    let digits = 3;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 9,
        t: int_cast(t, ZZbig, ZZi64),
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_odd::<true>(Some("."));
    
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(685..700);
    
    let sk = CompositeBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeBFV::gen_gk(&C, &mut rng, &sk, &g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = CompositeBFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
    
    let m = P.int_hom().map(2);
    let ct = CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        None,
        None
    );

    assert_el_eq!(P, P.int_hom().map(2), CompositeBFV::dec(&P, &C, res_ct, &sk));
}

#[test]
fn test_digit_extract_homomorphic() {
    let mut rng = rand::rng();

    let params = Pow2BFV::new(1 << 7);
    let P1 = params.create_plaintext_ring(int_cast(17 * 17, ZZbig, ZZi64));
    let P2 = params.create_plaintext_ring(int_cast(17 * 17 * 17, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(790..800);

    let sk = Pow2BFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(7, C.base_ring().len()), 3.2);
    let m = P2.int_hom().map(17 * 17 + 2 * 17 + 5);
    let ct = Pow2BFV::enc_sym(&P2, &C, &mut rng, &m, &sk, 3.2);

    let digitextract = DigitExtract::new_default(17, 2, 1);
    let (ct_high, ct_low) = digitextract.evaluate_bfv::<Pow2BFV>(&P1, std::slice::from_ref(&P2), &C, &C_mul, ct, &rk, &mut 0, Some(&sk));
    let m_high = Pow2BFV::dec(&P1, &C, Pow2BFV::clone_ct(&C, &ct_high), &sk);
    assert!(P1.wrt_canonical_basis(&m_high).iter().skip(1).all(|x| P1.base_ring().is_zero(&x)));
    let m_high = P1.base_ring().smallest_positive_lift(P1.wrt_canonical_basis(&m_high).at(0));
    assert_eq!(2, m_high % 17);
    
    let m_low = Pow2BFV::dec(&P2, &C, Pow2BFV::clone_ct(&C, &ct_low), &sk);
    assert!(P1.wrt_canonical_basis(&m_low).iter().skip(1).all(|x| P2.base_ring().is_zero(&x)));
    let m_low = P1.base_ring().smallest_positive_lift(P1.wrt_canonical_basis(&m_low).at(0));
    assert_eq!(5, m_low % (17 * 17));
}

#[test]
#[ignore]
fn measure_time_double_rns_composite_bfv_thin_bootstrapping() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    let filtered_chrome_layer = chrome_layer.with_filter(tracing_subscriber::filter::filter_fn(|metadata| !["small_basis_to_mult_basis", "mult_basis_to_small_basis", "small_basis_to_coeff_basis", "coeff_basis_to_small_basis"].contains(&metadata.name())));
    tracing_subscriber::registry().with(filtered_chrome_layer).init();
    
    let mut rng = rand::rng();
    
    let params = CompositeBFV::new(37, 949);
    let t = 4;
    let digits = 7;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 6,
        t: int_cast(t, ZZbig, ZZi64),
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_odd::<true>(Some("."));
    
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(805..820);
    
    let sk = CompositeBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeBFV::gen_gk(&C, &mut rng, &sk, &g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
        (g, gk)
    }).collect::<Vec<_>>();
    let rk = CompositeBFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()), 3.2);
    let sparse_sk = CompositeBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::SparseWithHwt(128));
    let C_switch_to_sparse = RingValue::from(C.get_ring().drop_rns_factor(&RNSFactorIndexList::from(2..C.base_ring().len(), C.base_ring().len())));
    let sparse_sk_encapsulation_data = SparseKeyEncapsulationData::create(bootstrapper.intermediate_plaintext_ring(), &C, C_switch_to_sparse, sparse_sk, &sk, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        Some(&sparse_sk_encapsulation_data),
        None
    );

    println!("final noise budget: {}", CompositeBFV::noise_budget(&P, &C, &res_ct, &sk));
    assert_el_eq!(P, P.int_hom().map(2), CompositeBFV::dec(&P, &C, res_ct, &sk));
}

#[test]
#[ignore]
fn measure_time_single_rns_composite_bfv_thin_bootstrapping() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    let filtered_chrome_layer = chrome_layer.with_filter(tracing_subscriber::filter::filter_fn(|metadata| !["small_basis_to_mult_basis", "mult_basis_to_small_basis", "small_basis_to_coeff_basis", "coeff_basis_to_small_basis"].contains(&metadata.name())));
    tracing_subscriber::registry().with(filtered_chrome_layer).init();
    
    let mut rng = rand::rng();
    
    let params = CompositeSingleRNSBFV::new(37, 949);
    let t = 4;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 6,
        t: int_cast(t, ZZbig, ZZi64),
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_odd::<true>(Some("."));
    
    let P = params.create_plaintext_ring(int_cast(t, ZZbig, ZZi64));
    let (C, C_mul) = params.create_ciphertext_rings(805..820);
    let key_switch_params = RNSGadgetVectorDigitIndices::select_digits(7, C.base_ring().len());
    
    let sk = CompositeSingleRNSBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::UniformTernary);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| {
        let gk = CompositeSingleRNSBFV::gen_gk(&C, &mut rng, &sk, &g, &key_switch_params, 3.2);
        return (g, gk);
    }).collect::<Vec<_>>();
    let rk = CompositeSingleRNSBFV::gen_rk(&C, &mut rng, &sk, &key_switch_params, 3.2);
    let sparse_sk = CompositeSingleRNSBFV::gen_sk(&C, &mut rng, SecretKeyDistribution::SparseWithHwt(128));
    let C_switch_to_sparse = RingValue::from(C.get_ring().drop_rns_factor(&RNSFactorIndexList::from(2..C.base_ring().len(), C.base_ring().len())));
    let sparse_sk_encapsulation_data = SparseKeyEncapsulationData::create(bootstrapper.intermediate_plaintext_ring(), &C, C_switch_to_sparse, sparse_sk, &sk, &mut rng, 3.2);

    let m = P.int_hom().map(2);
    let ct = CompositeSingleRNSBFV::enc_sym(&P, &C, &mut rng, &m, &sk, 3.2);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        Some(&sparse_sk_encapsulation_data),
        None
    );

    println!("final noise budget: {}", CompositeSingleRNSBFV::noise_budget(&P, &C, &res_ct, &sk));
    assert_el_eq!(P, P.int_hom().map(2), CompositeSingleRNSBFV::dec(&P, &C, res_ct, &sk));
}
