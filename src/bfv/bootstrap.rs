
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::cell::LazyCell;

use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::homomorphism::*;
use feanor_math::integer::{int_cast, IntegerRingStore};
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnRingStore;

use serde::Serialize;
use serde::de::DeserializeSeed;

use crate::bgv::modswitch::{level_digits, drop_rns_factors_balanced};
use crate::cyclotomic::CyclotomicRingStore;
use crate::lintransform::matmul::MatmulTransform;
use crate::digitextract::*;
use crate::lintransform::pow2;
use crate::lintransform::composite;
use crate::circuit::serialization::{DeserializeSeedPlaintextCircuit, SerializablePlaintextCircuit};

use super::*;

///
/// Parameters for an instantiation of BFV bootstrapping.
/// 
#[derive(Clone, Debug)]
pub struct ThinBootstrapParams<Params: BFVCiphertextParams> {
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
    pub t: i64,
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

///
/// Precomputed data required to perform BFV bootstrapping.
/// 
/// The standard way to create this data is to use [`ThinBootstrapParams::build_pow2()`]
/// or [`ThinBootstrapParams::build_odd()`], but note that this computation is very expensive.
/// 
pub struct ThinBootstrapData<Params: BFVCiphertextParams> {
    digit_extract: DigitExtract,
    slots_to_coeffs_thin: PlaintextCircuit<<PlaintextRing<Params> as RingStore>::Type>,
    coeffs_to_slots_thin: PlaintextCircuit<<PlaintextRing<Params> as RingStore>::Type>,
    plaintext_ring_hierarchy: Vec<PlaintextRing<Params>>,
    pre_bootstrap_rns_factors: usize
}

impl<Params: BFVCiphertextParams> ThinBootstrapParams<Params>
    where NumberRing<Params>: Clone
{
    fn read_or_create_circuit<F, const LOG: bool>(P: &PlaintextRing<Params>, base_name: &str, cache_dir: Option<&str>, create: F) -> PlaintextCircuit<<PlaintextRing<Params> as RingStore>::Type>
        where F: FnOnce() -> PlaintextCircuit<<PlaintextRing<Params> as RingStore>::Type>
    {
        if let Some(cache_dir) = cache_dir {
            let (p, e) = is_prime_power(ZZi64, P.base_ring().modulus()).unwrap();
            let filename = format!("{}/{}_m{}_p{}_e{}.json", cache_dir, base_name, P.m(), p, e);
            if let Ok(file) = File::open(filename.as_str()) {
                if LOG {
                    println!("Reading {} from file {}", base_name, filename);
                }
                let reader = serde_json::de::IoRead::new(BufReader::new(file));
                let mut deserializer = serde_json::Deserializer::new(reader);
                let deserialized = DeserializeSeedPlaintextCircuit::new(P, &P.galois_group()).deserialize(&mut deserializer).unwrap();
                return deserialized;
            }
            let result = log_time::<_, _, LOG, _>(format!("Creating circuit {}", base_name).as_str(), |[]| create());
            let file = File::create(filename.as_str()).unwrap();
            let writer = BufWriter::new(file);
            let mut serializer = serde_json::Serializer::new(writer);
            SerializablePlaintextCircuit::new(P, &P.galois_group(), &result).serialize(&mut serializer).unwrap();
            return result;
        } else {
            return create();
        }
    }

    pub fn build_pow2<const LOG: bool>(&self, cache_dir: Option<&str>) -> ThinBootstrapData<Params> {
        let log2_m = ZZ.abs_log2_ceil(&(self.scheme_params.number_ring().m() as i64)).unwrap();
        assert_eq!(self.scheme_params.number_ring().m(), 1 << log2_m);

        let (p, r) = is_prime_power(&ZZ, &self.t).unwrap();
        let v = self.v;
        let e = r + v;
        if LOG {
            println!("Setting up bootstrapping for plaintext modulus p^r = {}^{} = {} within the cyclotomic ring Q[X]/(Phi_{})", p, r, self.t, self.scheme_params.number_ring().m());
            println!("Choosing e = r + v = {} + {}", r, v);
        }

        let plaintext_ring = self.scheme_params.create_plaintext_ring(ZZ.pow(p, e));
        let original_plaintext_ring = self.scheme_params.create_plaintext_ring(ZZ.pow(p, r));

        let digit_extract = DigitExtract::new_default(p, e, r);

        let H = LazyCell::new(|| {
            let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(plaintext_ring.m() as u64), p);
            if let Some(cache_dir) = cache_dir {
                HypercubeIsomorphism::new_cache_file::<LOG>(&plaintext_ring, hypercube, cache_dir)
            } else {
                HypercubeIsomorphism::new::<LOG>(&plaintext_ring, hypercube)
            }
        });
        let original_H = LazyCell::new(|| H.change_modulus(&original_plaintext_ring));

        let slots_to_coeffs = Self::read_or_create_circuit::<_, LOG>(&original_plaintext_ring, "slots_to_coeffs", cache_dir, || MatmulTransform::to_circuit_many(pow2::slots_to_coeffs_thin(&original_H), &original_H));
        let coeffs_to_slots = Self::read_or_create_circuit::<_, LOG>(&plaintext_ring, "coeffs_to_slots", cache_dir, || pow2::coeffs_to_slots_thin(&H));
        let plaintext_ring_hierarchy = ((r + 1)..=e).map(|k| self.scheme_params.create_plaintext_ring(ZZ.pow(p, k))).collect();

        return ThinBootstrapData {
            digit_extract,
            slots_to_coeffs_thin: slots_to_coeffs,
            coeffs_to_slots_thin: coeffs_to_slots,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy,
            pre_bootstrap_rns_factors: self.pre_bootstrap_rns_factors
        };
    }

    pub fn build_odd<const LOG: bool>(&self, cache_dir: Option<&str>) -> ThinBootstrapData<Params> {
        assert!(self.scheme_params.number_ring().m() % 2 != 0);

        let (p, r) = is_prime_power(&ZZ, &self.t).unwrap();
        let v = self.v;
        let e = r + v;
        if LOG {
            println!("Setting up bootstrapping for plaintext modulus p^r = {}^{} = {} within the cyclotomic ring Q[X]/(Phi_{})", p, r, self.t, self.scheme_params.number_ring().m());
            println!("Choosing e = r + v = {} + {}", r, v);
        }

        let plaintext_ring = self.scheme_params.create_plaintext_ring(ZZ.pow(p, e));
        let original_plaintext_ring = self.scheme_params.create_plaintext_ring(ZZ.pow(p, r));

        let digit_extract = if p == 2 && e <= 23 {
            DigitExtract::new_precomputed_p_is_2(p, e, r)
        } else {
            DigitExtract::new_default(p, e, r)
        };

        let H = LazyCell::new(|| {
            let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(plaintext_ring.m() as u64), p);
            if let Some(cache_dir) = cache_dir {
                HypercubeIsomorphism::new_cache_file::<LOG>(&plaintext_ring, hypercube, cache_dir)
            } else {
                HypercubeIsomorphism::new::<LOG>(&plaintext_ring, hypercube)
            }
        });
        let original_H = LazyCell::new(|| H.change_modulus(&original_plaintext_ring));

        let slots_to_coeffs = Self::read_or_create_circuit::<_, LOG>(&original_plaintext_ring, "slots_to_coeffs", cache_dir, || MatmulTransform::to_circuit_many(composite::slots_to_powcoeffs_thin(&original_H), &original_H));
        let coeffs_to_slots = Self::read_or_create_circuit::<_, LOG>(&plaintext_ring, "coeffs_to_slots", cache_dir, || MatmulTransform::to_circuit_many(composite::powcoeffs_to_slots_thin(&H), &H));
        let plaintext_ring_hierarchy = ((r + 1)..=e).map(|k| self.scheme_params.create_plaintext_ring(ZZ.pow(p, k))).collect();

        return ThinBootstrapData {
            digit_extract,
            slots_to_coeffs_thin: slots_to_coeffs,
            coeffs_to_slots_thin: coeffs_to_slots,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy,
            pre_bootstrap_rns_factors: self.pre_bootstrap_rns_factors
        };
    }
}

impl<Params: BFVCiphertextParams> ThinBootstrapData<Params> {

    fn r(&self) -> usize {
        self.digit_extract.e() - self.digit_extract.v()
    }

    fn e(&self) -> usize {
        self.digit_extract.e()
    }

    fn v(&self) -> usize {
        self.digit_extract.v()
    }

    fn p(&self) -> i64 {
        self.digit_extract.p()
    }

    pub fn required_galois_keys(&self, P: &PlaintextRing<Params>) -> Vec<CyclotomicGaloisGroupEl> {
        let mut result = Vec::new();
        result.extend(self.slots_to_coeffs_thin.required_galois_keys(&P.galois_group()).into_iter());
        result.extend(self.coeffs_to_slots_thin.required_galois_keys(&P.galois_group()).into_iter());
        result.sort_by_key(|g| P.galois_group().representative(*g));
        result.dedup_by(|g, s| P.galois_group().eq_el(*g, *s));
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
    ///  - `debug_sk` can be a reference to a secret key, which is used to print out decryptions
    ///    of intermediate results for debugging purposes. May only be set if `LOG == true`.
    /// 
    #[instrument(skip_all)]
    pub fn bootstrap_thin<'a, const LOG: bool>(
        &self,
        C: &CiphertextRing<Params>, 
        C_mul: &CiphertextRing<Params>, 
        P_base: &PlaintextRing<Params>,
        ct: Ciphertext<Params>,
        rk: &RelinKey<'a, Params>,
        gks: &[(CyclotomicGaloisGroupEl, KeySwitchKey<'a, Params>)],
        debug_sk: Option<&SecretKey<Params>>
    ) -> Ciphertext<Params>
        where Params: 'a
    {
        assert!(LOG || debug_sk.is_none());
        assert_eq!(ZZ.pow(self.p(), self.r()), *P_base.base_ring().modulus());
        if LOG {
            println!("Starting Bootstrapping")
        }
        if let Some(sk) = debug_sk {
            Params::dec_println_slots(P_base, C, &ct, sk);
        }

        // First, we mod-switch the input ciphertext so that subsequent operations that less time; Note that we mod-switch it
        // to `self.pre_bootstrap_rns_factors` + special moduli RNS factors, where the special moduli are designed to take care
        // of the noise caused by the slots-to-coeffs transform 
        let input_dropped_rns_factors = {
            assert!(C.base_ring().len() >= self.pre_bootstrap_rns_factors);
            let gk_digits = gks[0].1.0.gadget_vector_digits();
            let (to_drop, special_modulus) = compute_optimal_special_modulus::<Params>(
                P_base,
                C,
                RNSFactorIndexList::empty_ref(),
                C.base_ring().len() - self.pre_bootstrap_rns_factors,
                gk_digits
            );
            to_drop.subtract(&special_modulus)
        };
        let C_input = RingValue::from(C.get_ring().drop_rns_factor(&input_dropped_rns_factors));
        let ct_input = Params::mod_switch_ct(P_base, &C_input, C, ct);
        let sk_input = debug_sk.map(|sk| C_input.get_ring().drop_rns_factor_element(C.get_ring(), &input_dropped_rns_factors, C.clone_el(&sk)));
        if let Some(sk) = &sk_input {
            Params::dec_println_slots(P_base, &C_input, &ct_input, sk);
        }

        let values_in_coefficients = log_time::<_, _, LOG, _>("1. Computing Slots-to-Coeffs transform", |[key_switches]| {
            let galois_group = P_base.galois_group();
            let modswitched_gks = self.slots_to_coeffs_thin.required_galois_keys(&galois_group).iter().map(|g| {
                if let Some((_, gk)) = gks.iter().filter(|(provided_g, _)| galois_group.eq_el(*g, *provided_g)).next() {
                    (*g, (
                        gk.0.clone(C.get_ring()).modulus_switch(C_input.get_ring(), &input_dropped_rns_factors, C.get_ring()),
                        gk.1.clone(C.get_ring()).modulus_switch(C_input.get_ring(), &input_dropped_rns_factors, C.get_ring()), 
                    ))
                } else {
                    panic!("missing galois key for {}", galois_group.underlying_ring().format(&galois_group.to_ring_el(*g)))
                }
            }).collect::<Vec<_>>();
            let result = self.slots_to_coeffs_thin.evaluate_bfv::<Params>(P_base, &C_input, None, std::slice::from_ref(&ct_input), None, &modswitched_gks, key_switches);
            assert_eq!(1, result.len());
            return result.into_iter().next().unwrap();
        });
        if let Some(sk) = &sk_input {
            Params::dec_println(P_base, &C_input, &values_in_coefficients, sk);
        }

        let P_main = self.plaintext_ring_hierarchy.last().unwrap();
        debug_assert_eq!(ZZ.pow(self.p(), self.e()), *P_main.base_ring().modulus());

        let noisy_decryption = log_time::<_, _, LOG, _>("2. Computing noisy decryption c0 + c1 * s", |[]| {
            let (c0, c1) = Params::mod_switch_to_plaintext(P_main, &C_input, values_in_coefficients);
            let enc_sk = Params::enc_sk(P_main, C);
            return Params::hom_add_plain(P_main, C, &c0, Params::hom_mul_plain(P_main, C, &c1, enc_sk));
        });
        if let Some(sk) = debug_sk {
            Params::dec_println(P_main, C, &noisy_decryption, sk);
        }

        let noisy_decryption_in_slots = log_time::<_, _, LOG, _>("3. Computing Coeffs-to-Slots transform", |[key_switches]| {
            let result = self.coeffs_to_slots_thin.evaluate_bfv::<Params>(P_main, C, None, std::slice::from_ref(&noisy_decryption), None, gks, key_switches);
            assert_eq!(1, result.len());
            return result.into_iter().next().unwrap();
        });
        if let Some(sk) = debug_sk {
            Params::dec_println_slots(P_main, C, &noisy_decryption_in_slots, sk);
        }

        let result = log_time::<_, _, LOG, _>("4. Performing digit extraction", |[key_switches]| {
            let rounding_divisor_half = P_main.base_ring().coerce(&ZZbig, ZZbig.rounded_div(ZZbig.pow(int_cast(self.p(), ZZbig, ZZ), self.v()), &ZZbig.int_hom().map(2)));
            let digit_extraction_input = Params::hom_add_plain(P_main, C, &P_main.inclusion().map(rounding_divisor_half), noisy_decryption_in_slots);
            self.digit_extract.evaluate_bfv::<Params>(P_base, &self.plaintext_ring_hierarchy, C, C_mul, digit_extraction_input, rk, key_switches).0
        });
        return result;
    }
}

/// 
/// Finds `drop_additional_count` RNS factors outside of `dropped_factors_input` and
/// a set `special_modulus` of RNS factors, which optimize performance and noise growth
/// for a key-switch.
/// 
/// For details, see the BGV equivalent [`crate::bgv::modswitch::DefaultModswitchStrategy::compute_optimal_special_modulus()`].
/// 
#[instrument(skip_all)]
pub fn compute_optimal_special_modulus<Params>(
    _P: &PlaintextRing<Params>,
    C: &CiphertextRing<Params>,
    dropped_factors_input: &RNSFactorIndexList,
    drop_additional_count: usize,
    key_switch_key_digits: &RNSGadgetVectorDigitIndices
) -> (/* B_final = */ Box<RNSFactorIndexList>, /* B_special = */ Box<RNSFactorIndexList>)
    where Params: BFVCiphertextParams
{
    let a = key_switch_key_digits.iter().map(|digit| digit.end - digit.start).collect::<Vec<_>>();
    let b = key_switch_key_digits.iter().map(|digit| digit.end - digit.start - dropped_factors_input.num_within(&digit)).collect::<Vec<_>>();
    if let Some((c, d)) = level_digits(&a, &b, drop_additional_count) {
        let B_additional = key_switch_key_digits.iter().enumerate().flat_map(|(digit_idx, digit)| digit.filter(|i| !dropped_factors_input.contains(*i)).take(c[digit_idx]));
        let B_final = RNSFactorIndexList::from(dropped_factors_input.iter().copied().chain(B_additional).collect::<Vec<_>>(), C.base_ring().len());
        let B_special = RNSFactorIndexList::from(key_switch_key_digits.iter().enumerate().flat_map(|(digit_idx, digit)| digit.filter(|i| B_final.contains(*i)).take(d[digit_idx])).collect::<Vec<_>>(), C.base_ring().len());
        assert_eq!(B_final.len(), dropped_factors_input.len() + drop_additional_count);
        return (B_final, B_special);
    } else {
        let additional_drop = drop_rns_factors_balanced(&key_switch_key_digits.remove_indices(dropped_factors_input), drop_additional_count);
        let B_final = additional_drop.pullback(dropped_factors_input);
        let B_special = B_final.clone();
        assert_eq!(B_final.len(), dropped_factors_input.len() + drop_additional_count);
        return (B_final, B_special);
    }
}

impl DigitExtract {
    
    ///
    /// Evaluates the digit extraction function on a BFV-encrypted input.
    /// 
    /// For details on how the digit extraction function looks like, see
    /// [`DigitExtract`] and [`DigitExtract::evaluate_generic()`].
    /// 
    pub fn evaluate_bfv<'a, Params: BFVCiphertextParams>(&self, 
        P_base: &PlaintextRing<Params>, 
        P: &[PlaintextRing<Params>], 
        C: &CiphertextRing<Params>, 
        C_mul: &CiphertextRing<Params>, 
        input: Ciphertext<Params>, 
        rk: &RelinKey<'a, Params>,
        key_switches: &mut usize
    ) -> (Ciphertext<Params>, Ciphertext<Params>) {
        let (p, actual_r) = is_prime_power(StaticRing::<i64>::RING, P_base.base_ring().modulus()).unwrap();
        assert_eq!(self.p(), p);
        assert!(actual_r >= self.r());
        for i in 0..(self.e() - self.r()) {
            assert_eq!(ZZ.pow(self.p(), actual_r + i + 1), *P[i].base_ring().modulus());
        }
        let get_P = |exp: usize| if exp == self.r() {
            P_base
        } else {
            &P[exp - self.r() - 1]
        };
        let result = self.evaluate_generic(
            input,
            |exp, params, circuit| circuit.evaluate_bfv::<Params>(
                get_P(exp),
                C,
                Some(C_mul),
                params,
                Some(rk),
                &[],
                key_switches
            ),
            |_, _, x| x
        );
        return result;
    }
}

#[test]
fn test_pow2_bfv_thin_bootstrapping_17() {
    let mut rng = thread_rng();
    
    // 8 slots of rank 16
    let params = Pow2BFV {
        log2_q_min: 790,
        log2_q_max: 800,
        log2_N: 7,
        ciphertext_allocator: DefaultCiphertextAllocator::default(),
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };
    let t = 17;
    let digits = 3;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 2,
        t: t,
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_pow2::<true>(Some("."));
    
    let P = params.create_plaintext_ring(t);
    let (C, C_mul) = params.create_ciphertext_rings();
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, None);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| (g, Pow2BFV::gen_gk(&C, &mut rng, &sk, g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len())))).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()));
    
    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        Some(&sk)
    );

    assert_el_eq!(P, P.int_hom().map(2), Pow2BFV::dec(&P, &C, res_ct, &sk));
}

#[test]
fn test_pow2_bfv_thin_bootstrapping_23() {
    let mut rng = thread_rng();
    
    // 4 slots of rank 32
    let params = Pow2BFV {
        log2_q_min: 790,
        log2_q_max: 800,
        log2_N: 7,
        ciphertext_allocator: DefaultCiphertextAllocator::default(),
        negacyclic_ntt: PhantomData::<DefaultNegacyclicNTT>
    };
    let t = 23;
    let digits = 3;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 2,
        t: t,
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_pow2::<true>(Some("."));
    
    let P = params.create_plaintext_ring(t);
    let (C, C_mul) = params.create_ciphertext_rings();
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng, None);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| (g, Pow2BFV::gen_gk(&C, &mut rng, &sk, g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len())))).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()));
    
    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        None
    );

    assert_el_eq!(P, P.int_hom().map(2), Pow2BFV::dec(&P, &C, res_ct, &sk));
}

#[test]
fn test_composite_bfv_thin_bootstrapping_2() {
    // let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    // let filtered_chrome_layer = chrome_layer.with_filter(tracing_subscriber::filter::filter_fn(|metadata| !["small_basis_to_mult_basis", "mult_basis_to_small_basis", "small_basis_to_coeff_basis", "coeff_basis_to_small_basis"].contains(&metadata.name())));
    // tracing_subscriber::registry().with(filtered_chrome_layer).init();
    
    let mut rng = thread_rng();
    
    let params = CompositeBFV {
        log2_q_min: 660,
        log2_q_max: 700,
        m1: 31,
        m2: 11,
        ciphertext_allocator: DefaultCiphertextAllocator::default()
    };
    let t = 8;
    let digits = 3;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 9,
        t: t,
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_odd::<true>(Some("."));
    
    let P = params.create_plaintext_ring(t);
    let (C, C_mul) = params.create_ciphertext_rings();
    
    let sk = CompositeBFV::gen_sk(&C, &mut rng, None);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| (g, CompositeBFV::gen_gk(&C, &mut rng, &sk, g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len())))).collect::<Vec<_>>();
    let rk = CompositeBFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()));
    
    let m = P.int_hom().map(2);
    let ct = CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        None
    );

    assert_el_eq!(P, P.int_hom().map(2), CompositeBFV::dec(&P, &C, res_ct, &sk));
}

#[test]
#[ignore]
fn measure_time_double_rns_composite_bfv_thin_bootstrapping() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    let filtered_chrome_layer = chrome_layer.with_filter(tracing_subscriber::filter::filter_fn(|metadata| !["small_basis_to_mult_basis", "mult_basis_to_small_basis", "small_basis_to_coeff_basis", "coeff_basis_to_small_basis"].contains(&metadata.name())));
    tracing_subscriber::registry().with(filtered_chrome_layer).init();
    
    let mut rng = thread_rng();
    
    let params = CompositeBFV {
        log2_q_min: 805,
        log2_q_max: 820,
        m1: 37,
        m2: 949,
        ciphertext_allocator: DefaultCiphertextAllocator::default()
    };
    let t = 4;
    let sk_hwt = Some(256);
    let digits = 7;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 7,
        t: t,
        pre_bootstrap_rns_factors: 2
    };
    let bootstrapper = bootstrap_params.build_odd::<true>(Some("."));
    
    let P = params.create_plaintext_ring(t);
    let (C, C_mul) = params.create_ciphertext_rings();
    
    let sk = CompositeBFV::gen_sk(&C, &mut rng, sk_hwt);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| (g, CompositeBFV::gen_gk(&C, &mut rng, &sk, g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len())))).collect::<Vec<_>>();
    let rk = CompositeBFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()));
    
    let m = P.int_hom().map(2);
    let ct = CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        None
    );

    assert_el_eq!(P, P.int_hom().map(2), CompositeBFV::dec(&P, &C, res_ct, &sk));
}

#[test]
#[ignore]
fn measure_time_single_rns_composite_bfv_thin_bootstrapping() {
    let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
    let filtered_chrome_layer = chrome_layer.with_filter(tracing_subscriber::filter::filter_fn(|metadata| !["small_basis_to_mult_basis", "mult_basis_to_small_basis", "small_basis_to_coeff_basis", "coeff_basis_to_small_basis"].contains(&metadata.name())));
    tracing_subscriber::registry().with(filtered_chrome_layer).init();
    
    let mut rng = thread_rng();
    
    let params = CompositeSingleRNSBFV {
        log2_q_min: 805,
        log2_q_max: 820,
        m1: 37,
        m2: 949,
        ciphertext_allocator: DefaultCiphertextAllocator::default(),
        convolution: PhantomData::<DefaultConvolution>
    };
    let t = 4;
    let sk_hwt = Some(256);
    let digits = 7;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params,
        v: 7,
        t: t,
        pre_bootstrap_rns_factors: 2
    };
    let params = &bootstrap_params.scheme_params;
    let bootstrapper = bootstrap_params.build_odd::<true>(Some("."));
    
    let P = params.create_plaintext_ring(t);
    let (C, C_mul) = params.create_ciphertext_rings();
    
    let sk = CompositeSingleRNSBFV::gen_sk(&C, &mut rng, sk_hwt);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| (g, CompositeSingleRNSBFV::gen_gk(&C, &mut rng, &sk, g, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len())))).collect::<Vec<_>>();
    let rk = CompositeSingleRNSBFV::gen_rk(&C, &mut rng, &sk, &RNSGadgetVectorDigitIndices::select_digits(digits, C.base_ring().len()));
    
    let m = P.int_hom().map(2);
    let ct = CompositeSingleRNSBFV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &C_mul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        None
    );

    assert_el_eq!(P, P.int_hom().map(2), CompositeSingleRNSBFV::dec(&P, &C, res_ct, &sk));
}
