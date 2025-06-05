
use std::fs::File;
use std::io::{BufReader, BufWriter};

use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::homomorphism::*;
use feanor_math::integer::{int_cast, IntegerRingStore};
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnRingStore;

use serde::Serialize;
use serde::de::DeserializeSeed;

use crate::cyclotomic::CyclotomicRingStore;
use crate::lintransform::matmul::MatmulTransform;
use crate::digitextract::*;
use crate::lintransform::pow2;
use crate::lintransform::composite;
use crate::circuit::serialization::{DeserializeSeedPlaintextCircuit, SerializablePlaintextCircuit};

use super::*;

#[derive(Clone, Debug)]
pub struct ThinBootstrapParams<Params: BFVCiphertextParams> {
    pub scheme_params: Params,
    pub v: usize,
    pub t: i64
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
    plaintext_ring_hierarchy: Vec<PlaintextRing<Params>>
}

impl<Params: BFVCiphertextParams> ThinBootstrapParams<Params>
    where NumberRing<Params>: Clone
{
    fn read_or_create_circuit<F, const LOG: bool>(H: &DefaultHypercube<NumberRing<Params>>, base_name: &str, cache_dir: Option<&str>, create: F) -> PlaintextCircuit<<PlaintextRing<Params> as RingStore>::Type>
        where F: FnOnce() -> PlaintextCircuit<<PlaintextRing<Params> as RingStore>::Type>
    {
        if let Some(cache_dir) = cache_dir {
            let filename = format!("{}/{}_m{}_p{}_e{}.json", cache_dir, base_name, H.hypercube().m(), H.p(), H.e());
            if let Ok(file) = File::open(filename.as_str()) {
                if LOG {
                    println!("Reading {} from file {}", base_name, filename);
                }
                let reader = serde_json::de::IoRead::new(BufReader::new(file));
                let mut deserializer = serde_json::Deserializer::new(reader);
                let deserialized = DeserializeSeedPlaintextCircuit::new(H.ring(), H.galois_group()).deserialize(&mut deserializer).unwrap();
                return deserialized;
            }
            let result = log_time::<_, _, LOG, _>(format!("Creating circuit {}", base_name).as_str(), |[]| create());
            let file = File::create(filename.as_str()).unwrap();
            let writer = BufWriter::new(file);
            let mut serializer = serde_json::Serializer::new(writer);
            SerializablePlaintextCircuit::new(H.ring(), H.galois_group(), &result).serialize(&mut serializer).unwrap();
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

        let hypercube = HypercubeStructure::halevi_shoup_hypercube(plaintext_ring.galois_group(), p);
        let H = if let Some(cache_dir) = cache_dir {
            HypercubeIsomorphism::new_cache_file::<LOG>(&plaintext_ring, hypercube, cache_dir)
        } else {
            HypercubeIsomorphism::new::<LOG>(&plaintext_ring, hypercube)
        };
        let original_H = H.change_modulus(&original_plaintext_ring);
        let slots_to_coeffs = Self::read_or_create_circuit::<_, LOG>(&original_H, "slots_to_coeffs", cache_dir, || MatmulTransform::to_circuit_many(pow2::slots_to_coeffs_thin(&original_H), &original_H));
        let coeffs_to_slots = Self::read_or_create_circuit::<_, LOG>(&H, "coeffs_to_slots", cache_dir, || pow2::coeffs_to_slots_thin(&H));
        let plaintext_ring_hierarchy = ((r + 1)..=e).map(|k| self.scheme_params.create_plaintext_ring(ZZ.pow(p, k))).collect();

        return ThinBootstrapData {
            digit_extract,
            slots_to_coeffs_thin: slots_to_coeffs,
            coeffs_to_slots_thin: coeffs_to_slots,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy
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

        let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(plaintext_ring.m() as u64), p);
        let H = if let Some(cache_dir) = cache_dir {
            HypercubeIsomorphism::new_cache_file::<LOG>(&plaintext_ring, hypercube, cache_dir)
        } else {
            HypercubeIsomorphism::new::<LOG>(&plaintext_ring, hypercube)
        };
        let original_H = H.change_modulus(&original_plaintext_ring);
        let slots_to_coeffs = Self::read_or_create_circuit::<_, LOG>(&original_H, "slots_to_coeffs", cache_dir, || MatmulTransform::to_circuit_many(composite::slots_to_powcoeffs_thin(&original_H), &original_H));
        let coeffs_to_slots = Self::read_or_create_circuit::<_, LOG>(&H, "coeffs_to_slots", cache_dir, || MatmulTransform::to_circuit_many(composite::powcoeffs_to_slots_thin(&H), &H));
        let plaintext_ring_hierarchy = ((r + 1)..=e).map(|k| self.scheme_params.create_plaintext_ring(ZZ.pow(p, k))).collect();

        return ThinBootstrapData {
            digit_extract,
            slots_to_coeffs_thin: slots_to_coeffs,
            coeffs_to_slots_thin: coeffs_to_slots,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy
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

    #[instrument(skip_all)]
    pub fn bootstrap_thin<'a, const LOG: bool>(
        &self,
        C: &CiphertextRing<Params>, 
        C_mul: &CiphertextRing<Params>, 
        P_base: &PlaintextRing<Params>,
        ct: Ciphertext<Params>,
        rk: &RelinKey<'a, Params>,
        gk: &[(CyclotomicGaloisGroupEl, KeySwitchKey<'a, Params>)],
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

        let P_main = self.plaintext_ring_hierarchy.last().unwrap();
        debug_assert_eq!(ZZ.pow(self.p(), self.e()), *P_main.base_ring().modulus());

        // TODO: mod-switch down before computing slots-to-coeffs

        let values_in_coefficients = log_time::<_, _, LOG, _>("1. Computing Slots-to-Coeffs transform", |[key_switches]| {
            let result = self.slots_to_coeffs_thin.evaluate_bfv::<Params>(P_base, C, None, std::slice::from_ref(&ct), None, gk, key_switches);
            assert_eq!(1, result.len());
            return result.into_iter().next().unwrap();
        });
        if let Some(sk) = debug_sk {
            Params::dec_println(P_base, C, &values_in_coefficients, sk);
        }

        let noisy_decryption = log_time::<_, _, LOG, _>("2. Computing noisy decryption c0 + c1 * s", |[]| {
            let (c0, c1) = Params::mod_switch_to_plaintext(P_main, C, values_in_coefficients);
            let enc_sk = Params::enc_sk(P_main, C);
            return Params::hom_add_plain(P_main, C, &c0, Params::hom_mul_plain(P_main, C, &c1, enc_sk));
        });
        if let Some(sk) = debug_sk {
            Params::dec_println(P_main, C, &noisy_decryption, sk);
        }

        let noisy_decryption_in_slots = log_time::<_, _, LOG, _>("3. Computing Coeffs-to-Slots transform", |[key_switches]| {
            let result = self.coeffs_to_slots_thin.evaluate_bfv::<Params>(P_main, C, None, std::slice::from_ref(&noisy_decryption), None, gk, key_switches);
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
        t: t
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
        t: t
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
        t: t
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
        t: t
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
        t: t
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
