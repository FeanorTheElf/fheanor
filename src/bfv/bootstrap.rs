
use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::homomorphism::*;
use feanor_math::integer::{int_cast, IntegerRingStore};
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnRingStore;

use crate::cyclotomic::CyclotomicRingStore;
use crate::lintransform::matmul::MatmulTransform;
use crate::digitextract::*;
use crate::lintransform::pow2;
use crate::lintransform::composite;

use super::*;

#[derive(Clone, Debug)]
pub struct ThinBootstrapParams<Params: BFVParams> {
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
pub struct ThinBootstrapData<Params: BFVParams> {
    digit_extract: DigitExtract,
    slots_to_coeffs_thin: PlaintextCircuit<<PlaintextRing<Params> as RingStore>::Type>,
    coeffs_to_slots_thin: PlaintextCircuit<<PlaintextRing<Params> as RingStore>::Type>,
    plaintext_ring_hierarchy: Vec<PlaintextRing<Params>>
}

impl<Params: BFVParams> ThinBootstrapParams<Params>
    where NumberRing<Params>: Clone
{
    pub fn build_pow2<const LOG: bool>(&self) -> ThinBootstrapData<Params> {
        let log2_n = ZZ.abs_log2_ceil(&(self.scheme_params.number_ring().n() as i64)).unwrap();
        assert_eq!(self.scheme_params.number_ring().n(), 1 << log2_n);

        let (p, r) = is_prime_power(&ZZ, &self.t).unwrap();
        let s_can_norm = <_ as HENumberRing>::inf_to_can_norm_expansion_factor(&self.scheme_params.number_ring());
        let v = self.v;
        let e = r + v;
        if LOG {
            println!("Setting up bootstrapping for plaintext modulus p^r = {}^{} = {} within the cyclotomic ring Q[X]/(Phi_{})", p, r, self.t, <_ as HECyclotomicNumberRing>::n(&self.scheme_params.number_ring()));
            println!("Choosing e = r + v = {} + {}", r, v);
        }

        let plaintext_ring = self.scheme_params.create_plaintext_ring(ZZ.pow(p, e));
        let original_plaintext_ring = self.scheme_params.create_plaintext_ring(ZZ.pow(p, r));

        let digit_extract = DigitExtract::new_default(p, e, r);

        let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(plaintext_ring.n() as u64), p);
        let H = HypercubeIsomorphism::new::<LOG>(&plaintext_ring, hypercube);
        let original_H = H.change_modulus(&original_plaintext_ring);
        let slots_to_coeffs = log_time::<_, _, LOG, _>("Creating Slots-to-Coeffs transform", |[]| MatmulTransform::to_circuit_many(pow2::slots_to_coeffs_thin(&original_H), &original_H));
        let coeffs_to_slots = log_time::<_, _, LOG, _>("Creating Coeffs-to-Slots transform", |[]| pow2::coeffs_to_slots_thin(&H));
        let plaintext_ring_hierarchy = ((r + 1)..=e).map(|k| self.scheme_params.create_plaintext_ring(ZZ.pow(p, k))).collect();

        return ThinBootstrapData {
            digit_extract,
            slots_to_coeffs_thin: slots_to_coeffs,
            coeffs_to_slots_thin: coeffs_to_slots,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy
        };
    }

    pub fn build_odd<const LOG: bool>(&self) -> ThinBootstrapData<Params> {
        assert!(self.scheme_params.number_ring().n() % 2 != 0);

        let (p, r) = is_prime_power(&ZZ, &self.t).unwrap();
        let s_can_norm = self.scheme_params.number_ring().inf_to_can_norm_expansion_factor();
        let v = self.v;
        let e = r + v;
        if LOG {
            println!("Setting up bootstrapping for plaintext modulus p^r = {}^{} = {} within the cyclotomic ring Q[X]/(Phi_{})", p, r, self.t, self.scheme_params.number_ring().n());
            println!("Choosing e = r + v = {} + {}", r, v);
        }

        let plaintext_ring = self.scheme_params.create_plaintext_ring(ZZ.pow(p, e));
        let original_plaintext_ring = self.scheme_params.create_plaintext_ring(ZZ.pow(p, r));

        let digit_extract = if p == 2 && e <= 23 {
            DigitExtract::new_precomputed_p_is_2(p, e, r)
        } else {
            DigitExtract::new_default(p, e, r)
        };

        let hypercube = HypercubeStructure::halevi_shoup_hypercube(CyclotomicGaloisGroup::new(plaintext_ring.n() as u64), p);
        let H = HypercubeIsomorphism::new::<LOG>(&plaintext_ring, hypercube);
        let original_H = H.change_modulus(&original_plaintext_ring);
        let slots_to_coeffs = log_time::<_, _, LOG, _>("Creating Slots-to-Coeffs transform", |[]| MatmulTransform::to_circuit_many(composite::slots_to_powcoeffs_thin(&original_H), &original_H));
        let coeffs_to_slots = log_time::<_, _, LOG, _>("Creating Coeffs-to-Slots transform", |[]| MatmulTransform::to_circuit_many(composite::powcoeffs_to_slots_thin(&H), &H));
        let plaintext_ring_hierarchy = ((r + 1)..=e).map(|k| self.scheme_params.create_plaintext_ring(ZZ.pow(p, k))).collect();

        return ThinBootstrapData {
            digit_extract,
            slots_to_coeffs_thin: slots_to_coeffs,
            coeffs_to_slots_thin: coeffs_to_slots,
            plaintext_ring_hierarchy: plaintext_ring_hierarchy
        };
    }
}

impl<Params: BFVParams> ThinBootstrapData<Params> {

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

    pub fn bootstrap_thin<'a, const LOG: bool>(
        &self,
        C: &CiphertextRing<Params>, 
        Cmul: &CiphertextRing<Params>, 
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

        let values_in_coefficients = log_time::<_, _, LOG, _>("1. Computing Slots-to-Coeffs transform", |[key_switches]| {
            let result = self.slots_to_coeffs_thin.evaluate_bfv::<Params>(P_base, C, None, std::slice::from_ref(&ct), None, gk, key_switches);
            assert_eq!(1, result.len());
            return result.into_iter().next().unwrap();
        });
        if let Some(sk) = debug_sk {
            Params::dec_println(P_base, C, &values_in_coefficients, sk);
        }

        let noisy_decryption = log_time::<_, _, LOG, _>("2. Computing noisy decryption c0 + c1 * s", |[key_switches]| {
            let (c0, c1) = Params::mod_switch_to_plaintext(P_main, C, values_in_coefficients);
            let enc_sk = Params::enc_sk(P_main, C);
            *key_switches += 1;
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

        if LOG {
            println!("4. Performing digit extraction");
        }
        let rounding_divisor_half = P_main.base_ring().coerce(&ZZbig, ZZbig.rounded_div(ZZbig.pow(int_cast(self.p(), ZZbig, ZZ), self.v()), &ZZbig.int_hom().map(2)));
        let digit_extraction_input = Params::hom_add_plain(P_main, C, &P_main.inclusion().map(rounding_divisor_half), noisy_decryption_in_slots);
        let result = self.digit_extract.evaluate_bfv::<Params>(P_base, &self.plaintext_ring_hierarchy, C, Cmul, digit_extraction_input, rk).0;

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
    pub fn evaluate_bfv<'a, Params: BFVParams>(&self, 
        P_base: &PlaintextRing<Params>, 
        P: &[PlaintextRing<Params>], 
        C: &CiphertextRing<Params>, 
        Cmul: &CiphertextRing<Params>, 
        input: Ciphertext<Params>, 
        rk: &RelinKey<'a, Params>
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
        let mut key_switches = 0;
        let result = self.evaluate_generic(
            input,
            |exp, params, circuit| circuit.evaluate_bfv::<Params>(
                get_P(exp),
                C,
                Some(Cmul),
                params,
                Some(rk),
                &[],
                &mut key_switches
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
    let bootstrapper = bootstrap_params.build_pow2::<true>();
    
    let P = params.create_plaintext_ring(t);
    let (C, Cmul) = params.create_ciphertext_rings();
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| (g, Pow2BFV::gen_gk(&C, &mut rng, &sk, g, digits))).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, digits);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &Cmul, 
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
    let bootstrapper = bootstrap_params.build_pow2::<true>();
    
    let P = params.create_plaintext_ring(t);
    let (C, Cmul) = params.create_ciphertext_rings();
    
    let sk = Pow2BFV::gen_sk(&C, &mut rng);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| (g, Pow2BFV::gen_gk(&C, &mut rng, &sk, g, digits))).collect::<Vec<_>>();
    let rk = Pow2BFV::gen_rk(&C, &mut rng, &sk, digits);
    
    let m = P.int_hom().map(2);
    let ct = Pow2BFV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &Cmul, 
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
        n1: 31,
        n2: 11,
        ciphertext_allocator: DefaultCiphertextAllocator::default()
    };
    let t = 8;
    let digits = 3;
    let bootstrap_params = ThinBootstrapParams {
        scheme_params: params.clone(),
        v: 9,
        t: t
    };
    let bootstrapper = bootstrap_params.build_odd::<true>();
    
    let P = params.create_plaintext_ring(t);
    let (C, Cmul) = params.create_ciphertext_rings();
    
    let sk = CompositeBFV::gen_sk(&C, &mut rng);
    let gk = bootstrapper.required_galois_keys(&P).into_iter().map(|g| (g, CompositeBFV::gen_gk(&C, &mut rng, &sk, g, digits))).collect::<Vec<_>>();
    let rk = CompositeBFV::gen_rk(&C, &mut rng, &sk, digits);
    
    let m = P.int_hom().map(2);
    let ct = CompositeBFV::enc_sym(&P, &C, &mut rng, &m, &sk);
    let res_ct = bootstrapper.bootstrap_thin::<true>(
        &C, 
        &Cmul, 
        &P, 
        ct, 
        &rk, 
        &gk,
        None
    );

    assert_el_eq!(P, P.int_hom().map(2), CompositeBFV::dec(&P, &C, res_ct, &sk));
}
