use std::alloc::Global;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::ops::Deref;
use std::slice::from_ref;

use feanor_math::algorithms::convolution::rns::{RNSConvolution, RNSConvolutionZn};
use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::algorithms::interpolate::interpolate;
use feanor_math::algorithms::linsolve::LinSolveRingStore;
use feanor_math::algorithms::multipointeval::multipointeval;
use feanor_math::assert_el_eq;
use feanor_math::divisibility::{DivisibilityRing, DivisibilityRingStore};
use feanor_math::group::AbelianGroupStore;
use feanor_math::homomorphism::{CanHomFrom, Homomorphism};
use feanor_math::integer::*;
use feanor_math::matrix::OwnedMatrix;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::ring::*;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use feanor_math::rings::zn::*;
use feanor_math::seq::{VectorFn, VectorView};
use feanor_math::serialization::*;
use serde::Serialize;
use serde::de::DeserializeSeed;
use tracing::instrument;

use crate::cache::{SerializeDeserializeWith, SerializeSerializableWithData, StoreAs, create_cached};
use crate::circuit::*;
use crate::number_ring::galois::{CyclotomicGaloisGroup, CyclotomicGaloisGroupOps, GaloisGroupEl};
use crate::number_ring::hypercube::isomorphism::HypercubeIsomorphism;
use crate::number_ring::{NumberRingQuotient, NumberRingQuotientStore};
use crate::poly_eval::digit_extract::serialization::*;
use crate::poly_eval::special::precomputed_p_2;
use crate::poly_eval::to_circuit::{poly_to_circuit, poly_to_circuit_with_galois};
use crate::{NiceZn, ZZbig, ZZi64, filename_keys};

mod serialization;

/// Represents a digit extraction circuit, i.e. a [`PlaintextCircuit`] that, given `x in Z/p^kZ`
/// for some `k`, computes outputs `f(x)_j` that are congruent to the lowest p-ary digit `lift(x
/// cmod p)` modulo `p^(k_j)`, for various `k_j`.
pub struct DigitExtractionCircuit<R: ?Sized + RingBase = zn_big::ZnBase<BigIntRing>> {
    /// the circuit to perform the digit extraction; it should be defined over a ring that maps into
    /// the FHE scheme's plaintext space, have a single input and outputs corresponding to
    /// [`DigitExtractionCircuit::extracted_digit_mod_exp`].
    pub circuit: PlaintextCircuit<R>,
    /// the exponent `k` of the characteristic for which this digit extraction circuit should be
    /// used; concretely, a digit extraction circuit is given an input modulo `p^k`, and
    /// computes multiple values that are congruent to the lowest p-ary digit of the input
    /// modulo `p^i`, `1 <= i <= k`.
    pub global_mod_exp: usize,
    /// the exponents `k_j` modulo which the results are the lowest p-ary digit of the input.
    pub extracted_digit_mod_exp: Vec<usize>,
}

struct HelperCircuits<R: ?Sized + RingBase = zn_big::ZnBase<BigIntRing>> {
    /// the one-input, one-output identity circuit
    identity_circuit: PlaintextCircuit<R>,
    /// the two-input, one-output addition circuit
    add_circuit: PlaintextCircuit<R>,
    /// the two-input, one-output subtraction circuit
    sub_circuit: PlaintextCircuit<R>,
}

/// The digit extraction operation, as required during BFV and
/// BGV bootstrapping.
///
/// Concretely, this encapsulates an efficient implementation of the
/// per-slot digit extraction function
/// ```text
///   Z/p^eZ -> Z/p^rZ x Z/p^eZ,  x -> (x - (x cmod p^v) / p^v, x cmod p^v)
/// ```
/// for `v = e - r`. Here `x cmod p^v` refers to the smallest element of
/// `Z/p^eZ` that is congruent to `x` modulo `p^v`, i.e. the "centered modulo"
/// operation (in the case that `p = 2`, we define `2^(v - 1) cmod 2^v = -2^(v - 1)`).
///
/// [`DigitExtract`] is generic in the type of the rings to which the internal
/// constants belong to. Usually, these will be rings that embeds into the plaintext
/// space of the target FHE scheme for the respective intermediate plaintext moduli
/// `p^r, ..., p^e`; common examples would be the integers `Z`, the quotients `Z/p^kZ`
/// or the plaintext rings `R/p^rR, ..., R/p^eR` themselves.
///
/// [`DigitExtract`] is a dependent object, and does not keep track of the ring
/// it is defined over. Therefore, functions like [`DigitExtract::evaluate_plain()`]
/// require the sequence of rings `Z/p^rZ`, ..., `Z/p^eZ` as parameter.
///
/// Note that performing digit extraction via [`DigitExtract::evaluate_plain()`] or
/// [`DigitExtract::evaluate_generic()`] only makes sense when the input belongs to the
/// ring `Z/p^e`, or a ring isomorphic to many copies thereof. In many cases, the plaintext
/// space of an FHE scheme is strictly larger than that (e.g. isomorphic to a product
/// of Galois rings), in which case it is necessary that the input actually lives in a
/// suitable subring of the full plaintext space.
pub struct DigitExtract<R: ?Sized + RingBase = zn_big::ZnBase<BigIntRing>> {
    extraction_circuits: Vec<DigitExtractionCircuit<R>>,
    helper_circuits: HelperCircuits<R>,
    /// if `p = 2`, using centered digit retain polynomials does not automatically
    /// give a centered result; thus we need to add `2^(v - 1)` before digit extraction
    /// and subtract it afterwards
    center_circuits: Option<(PlaintextCircuit<R>, PlaintextCircuit<R>)>,
    v: usize,
    e: usize,
    p: El<BigIntRing>,
}

impl<R> DigitExtract<R>
where
    R: ?Sized + RingBase + NumberRingQuotient,
    <R::BaseRing as RingStore>::Type: NiceZn,
{
    /// Creates a [`DigitExtract`] for slot-wise digit extraction in the given ring.
    ///
    /// Uses internal heuristics to determine which polynomials and circuits to use.
    #[instrument(skip_all)]
    pub fn new_default<C, S>(rings: &[S], _hypercube_iso: &C, B: Option<i64>, cache_dir: Option<&str>) -> Self
    where
        C: Deref<Target = HypercubeIsomorphism<S>>,
        S: RingStore<Type = R>,
        R: SerializableElementRing,
    {
        let (p, r, v, e) = DigitExtract::get_p_r_v_e(rings.iter().map(RingExtensionStore::base_ring));
        for ring in rings {
            assert!(ring.number_ring() == ring.number_ring());
        }
        let Gal = rings[0].acting_galois_group();
        create_cached(
            (rings, Gal),
            || {
                let zn_rings = (0..=v).map(|i| rings[i].base_ring()).collect::<Vec<_>>();
                if ZZbig.eq_el(&p, &int_cast(2, ZZbig, ZZi64)) && e <= 23 {
                    DigitExtract::new_precomputed_p_is_2(&zn_rings).embed_plaintext_ring(rings)
                } else if v == 1 && B.is_some() && ZZbig.is_lt(&int_cast(B.unwrap() * 2, ZZbig, ZZi64), &p) {
                    DigitExtract::new_bounded_error(&zn_rings, B.unwrap()).embed_plaintext_ring(rings)
                } else {
                    DigitExtract::new_digit_retain_based(&zn_rings).embed_plaintext_ring(rings)
                }
            },
            &filename_keys![digit_extract, m: Gal.m(), o: Gal.group_order(), p: &p, e: e, r: r, B: B],
            cache_dir,
            StoreAs::AlwaysJson,
        )
    }

    /// Creates a [`DigitExtract`] for a scalar ring `Z/p^eZ`.
    ///
    /// Uses the Chen-Han digit retain polynomials <https://ia.cr/2018/067> together with
    /// a heuristic method to compile them into an arithmetic circuit, which considers
    /// Paterson-Stockmeyer-like methods as well as Galois-automorphism-based methods.
    ///
    /// **Warning**: Currently the Galois-based arithmetization is very slow. Improvements are
    /// planned.
    #[instrument(skip_all)]
    pub fn new_digit_retain_based_with_galois<S: RingStore<Type = R>>(
        rings: &[S],
        H: &HypercubeIsomorphism<S>,
        cost_model: &CircuitEvaluatorCosts,
    ) -> Self {
        let (p, r, v, _e) = DigitExtract::get_p_r_v_e(rings.iter().map(RingExtensionStore::base_ring));
        assert!(rings.last().unwrap().get_ring() == H.ring().get_ring());
        for ring in rings {
            assert!(ring.number_ring() == ring.number_ring());
        }

        let digit_extraction_circuits = (1..=v)
            .map(|i| {
                let required_digits = (2..=i).chain([r + i].into_iter()).collect::<Vec<_>>();
                let poly_ring = DensePolyRing::new(zn_big::Zn::new(ZZbig, ZZbig.pow(ZZbig.clone_el(&p), r + i)), "X");
                let current_H = H.change_modulus(&rings[i]);
                let circuit = poly_to_circuit_with_galois(
                    &current_H,
                    &poly_ring,
                    &required_digits
                        .iter()
                        .map(|j| centered_digit_retain_poly(&poly_ring, *j))
                        .collect::<Vec<_>>(),
                    cost_model,
                );
                return DigitExtractionCircuit {
                    circuit,
                    extracted_digit_mod_exp: required_digits,
                    global_mod_exp: r + i,
                };
            })
            .collect::<Vec<_>>();

        return Self::new_with_circuits(rings.last().unwrap(), p, r, v, digit_extraction_circuits);
    }

    /// Creates a [`DigitExtract`] for a scalar ring `Z/p^eZ`.
    ///
    /// Uses the Ma, Huang, Wang and Want digit extraction polynomials <https://ia.cr/2024/115>
    /// for errors bounded by `B` and large `p`, together with a heuristic method to compile them
    /// into an algebraic circuit, based on the Paterson-Stockmeyer method.
    ///
    /// **Warning**: Currently the Galois-based arithmetization is very slow. Improvements are
    /// planned.
    #[instrument(skip_all)]
    pub fn new_bounded_error_with_galois<S: RingStore<Type = R>>(
        rings: &[S],
        hypercube_iso: &HypercubeIsomorphism<S>,
        B: i64,
        cost_model: &CircuitEvaluatorCosts,
    ) -> Self {
        let (p, r, v, e) = DigitExtract::get_p_r_v_e(rings.iter().map(RingExtensionStore::base_ring));
        assert_eq!(1, v);
        assert!(rings.last().unwrap().get_ring() == hypercube_iso.ring().get_ring());
        for ring in rings {
            assert!(ring.number_ring() == ring.number_ring());
        }

        let poly_ring = DensePolyRing::new(zn_big::Zn::new(ZZbig, ZZbig.pow(ZZbig.clone_el(&p), e)), "X");
        let circuit = poly_to_circuit_with_galois(
            hypercube_iso,
            &poly_ring,
            &[bounded_digit_retain_poly(&poly_ring, B)],
            cost_model,
        );
        let digit_extraction_circuits = vec![DigitExtractionCircuit {
            extracted_digit_mod_exp: vec![e],
            global_mod_exp: e,
            circuit,
        }];

        return Self::new_with_circuits(rings.last().unwrap(), p, r, v, digit_extraction_circuits);
    }

    pub fn required_galois_keys(&self, galois_group: &Subgroup<CyclotomicGaloisGroup>) -> Vec<GaloisGroupEl> {
        let mut result = Vec::new();
        for circuit in &self.extraction_circuits {
            result.extend(circuit.circuit.required_galois_keys(galois_group))
        }
        result.sort_by_key(|g| galois_group.representative(g));
        result.dedup_by(|g, s| galois_group.eq_el(g, s));
        return result;
    }
}

impl<R: ?Sized + NiceZn> DigitExtract<R> {
    pub fn embed_plaintext_ring<S>(self, new_rings: &[S]) -> DigitExtract<S::Type>
    where
        S: RingStore,
        S::Type: RingExtension,
        <S::Type as RingExtension>::BaseRing: RingStore<Type = R>,
    {
        let r = self.r();
        self.change_ring_uniform(|i, x| match x {
            Coefficient::One => Coefficient::One,
            Coefficient::NegOne => Coefficient::NegOne,
            Coefficient::Zero => Coefficient::Zero,
            Coefficient::Integer(x) => Coefficient::Integer(x),
            Coefficient::Other(x) => Coefficient::from_int(int_cast(
                new_rings[i - r].base_ring().smallest_lift(x),
                ZZbig,
                new_rings[i - r].base_ring().integer_ring(),
            )),
        })
    }

    /// Creates a [`DigitExtract`] for a scalar ring `Z/2^eZ`.
    ///
    /// Uses the precomputed table of best digit extraction circuits for `e <= 23`.
    #[instrument(skip_all)]
    pub fn new_precomputed_p_is_2<S: RingStore<Type = R>>(rings: &[S]) -> Self {
        let (p, r, v, e) = Self::get_p_r_v_e(rings);
        assert_el_eq!(ZZbig, ZZbig.int_hom().map(2), p);
        assert!(e <= 23);

        let circuits = (1..=v)
            .map(|i| DigitExtractionCircuit {
                circuit: precomputed_p_2(&rings[i]),
                extracted_digit_mod_exp: [1, 2, 4, 8, 16, 23]
                    .into_iter()
                    .take_while(|j| *j < i + r)
                    .chain([i + r])
                    .collect(),
                global_mod_exp: i + r,
            })
            .collect::<Vec<_>>();
        return Self::new_with_circuits(rings.last().unwrap(), p, r, v, circuits);
    }

    /// Creates a [`DigitExtract`] for a scalar ring `Z/p^eZ`.
    ///
    /// Uses the Chen-Han digit retain polynomials <https://ia.cr/2018/067> together with
    /// a heuristic method to compile them into an arithmetic circuit, based on the
    /// Paterson-Stockmeyer method.
    #[instrument(skip_all)]
    pub fn new_digit_retain_based<S: RingStore<Type = R>>(rings: &[S]) -> Self {
        let (p, r, v, _e) = Self::get_p_r_v_e(rings);

        let digit_extraction_circuits = (1..=v)
            .map(|i| {
                let required_digits = (2..=i).chain([r + i].into_iter()).collect::<Vec<_>>();
                let poly_ring = DensePolyRing::new(&rings[i], "X");
                let circuit = poly_to_circuit(
                    &poly_ring,
                    &required_digits
                        .iter()
                        .map(|j| centered_digit_retain_poly(&poly_ring, *j))
                        .collect::<Vec<_>>(),
                );
                return DigitExtractionCircuit {
                    circuit,
                    extracted_digit_mod_exp: required_digits,
                    global_mod_exp: r + i,
                };
            })
            .collect::<Vec<_>>();

        return Self::new_with_circuits(rings.last().unwrap(), p, r, v, digit_extraction_circuits);
    }

    /// Creates a [`DigitExtract`] for a scalar ring `Z/p^eZ`.
    ///
    /// Uses the Ma, Huang, Wang and Want digit extraction polynomials <https://ia.cr/2024/115>
    /// for errors bounded by `B` and large `p`, together with a heuristic method to compile them
    /// into an algebraic circuit, based on the Paterson-Stockmeyer method.
    #[instrument(skip_all)]
    pub fn new_bounded_error<S: RingStore<Type = R>>(rings: &[S], B: i64) -> Self {
        let (p, r, v, e) = Self::get_p_r_v_e(rings);
        assert_eq!(1, v);

        let poly_ring = DensePolyRing::new(rings.last().unwrap(), "X");
        let circuit = poly_to_circuit(&poly_ring, &[bounded_digit_retain_poly(&poly_ring, B)]);
        let digit_extraction_circuits = vec![DigitExtractionCircuit {
            extracted_digit_mod_exp: vec![e],
            global_mod_exp: e,
            circuit,
        }];

        return Self::new_with_circuits(rings.last().unwrap(), p, r, v, digit_extraction_circuits);
    }

    fn get_p_r_v_e<I, S>(rings: I) -> (El<BigIntRing>, usize, usize, usize)
    where
        S: RingStore<Type = R>,
        I: IntoIterator<Item = S>,
    {
        let mut it = rings.into_iter();
        let first = it.next().unwrap();
        let ZZ = first.integer_ring();
        let (p, r) = is_prime_power(ZZ, first.modulus()).unwrap();
        let mut v = 0;
        for ring in it {
            assert!(ZZ.get_ring() == ring.integer_ring().get_ring());
            v += 1;
            assert_el_eq!(ZZ, ZZ.pow(ZZ.clone_el(&p), r + v), ring.modulus());
        }
        assert!(v >= 1);
        return (int_cast(p, ZZbig, ZZ), r, v, r + v);
    }

    pub fn evaluate_plain<S>(&self, input: El<S>, rings: &[S]) -> (El<S>, El<S>)
    where
        S: RingStore<Type = R>,
    {
        let (p, r, v, e) = Self::get_p_r_v_e(rings);
        assert_el_eq!(ZZbig, p, self.p());
        assert_eq!(r, self.r());
        assert_eq!(v, self.v());
        assert_eq!(e, self.e());

        let (quo, rem) = self.evaluate_generic(
            (self.e(), input),
            |exp, params, circuit| {
                assert!(params.iter().all(|(e, _)| *e == exp));
                let ring = &rings[exp - self.r()];
                let params = params.iter().map(|(_, x)| ring.clone_el(x)).collect::<Vec<_>>();
                let result = circuit.evaluate_no_galois(&params, ring.identity());
                return result.into_iter().map(|x| (exp, x)).collect();
            },
            |from, to, (e, x)| {
                assert_eq!(from, e);
                let from_ring = &rings[from - self.r()];
                let to_ring = &rings[to - self.r()];
                if from < to {
                    (
                        to,
                        to_ring.coerce(
                            &ZZbig,
                            ZZbig.mul(
                                int_cast(from_ring.smallest_lift(x), ZZbig, from_ring.integer_ring()),
                                ZZbig.pow(ZZbig.clone_el(self.p()), to - from),
                            ),
                        ),
                    )
                } else {
                    (
                        to,
                        to_ring.coerce(
                            &ZZbig,
                            ZZbig
                                .checked_div(
                                    &int_cast(from_ring.smallest_lift(x), ZZbig, from_ring.integer_ring()),
                                    &ZZbig.pow(ZZbig.clone_el(self.p()), from - to),
                                )
                                .unwrap(),
                        ),
                    )
                }
            },
        );
        assert_eq!(self.e(), rem.0);
        assert_eq!(self.r(), quo.0);
        return (quo.1, rem.1);
    }
}

impl<R: ?Sized + RingBase> DigitExtract<R> {
    /// Creates a new [`DigitExtract`] from the given circuits.
    ///
    /// If you want to use the default choice of circuits, consider using
    /// [`DigitExtract::new_default()`].
    ///
    /// This function takes parameters `p, r` and `v` and creates a [`DigitExtract`] modulo `p^e`
    /// for `e = r + v` as explained at the struct-level doc. Furthermore, it takes a ring that
    /// should embed into the plaintext ring of the FHE scheme for plaintext modulus `p^e`,
    /// which will be used to compute some auxiliary data. Finally, it will take a list of
    /// [`DigitExtractionCircuit`]s, one for every intermediate plaintext modulus `p^(r + i)`,
    /// `1 <= i <= v`. These circuits must, at the very least, support extraction of the lowest
    /// p-ary digit modulo `p^(r + i)`, but may additionally extract this digit modulo `p^k`, `k
    /// < r + i`, which can lead to reduced noise growth. Concretely, the `j`-th output of the
    /// `i`-th [`DigitExtractionCircuit`] should, on input `x` modulo `p^(r + i + 1)` compute `x
    /// cmod p` modulo `p^extracted_digit_mod_exp[j]`. Here `cmod` is the "centered modulo",
    /// i.e. should output an element in `{ - (p - 1)/2, ..., (p - 1)/2 }` that is congruent to the
    /// input (or `{0, 1}` if `p = 2`).
    pub fn new_with_circuits<S: RingStore<Type = R>>(
        ring_pe: S,
        p: El<BigIntRing>,
        r: usize,
        v: usize,
        extraction_circuits: Vec<DigitExtractionCircuit<R>>,
    ) -> Self {
        assert_eq!(v, extraction_circuits.len());
        for (i, circuit) in extraction_circuits.iter().enumerate() {
            assert_eq!(i + r + 1, circuit.global_mod_exp);
            assert!(circuit.extracted_digit_mod_exp.is_sorted());
            assert_eq!(circuit.extracted_digit_mod_exp.len(), circuit.circuit.output_count());
            assert_eq!(1, circuit.circuit.input_count());
            assert_eq!(i + r + 1, *circuit.extracted_digit_mod_exp.last().unwrap());
        }

        let center_circuits = if ZZbig.eq_el(&p, &int_cast(2, ZZbig, ZZi64)) {
            let shift = ZZbig.pow(ZZbig.clone_el(&p), v - 1);
            Some((
                PlaintextCircuit::add(&ring_pe).compose(
                    PlaintextCircuit::identity(1, &ring_pe).tensor(
                        PlaintextCircuit::constant_int(ZZbig.clone_el(&shift), &ring_pe),
                        &ring_pe,
                    ),
                    &ring_pe,
                ),
                PlaintextCircuit::sub(&ring_pe).compose(
                    PlaintextCircuit::identity(1, &ring_pe)
                        .tensor(PlaintextCircuit::constant_int(shift, &ring_pe), &ring_pe),
                    &ring_pe,
                ),
            ))
        } else {
            None
        };
        Self {
            extraction_circuits,
            helper_circuits: HelperCircuits {
                add_circuit: PlaintextCircuit::add(&ring_pe),
                identity_circuit: PlaintextCircuit::identity(1, &ring_pe),
                sub_circuit: PlaintextCircuit::sub(&ring_pe),
            },
            center_circuits,
            v,
            p,
            e: r + v,
        }
    }

    /// Returns `r`, i.e. the number of base-`p` digits in the final output.
    pub fn r(&self) -> usize { self.e - self.v }

    /// Returns `e`, i.e. the number of base-`p` digits in the input.
    pub fn e(&self) -> usize { self.e }

    /// Returns `v`, i.e. the number of base-`p` digits that are removed during digit extraction.
    pub fn v(&self) -> usize { self.v }

    pub fn p(&self) -> &El<BigIntRing> { &self.p }

    pub fn change_ring<S, F1, F2>(self, mut change_summand: F1, mut change_factor: F2) -> DigitExtract<S>
    where
        F1: FnMut(usize, Coefficient<R>) -> Coefficient<S>,
        F2: FnMut(usize, Coefficient<R>) -> Coefficient<S>,
        S: ?Sized + RingBase,
    {
        let mut map_circuit = |exp, circuit: PlaintextCircuit<R>| {
            circuit.change_ring(|x| change_summand(exp, x), |x| change_factor(exp, x))
        };
        DigitExtract {
            extraction_circuits: self
                .extraction_circuits
                .into_iter()
                .map(|circuit| DigitExtractionCircuit {
                    circuit: map_circuit(circuit.global_mod_exp, circuit.circuit),
                    extracted_digit_mod_exp: circuit.extracted_digit_mod_exp,
                    global_mod_exp: circuit.global_mod_exp,
                })
                .collect(),
            helper_circuits: HelperCircuits {
                add_circuit: map_circuit(self.e, self.helper_circuits.add_circuit),
                identity_circuit: map_circuit(self.e, self.helper_circuits.identity_circuit),
                sub_circuit: map_circuit(self.e, self.helper_circuits.sub_circuit),
            },
            center_circuits: self
                .center_circuits
                .map(|(pre, post)| (map_circuit(self.e, pre), map_circuit(self.e, post))),
            e: self.e,
            p: self.p,
            v: self.v,
        }
    }

    pub fn change_ring_uniform<S, F>(self, f: F) -> DigitExtract<S>
    where
        F: FnMut(usize, Coefficient<R>) -> Coefficient<S>,
        S: ?Sized + RingBase,
    {
        let f_refcell = RefCell::new(f);
        return self.change_ring(
            |p_exp, x| (f_refcell.borrow_mut())(p_exp, x),
            |p_exp, x| (f_refcell.borrow_mut())(p_exp, x),
        );
    }

    /// Evaluates the digit extraction function over any representation of elements of `Z/p^iZ`,
    /// which supports the evaluation of [`PlaintextCircuit`]s. Since digit extraction requires
    /// computations in all the rings `Z/p^(r - 1)Z, ...., Z/p^eZ`, we also require a
    /// `change_space` function, with the following properties:
    /// ```text
    ///   change_space(e, e', .): Z/p^eZ -> Z/p^e' Z
    ///   change_space(e, e', x mod p^e) = x p^(e' - e) mod p^e'      if e' > e
    ///   change_space(e, e', x mod p^e) = x / p^(e - e') mod p^e'    if e' < e and p^(e - e') | x
    /// ```
    /// If the passed functions behave as specified, `change_space(e, e', x)` will never be called
    /// for `e' < e` and an `x` which is not divisible by `p^(e - e')`.
    ///
    /// Furthermore, the `eval_circuit` is given the exponent of the current ring we work in as the
    /// first parameter. The result of [`DigitExtract::evaluate_generic()`] is then the tuple
    /// `(quo, rem)` with `quo` in `Z/p^rZ` and `rem` in `Z/p^eZ` such that `x = p^(e - r) * quo
    /// + rem` and `rem < p^(e - r)`.
    pub fn evaluate_generic<T, EvalCircuit, ChangeSpace>(
        &self,
        original_input: T,
        mut eval_circuit: EvalCircuit,
        mut change_space: ChangeSpace,
    ) -> (T, T)
    where
        EvalCircuit: FnMut(/* exponent of p */ usize, &[T], &PlaintextCircuit<R>) -> Vec<T>,
        ChangeSpace: FnMut(/* input exponent of p */ usize, /* output exponent of p */ usize, T) -> T,
    {
        let e = self.e;
        let r = self.e - self.v;

        fn tmp_in_array<T, U, F: FnMut(&[T; 2]) -> U>(fst: T, snd: &mut Option<T>, mut f: F) -> U {
            let array = [fst, snd.take().unwrap()];
            let result = f(&array);
            *snd = Some(array.into_iter().skip(1).next().unwrap());
            return result;
        }

        let clone_value = |modulus_exp: usize, value: &T, eval_circuit: &mut EvalCircuit| {
            eval_circuit(
                modulus_exp,
                std::slice::from_ref(value),
                &self.helper_circuits.identity_circuit,
            )
            .into_iter()
            .next()
            .unwrap()
        };
        let sub_values = |modulus_exp: usize, params: &[T; 2], eval_circuit: &mut EvalCircuit| {
            eval_circuit(modulus_exp, params, &self.helper_circuits.sub_circuit)
                .into_iter()
                .next()
                .unwrap()
        };
        let add_values = |modulus_exp: usize, params: &[T; 2], eval_circuit: &mut EvalCircuit| {
            eval_circuit(modulus_exp, params, &self.helper_circuits.add_circuit)
                .into_iter()
                .next()
                .unwrap()
        };

        let mut input = || {
            if let Some((pre, _post)) = &self.center_circuits {
                eval_circuit(e, from_ref(&original_input), pre)
                    .into_iter()
                    .next()
                    .unwrap()
            } else {
                clone_value(e, &original_input, &mut eval_circuit)
            }
        };

        let mut mod_result: Option<T> = None;
        let mut partial_floor_divs = (0..self.v).map(|_| Some(input())).collect::<Vec<_>>();
        for i in 0..self.v {
            let remaining_digits = e - i;
            let circuit = &self.extraction_circuits[self.v - i - 1];
            debug_assert_eq!(remaining_digits, circuit.global_mod_exp);
            debug_assert!(circuit.extracted_digit_mod_exp.is_sorted());

            let current = change_space(e, remaining_digits, partial_floor_divs[i].take().unwrap());
            let digit_extracted = eval_circuit(remaining_digits, std::slice::from_ref(&current), &circuit.circuit);
            let mut digit_extracted = digit_extracted
                .into_iter()
                .map(|value| Some(change_space(remaining_digits, e, value)))
                .collect::<Vec<_>>();

            let last_digit_extracted = digit_extracted.last_mut().unwrap();
            mod_result = Some(if let Some(mod_result) = mod_result {
                tmp_in_array(mod_result, last_digit_extracted, |params| {
                    add_values(e, &params, &mut eval_circuit)
                })
            } else {
                clone_value(e, last_digit_extracted.as_ref().unwrap(), &mut eval_circuit)
            });

            for j in (i + 1)..self.v {
                let digit_extracted_index = circuit
                    .extracted_digit_mod_exp
                    .iter()
                    .enumerate()
                    .filter(|(_, cleared_digits)| **cleared_digits > j - i)
                    .next()
                    .unwrap()
                    .0;
                take_mut::take(partial_floor_divs[j].as_mut().unwrap(), |current| {
                    tmp_in_array(current, &mut digit_extracted[digit_extracted_index], |params| {
                        sub_values(e, params, &mut eval_circuit)
                    })
                });
            }
        }

        let mut mod_result = if let Some((_pre, post)) = &self.center_circuits {
            Some(
                eval_circuit(e, &[mod_result.unwrap()], post)
                    .into_iter()
                    .next()
                    .unwrap(),
            )
        } else {
            Some(mod_result.unwrap())
        };
        let floor_div_result = tmp_in_array(original_input, &mut mod_result, |params| {
            change_space(e, r, sub_values(e, params, &mut eval_circuit))
        });

        return (floor_div_result, mod_result.unwrap());
    }
}

impl<'a, R> SerializeDeserializeWith<(&'a [R],)> for DigitExtract<R::Type>
where
    R: RingStore,
    R::Type: SerializableElementRing,
{
    fn deserialize_with_data<'de, D: serde::Deserializer<'de>>(
        data: (&'a [R],),
        deserializer: D,
    ) -> Result<Self, D::Error> {
        DeserializeSeedDigitExtract {
            galois_group: None,
            rings: data.0,
        }
        .deserialize(deserializer)
    }

    fn serialize_with_data<S: serde::Serializer>(&self, data: &(&'a [R],), serializer: S) -> Result<S::Ok, S::Error> {
        let datas = self
            .extraction_circuits
            .iter()
            .map(|circuit| (&data.0[circuit.global_mod_exp - self.r()],))
            .collect::<Vec<_>>();
        SerializableDigitExtract {
            e: self.e,
            v: self.v,
            p: SerializeWithRing::new(self.p(), ZZbig),
            ignore: PhantomData,
            extraction_circuits: self
                .extraction_circuits
                .iter()
                .zip(&datas)
                .map(|(circuit, data)| SerializableDigitExtractCircuit {
                    extracted_digit_mod_exp: &circuit.extracted_digit_mod_exp,
                    global_mod_exp: circuit.global_mod_exp,
                    ignore: PhantomData,
                    circuit: SerializeSerializableWithData::new(data, &circuit.circuit),
                })
                .collect(),
        }
        .serialize(serializer)
    }
}

impl<'a, R> SerializeDeserializeWith<(&'a [R], &'a Subgroup<CyclotomicGaloisGroup>)> for DigitExtract<R::Type>
where
    R: RingStore,
    R::Type: SerializableElementRing,
{
    fn deserialize_with_data<'de, D: serde::Deserializer<'de>>(
        data: (&'a [R], &'a Subgroup<CyclotomicGaloisGroup>),
        deserializer: D,
    ) -> Result<Self, D::Error> {
        DeserializeSeedDigitExtract {
            galois_group: Some(data.1),
            rings: data.0,
        }
        .deserialize(deserializer)
    }

    fn serialize_with_data<S: serde::Serializer>(
        &self,
        data: &(&'a [R], &'a Subgroup<CyclotomicGaloisGroup>),
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        let datas = self
            .extraction_circuits
            .iter()
            .map(|circuit| (&data.0[circuit.global_mod_exp - self.r()], data.1))
            .collect::<Vec<_>>();
        SerializableDigitExtract {
            e: self.e,
            v: self.v,
            p: SerializeWithRing::new(self.p(), ZZbig),
            ignore: PhantomData,
            extraction_circuits: self
                .extraction_circuits
                .iter()
                .zip(&datas)
                .map(|(circuit, data)| SerializableDigitExtractCircuit {
                    extracted_digit_mod_exp: &circuit.extracted_digit_mod_exp,
                    global_mod_exp: circuit.global_mod_exp,
                    ignore: PhantomData,
                    circuit: SerializeSerializableWithData::new(data, &circuit.circuit),
                })
                .collect(),
        }
        .serialize(serializer)
    }
}

/// Computes a low-degree polynomial `f` such that `f(x + py) = x` for
/// `x` in `{ -B, ..., B }` over `Z/p^eZ`.
#[instrument(skip_all)]
pub fn bounded_digit_retain_poly<P>(poly_ring: P, bound: i64) -> El<P>
where
    P: RingStore,
    P::Type: PolyRing,
    <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn,
{
    let base_ring = poly_ring.base_ring();
    let (p, e) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    assert!(
        base_ring
            .integer_ring()
            .is_lt(&int_cast(2 * bound, base_ring.integer_ring(), ZZi64), &p)
    );
    let hom = base_ring.can_hom(&ZZi64).unwrap();

    // poly that is zero modulo p on the support
    let base_null_poly =
        poly_ring.prod((-bound..=bound).map(|i| poly_ring.from_terms([(base_ring.one(), 1), (hom.map(i), 0)])));
    // poly that is zero modulo p^e on the support
    let null_polys = (0..=e)
        .scan(poly_ring.one(), |current, _| {
            let result = poly_ring.clone_el(current);
            poly_ring.mul_assign_ref(current, &base_null_poly);
            return Some(result);
        })
        .collect::<Vec<_>>();
    let null_poly = null_polys.last().unwrap();
    let modulus = (0..poly_ring.degree(null_poly).unwrap())
        .map(|i| base_ring.negate(base_ring.clone_el(poly_ring.coefficient_at(null_poly, i))))
        .collect::<Vec<_>>();
    let mod_null_poly_ring = FreeAlgebraImpl::new(base_ring, poly_ring.degree(&null_poly).unwrap(), modulus);
    // poly whose value is `= x mod p` and independent of `y` on `x + p y`
    let base_poly = mod_null_poly_ring.poly_repr(
        &poly_ring,
        &mod_null_poly_ring.pow_gen(
            mod_null_poly_ring.canonical_gen(),
            base_ring.modulus(),
            base_ring.integer_ring(),
        ),
        base_ring.identity(),
    );

    let len = 2 * bound as usize + 1;
    let x = (0..len).map_fn(|i| hom.map(i as i64 - bound));
    let mut matrix = OwnedMatrix::from_fn(len, len, |i, j| base_ring.pow(x.at(i), j));
    let mut expected = OwnedMatrix::from_fn(len, 1, |i, _| {
        base_ring.sub(x.at(i), poly_ring.evaluate(&base_poly, &x.at(i), base_ring.identity()))
    });
    let mut result = OwnedMatrix::zero(len, 1, base_ring);
    <_ as LinSolveRingStore>::solve_right(base_ring, matrix.data_mut(), expected.data_mut(), result.data_mut())
        .assert_solved();
    let digit_extraction_poly = poly_ring.add(
        base_poly,
        poly_ring.from_terms((0..len).map(|i| (base_ring.clone_el(result.at(i, 0)), i))),
    );
    let mut digit_retain_poly = mod_null_poly_ring.canonical_gen();
    for _ in 1..e {
        digit_retain_poly = poly_ring.evaluate(
            &digit_extraction_poly,
            &digit_retain_poly,
            mod_null_poly_ring.inclusion(),
        );
    }

    let digit_retain_poly = mod_null_poly_ring.poly_repr(&poly_ring, &digit_retain_poly, base_ring.identity());
    return reduce_mod_null_poly_lattice(
        &poly_ring,
        digit_retain_poly,
        &null_polys,
        &int_cast(p, ZZbig, base_ring.integer_ring()),
        e,
    );
}

/// Computes `min { n | n! % p^e == 0 }`
pub fn mu(p: i64, e: usize) -> El<BigIntRing> {
    let mut n = int_cast(p, ZZbig, ZZi64);
    let mut n_fac = int_cast(p, ZZbig, ZZi64);
    let divisor = ZZbig.pow(int_cast(p, ZZbig, ZZi64), e);
    while ZZbig.checked_div(&n_fac, &divisor).is_none() {
        ZZbig.add_assign(&mut n, int_cast(p, ZZbig, ZZi64));
        ZZbig.mul_assign_ref(&mut n_fac, &n);
    }
    return n;
}

/// Computes `prod_(i < m) (X - i)`.
pub fn falling_factorial_poly<P>(poly_ring: P, m: usize) -> El<P>
where
    P: RingStore,
    P::Type: PolyRing,
{
    poly_ring.prod((0..m).map(|j| poly_ring.sub(poly_ring.indeterminate(), poly_ring.int_hom().map(j as i32))))
}

#[instrument(skip_all)]
fn reduce_mod_null_poly_lattice<P>(
    poly_ring: P,
    poly: El<P>,
    null_polys: &[El<P>],
    p: &El<BigIntRing>,
    e: usize,
) -> El<P>
where
    P: RingStore,
    P::Type: PolyRing,
    <<P::Type as RingExtension>::BaseRing as RingStore>::Type: DivisibilityRing + CanHomFrom<BigIntRingBase>,
{
    let base_ring = poly_ring.base_ring();
    let hom = base_ring.can_hom(&ZZbig).unwrap();
    let mut current = poly;
    let mut current_e = 0;
    while current_e <= e
        && base_ring
            .checked_div(
                poly_ring.lc(&current).unwrap(),
                &base_ring.pow(hom.map_ref(p), current_e),
            )
            .is_some()
    {
        let null_poly = poly_ring
            .inclusion()
            .mul_ref_fst_map(&null_polys[e - current_e], base_ring.pow(hom.map_ref(p), current_e));
        while let Some(quo) = base_ring.checked_div(poly_ring.lc(&current).unwrap(), &poly_ring.lc(&null_poly).unwrap())
        {
            if poly_ring.degree(&current).unwrap() < poly_ring.degree(&null_poly).unwrap() {
                break;
            }
            let mut subtractor = poly_ring.inclusion().mul_ref_map(&null_poly, &quo);
            poly_ring.mul_assign_monomial(
                &mut subtractor,
                poly_ring.degree(&current).unwrap() - poly_ring.degree(&null_poly).unwrap(),
            );
            poly_ring.sub_assign(&mut current, subtractor);
        }
        current_e += 1;
    }
    return current;
}

/// Returns the lowest-degree polynomial `f` such that `f(x + p^i y) = x mod p^(i + 1)` for
/// `x in { -(p - 1)/2, ..., (p - 1)/2 }`, any `y` and `0 < i < e` (if `p = 2`, this is instead
/// the case for `x in { 0, 1 }`).
///
/// The degree of the polynomial is `p`.
#[instrument(skip_all)]
pub fn centered_digit_extract_poly<P>(poly_ring: P, e: usize) -> El<P>
where
    P: RingStore + Copy,
    P::Type: PolyRing,
    <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn,
{
    let base_ring = poly_ring.base_ring();
    let (p, e_max) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    assert!(e <= e_max);
    let p = int_cast(p, ZZi64, base_ring.integer_ring());

    let null_polys = (0..=e)
        .map(|i| falling_factorial_poly(poly_ring, int_cast(mu(p, i), ZZi64, ZZbig) as usize))
        .collect::<Vec<_>>();
    let Fp = zn_64::Zn::new(p as u64).as_field().unwrap();
    let convolution = RNSConvolutionZn::from(RNSConvolution::new(ZZi64.abs_log2_ceil(&(p as i64)).unwrap() + 1));
    let poly_ring_mod_p = DensePolyRing::new_with_convolution(Fp, "X", Global, convolution);
    let mod_p = poly_ring_mod_p.base_ring().can_hom(base_ring.integer_ring()).unwrap();
    let mut current = poly_ring.pow(poly_ring.indeterminate(), p as usize);
    for i in 1..=e {
        let pi = base_ring
            .integer_ring()
            .pow(int_cast(p, base_ring.integer_ring(), ZZi64), i);
        let x = ((-(p - 1) / 2)..=((p - 1) / 2))
            .map(|x| base_ring.coerce(&ZZi64, x))
            .collect::<Vec<_>>();
        let evaluations = multipointeval(&poly_ring, &current, &x);
        let x = ((-(p - 1) / 2)..=((p - 1) / 2))
            .map(|x| poly_ring_mod_p.base_ring().coerce(&ZZi64, x))
            .collect::<Vec<_>>();
        let y = ((-(p - 1) / 2)..=((p - 1) / 2))
            .zip(evaluations.into_iter())
            .map(|(x, y)| {
                mod_p.map(
                    base_ring
                        .integer_ring()
                        .checked_div(
                            &base_ring.smallest_lift(base_ring.sub(y, base_ring.coerce(&ZZi64, x))),
                            &pi,
                        )
                        .unwrap(),
                )
            })
            .collect::<Vec<_>>();
        let fix_poly = interpolate(&poly_ring_mod_p, x.copy_els(), y.copy_els(), Global).unwrap();
        let pi = base_ring.coerce(base_ring.integer_ring(), pi);
        poly_ring.get_ring().add_assign_from_terms(
            &mut current,
            poly_ring_mod_p.terms(&fix_poly).map(|(c, i)| {
                (
                    base_ring.mul_ref_snd(
                        base_ring.coerce(&ZZi64, -poly_ring_mod_p.base_ring().smallest_lift(*c)),
                        &pi,
                    ),
                    i,
                )
            }),
        );
        // invariant: `current = X^p + p * (...)` and `current(x + p^k y) = x mod p^(k + 1)` for all
        // `k <= i`
    }
    return reduce_mod_null_poly_lattice(poly_ring, current, &null_polys, &int_cast(p, ZZbig, ZZi64), e);
}

/// Returns the lowest-degree polynomial `f` such that `f(x + py) = x mod p^e` for
/// `x in { -(p - 1)/2, ..., (p - 1)/2 }` and any `y` (if `p = 2`, this is instead
/// the case for `x in { 0, 1 }`).
///
/// The degree of this polynomial is at most `(p - 1)(e - 1) + 1`, but may be smaller
/// than that. This function will always compute the polynomial of lowest degree with
/// above property. For the reason why a polynomial of degree `<= (p - 1)(e - 1) + 1`
/// with the property exists, see Chen and Han's paper <https://ia.cr/2022/1364>.
#[instrument(skip_all)]
pub fn centered_digit_retain_poly<P>(poly_ring: P, e: usize) -> El<P>
where
    P: RingStore + Copy,
    P::Type: PolyRing,
    <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn,
{
    assert!(e > 0);
    if e == 1 {
        return poly_ring.indeterminate();
    }
    let base_ring = poly_ring.base_ring();
    let (p, e_max) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    assert!(e <= e_max);
    let p = int_cast(p, ZZi64, base_ring.integer_ring());
    if p == 2 {
        // poly that is zero modulo p^e on the support
        let null_polys = (0..=e)
            .map(|i| falling_factorial_poly(poly_ring, int_cast(mu(p, i), ZZi64, ZZbig) as usize))
            .collect::<Vec<_>>();
        let null_poly = null_polys.last().unwrap();
        let modulus = (0..poly_ring.degree(null_poly).unwrap())
            .map(|i| base_ring.negate(base_ring.clone_el(poly_ring.coefficient_at(null_poly, i))))
            .collect::<Vec<_>>();
        let mod_null_poly_ring = FreeAlgebraImpl::new(base_ring, poly_ring.degree(&null_poly).unwrap(), modulus);

        let digit_retain_poly = mod_null_poly_ring.poly_repr(
            &poly_ring,
            &mod_null_poly_ring.pow(mod_null_poly_ring.canonical_gen(), 1 << e),
            base_ring.identity(),
        );
        return reduce_mod_null_poly_lattice(poly_ring, digit_retain_poly, &null_polys, &int_cast(2, ZZbig, ZZi64), e);
    } else if e == 2 {
        return centered_digit_extract_poly(poly_ring, e);
    } else {
        return bounded_digit_retain_poly(poly_ring, p.div_floor(2));
    }
}

/// Returns the lowest-degree polynomial `f` such that `f(x + py) = x mod p^e` for
/// `x in { 0, ..., p - 1 }` and any `y`.
///
/// The degree of this polynomial is at most `(p - 1)(e - 1) + 1`, but may be smaller
/// than that. This function will always compute the polynomial of lowest degree with
/// above property. For the reason why a polynomial of degree `<= (p - 1)(e - 1) + 1`
/// with the property exists, see Chen and Han's paper <https://ia.cr/2022/1364>.
#[instrument(skip_all)]
pub fn digit_retain_poly<P>(poly_ring: P, e: usize) -> El<P>
where
    P: RingStore + Copy,
    P::Type: PolyRing,
    <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn,
{
    assert!(e > 0);
    if e == 1 {
        return poly_ring.indeterminate();
    }
    let base_ring = poly_ring.base_ring();
    let (p, _) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    let p = int_cast(p, ZZi64, base_ring.integer_ring());
    let summand = if p == 2 {
        0
    } else {
        ZZi64.checked_div(&(p - 1), &2).unwrap()
    };
    let result = centered_digit_retain_poly(poly_ring, e);
    return poly_ring.add(
        poly_ring.evaluate(
            &result,
            &poly_ring.from_terms([(base_ring.one(), 1), (base_ring.coerce(&ZZi64, -summand), 0)]),
            poly_ring.inclusion(),
        ),
        poly_ring.inclusion().map(base_ring.coerce(&ZZi64, summand)),
    );
}

#[cfg(test)]
use feanor_math::rings::zn::zn_64::*;

#[cfg(test)]
use crate::number_ring::general_cyclotomic::OddSquarefreeCyclotomicNumberRing;
#[cfg(test)]
use crate::number_ring::hypercube::structure::HypercubeStructure;
#[cfg(test)]
use crate::number_ring::quotient_by_int::NumberRingQuotientByIntBase;

#[cfg(test)]
pub fn cmod(x: i64, y: i64) -> i64 { x - y * ZZi64.rounded_div(x, &y) }

#[cfg(test)]
pub fn high_part_mod(x: i64, y: i64, z: i64) -> i64 { cmod((x - cmod(x, y)) / y, z) }

#[test]
fn test_centered_digit_retain_poly() {
    feanor_tracing::DelayedLogger::init_test();
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 3);
    assert_eq!(Some(33), P.degree(&digit_retain));
    for k in 0..(17 * 17 * 17) {
        assert_el_eq!(
            &Zn,
            &Zn.coerce(&ZZi64, cmod(k, 17)),
            &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())
        );
    }

    let Zn = Zn::new(19 * 19 * 19);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 2);
    for k in 0..(19 * 19 * 19) {
        assert_eq!(
            cmod(k, 19),
            cmod(
                Zn.smallest_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())),
                19 * 19
            )
        );
    }
    assert_eq!(Some(19), P.degree(&digit_retain));

    let Zn = Zn::new(1024);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 3);
    assert_eq!(Some(3), P.degree(&digit_retain));
    for k in 0..1024 {
        assert_eq!(
            k % 2,
            Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 8
        );
    }
    let digit_retain = centered_digit_retain_poly(&P, 6);
    assert_eq!(Some(6), P.degree(&digit_retain));
    for k in 0..1024 {
        assert_eq!(
            k % 2,
            Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 64
        );
    }

    let Zn = Zn::new(257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 2);
    assert_eq!(Some(257), P.degree(&digit_retain));
    for k in 0..257 {
        assert_el_eq!(
            &Zn,
            &Zn.coerce(&ZZi64, 2),
            &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity())
        );
    }

    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = centered_digit_retain_poly(&P, 1);
    assert_el_eq!(&P, P.indeterminate(), digit_retain);
}

#[test]
fn test_centered_digit_extract_poly() {
    feanor_tracing::DelayedLogger::init_test();
    let cmod = |x, y| x - ZZi64.rounded_div(x, &y) * y;

    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = centered_digit_extract_poly(&P, 3);
    for k in 0..(17 * 17 * 17) {
        assert_eq!(
            cmod(k, 17),
            cmod(
                Zn.smallest_lift(P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, k), Zn.identity())),
                17 * 17
            )
        );
        assert_eq!(
            cmod(k, 17),
            Zn.smallest_lift(P.evaluate(
                &digit_extract,
                &P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, k), Zn.identity()),
                Zn.identity()
            ))
        );
    }
    assert_eq!(Some(17), P.degree(&digit_extract));

    let Zn = Zn::new(19 * 19 * 19);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = centered_digit_extract_poly(&P, 2);
    for k in 0..(19 * 19 * 19) {
        assert_eq!(
            cmod(k, 19),
            cmod(
                Zn.smallest_lift(P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, k), Zn.identity())),
                19 * 19
            )
        );
        assert_eq!(
            cmod(k, 19),
            Zn.smallest_lift(P.evaluate(
                &digit_extract,
                &P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, k), Zn.identity()),
                Zn.identity()
            ))
        );
    }
    assert_eq!(Some(19), P.degree(&digit_extract));

    let Zn = Zn::new(257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = centered_digit_extract_poly(&P, 2);
    for k in 0..257 {
        assert_el_eq!(
            &Zn,
            &Zn.coerce(&ZZi64, 2),
            &P.evaluate(&digit_extract, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity())
        );
    }
    assert_eq!(Some(257), P.degree(&digit_extract));

    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_extract = centered_digit_extract_poly(&P, 1);
    assert_el_eq!(&P, P.indeterminate(), digit_extract);
}

#[test]
fn test_digit_retain_poly_small() {
    feanor_tracing::DelayedLogger::init_test();
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    for k in 0..(17 * 17 * 17) {
        assert_el_eq!(
            &Zn,
            &Zn.coerce(&ZZi64, k % 17),
            &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())
        );
    }
    assert_eq!(Some(33), P.degree(&digit_retain));

    let Zn = Zn::new(1024);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    for k in 0..1024 {
        assert_eq!(
            k % 2,
            Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 8
        );
    }
    assert_eq!(Some(3), P.degree(&digit_retain));
    let digit_retain = digit_retain_poly(&P, 6);
    for k in 0..1024 {
        assert_eq!(
            k % 2,
            Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 64
        );
    }
    assert_eq!(Some(6), P.degree(&digit_retain));

    let Zn = Zn::new(257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 2);
    for k in 0..257 {
        assert_el_eq!(
            &Zn,
            &Zn.coerce(&ZZi64, 2),
            &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity())
        );
    }
    assert_eq!(Some(257), P.degree(&digit_retain));

    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 1);
    assert_el_eq!(&P, P.indeterminate(), digit_retain);
}

#[test]
fn test_bounded_digit_retain_poly() {
    feanor_tracing::DelayedLogger::init_test();
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = bounded_digit_retain_poly(&P, 3);
    for x in -3..=3 {
        for y in 0..(17 * 17) {
            assert_el_eq!(
                &Zn,
                &Zn.coerce(&ZZi64, x),
                &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, x + 17 * y), &Zn.identity())
            );
        }
    }
    assert_eq!(Some(17), P.degree(&digit_retain));

    let Zn = Zn::new(257 * 257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = bounded_digit_retain_poly(&P, 4);
    for x in -4..=4 {
        for y in 0..(257 * 257) {
            assert_el_eq!(
                &Zn,
                &Zn.coerce(&ZZi64, x),
                &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, x + 257 * y), &Zn.identity())
            );
        }
    }
    assert_eq!(Some(25), P.degree(&digit_retain));

    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = bounded_digit_retain_poly(&P, 3);
    assert_el_eq!(&P, P.indeterminate(), digit_retain);
}

#[test]
fn test_digit_retain_poly_large() {
    feanor_tracing::DelayedLogger::init_test();
    let Zn = Zn::new(257 * 257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    assert_el_eq!(
        &Zn,
        &Zn.coerce(&ZZi64, 251),
        &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 132092), &Zn.identity())
    );
    for k in 0..(257 * 257) {
        assert_el_eq!(
            &Zn,
            &Zn.coerce(&ZZi64, 2),
            &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity())
        );
    }
}

#[test]
fn test_digit_extract_precomputed_p_2() {
    feanor_tracing::DelayedLogger::init_test();
    for (r, v) in [(5, 7), (3, 2)] {
        let p = 2;
        let e = r + v;
        let rings = (0..=v)
            .map(|i| zn_big::Zn::new(ZZbig, ZZbig.pow(int_cast(p, ZZbig, ZZi64), i + r + 1)))
            .collect::<Vec<_>>();
        let digit_extract = DigitExtract::new_precomputed_p_is_2(&rings);
        for x in 0..ZZi64.pow(p, e) {
            let (actual_high, actual_low) =
                digit_extract.evaluate_plain(rings.last().unwrap().coerce(&ZZi64, x), &rings);
            assert_el_eq!(&rings[v], rings[v].coerce(&ZZi64, cmod(x, ZZi64.pow(p, v))), actual_low);
            assert_el_eq!(
                &rings[0],
                rings[0].coerce(&ZZi64, (x - cmod(x, ZZi64.pow(p, v))) / ZZi64.pow(p, v)),
                actual_high
            );
        }
    }
}

#[test]
fn test_digit_retain_based_right_digits() {
    feanor_tracing::DelayedLogger::init_test();
    let v = 5;
    let r = 3;
    let p = 2;
    let rings = (0..=v)
        .map(|i| zn_big::Zn::new(ZZbig, ZZbig.pow(int_cast(p, ZZbig, ZZi64), i + r)))
        .collect::<Vec<_>>();
    let extraction = DigitExtract::new_digit_retain_based(&rings);
    let mut circuits = extraction.extraction_circuits;
    circuits.sort_unstable_by_key(|circuit| circuit.global_mod_exp);
    assert_eq!(5, circuits.len());
    assert_eq!(4, circuits[0].global_mod_exp);
    assert_eq!(5, circuits[1].global_mod_exp);
    assert_eq!(6, circuits[2].global_mod_exp);
    assert_eq!(7, circuits[3].global_mod_exp);
    assert_eq!(8, circuits[4].global_mod_exp);
    assert_eq!(vec![4], circuits[0].extracted_digit_mod_exp);
    assert_eq!(vec![2, 5], circuits[1].extracted_digit_mod_exp);
    assert_eq!(vec![2, 3, 6], circuits[2].extracted_digit_mod_exp);
    assert_eq!(vec![2, 3, 4, 7], circuits[3].extracted_digit_mod_exp);
    assert_eq!(vec![2, 3, 4, 5, 8], circuits[4].extracted_digit_mod_exp);

    let plaintext_rings = rings
        .iter()
        .map(|ring| NumberRingQuotientByIntBase::new(OddSquarefreeCyclotomicNumberRing::new(3), ring))
        .collect::<Vec<_>>();
    let h = HypercubeStructure::halevi_shoup_hypercube(
        plaintext_rings.last().unwrap().acting_galois_group(),
        int_cast(p, ZZbig, ZZi64),
    );
    let H = HypercubeIsomorphism::new(plaintext_rings.last().unwrap(), &h, None);
    let plaintext_rings = plaintext_rings.iter().collect::<Vec<_>>();
    let extraction = DigitExtract::new_digit_retain_based_with_galois(&plaintext_rings, &H, &DEFAULT_EVALUATOR_COSTS);
    let mut circuits = extraction.extraction_circuits;
    circuits.sort_unstable_by_key(|circuit| circuit.global_mod_exp);
    assert_eq!(5, circuits.len());
    assert_eq!(4, circuits[0].global_mod_exp);
    assert_eq!(5, circuits[1].global_mod_exp);
    assert_eq!(6, circuits[2].global_mod_exp);
    assert_eq!(7, circuits[3].global_mod_exp);
    assert_eq!(8, circuits[4].global_mod_exp);
    assert_eq!(vec![4], circuits[0].extracted_digit_mod_exp);
    assert_eq!(vec![2, 5], circuits[1].extracted_digit_mod_exp);
    assert_eq!(vec![2, 3, 6], circuits[2].extracted_digit_mod_exp);
    assert_eq!(vec![2, 3, 4, 7], circuits[3].extracted_digit_mod_exp);
    assert_eq!(vec![2, 3, 4, 5, 8], circuits[4].extracted_digit_mod_exp);
}

#[test]
fn test_digit_retain_based() {
    feanor_tracing::DelayedLogger::init_test();
    for (p, r, v) in [
        (2, 3, 7),
        (2, 7, 4),
        (3, 2, 1),
        (3, 1, 2),
        (5, 2, 1),
        (5, 1, 2),
        (7, 1, 1),
    ] {
        let e = r + v;
        let rings = (0..=v)
            .map(|i| zn_big::Zn::new(ZZbig, ZZbig.pow(int_cast(p, ZZbig, ZZi64), i + r + 1)))
            .collect::<Vec<_>>();
        let digit_extract = DigitExtract::new_digit_retain_based(&rings);
        for x in 0..ZZi64.pow(p, e) {
            let (actual_high, actual_low) =
                digit_extract.evaluate_plain(rings.last().unwrap().coerce(&ZZi64, x), &rings);
            assert_el_eq!(&rings[v], rings[v].coerce(&ZZi64, cmod(x, ZZi64.pow(p, v))), actual_low);
            assert_el_eq!(
                &rings[0],
                rings[0].coerce(&ZZi64, (x - cmod(x, ZZi64.pow(p, v))) / ZZi64.pow(p, v)),
                actual_high
            );
        }
    }
}

#[test]
fn test_bounded_error() {
    feanor_tracing::DelayedLogger::init_test();
    let B = 4;
    for (p, r, v) in [(11, 2, 1), (17, 1, 1), (19, 1, 1)] {
        let rings = (0..=v)
            .map(|i| zn_big::Zn::new(ZZbig, ZZbig.pow(int_cast(p, ZZbig, ZZi64), i + r + 1)))
            .collect::<Vec<_>>();
        let digit_extract = DigitExtract::new_bounded_error(&rings, B);
        for x in 0..ZZi64.pow(p, r) {
            for error in -B..=B {
                let (actual_high, actual_low) =
                    digit_extract.evaluate_plain(rings.last().unwrap().coerce(&ZZi64, x * p + error), &rings);
                assert_el_eq!(&rings[v], rings[v].coerce(&ZZi64, error), actual_low);
                assert_el_eq!(&rings[0], rings[0].coerce(&ZZi64, x), actual_high);
            }
        }
    }
}
