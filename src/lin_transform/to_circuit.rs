use std::fmt::Debug;

use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::group::AbelianGroupStore;
use feanor_math::integer::int_cast;
use feanor_math::iters::multi_cartesian_product;
use feanor_math::ring::*;

use crate::circuit::*;
use crate::number_ring::galois::*;
use crate::number_ring::{NumberRingQuotient, NumberRingQuotientStore};
use crate::search::minimum_somewhat_continuous_function;
use crate::{ZZbig, ZZi64};

pub struct BSGSPlan<'a> {
    Gal: &'a Subgroup<CyclotomicGaloisGroup>,
    base_auto: GaloisGroupEl,
    /// the baby steps are `\prod_i τ_i^j_i x` for `j_i < n_i m_i`, where the list contains the
    /// tuples `(τ_i, n_i, m_i)`; we hoist m_i of them in every direction
    baby_step_dims: Vec<(GaloisGroupEl, usize, usize)>,
    /// the giant steps are `\prod_i τ_i^j_i x` for `j_i < n_i`, where the list contains the
    /// tuples `(τ_i, n_i)`
    giant_step_dims: Vec<(GaloisGroupEl, usize)>,
}

impl<'a> BSGSPlan<'a> {
    pub fn create(
        Gal: &'a Subgroup<CyclotomicGaloisGroup>,
        base_auto: GaloisGroupEl,
        baby_step_dims: Vec<(GaloisGroupEl, usize, usize)>,
        giant_step_dims: Vec<(GaloisGroupEl, usize)>,
    ) -> Self {
        for (step, n, m) in &baby_step_dims {
            assert!((*n == 1 && *m == 1) || !Gal.is_identity(step));
            assert!(*n == 1 || !Gal.is_identity(&Gal.pow(step, &int_cast(*m as i64, ZZbig, ZZi64))));
            assert!(*n >= 1 && *m >= 1);
        }
        for (step, len) in &giant_step_dims {
            assert!(*len == 1 || !Gal.is_identity(step));
            assert!(*len >= 1);
        }
        return Self {
            Gal,
            baby_step_dims,
            base_auto,
            giant_step_dims,
        };
    }

    /// Creates a [`BSGSPlan`] that covers the given grid of automorphisms. It uses a search and
    /// heuristics to obtain a plan with costs that are as low as we can find.
    /// 
    /// Note that in many scenarios, it it is not optimal.
    pub fn plan(
        Gal: &'a Subgroup<CyclotomicGaloisGroup>,
        grid: Vec<(GaloisGroupEl, GaloisGroupEl, usize)>,
        cost_model: &CircuitEvaluatorCosts,
        gk_key_limit: usize,
    ) -> Option<BSGSPlan<'a>> {
        fn plan_with_unhoisted_baby_step_count<'a>(
            Gal: &'a Subgroup<CyclotomicGaloisGroup>,
            base_auto: GaloisGroupEl,
            mut baby_step_dims: Vec<(GaloisGroupEl, usize)>,
            giant_step_dims: Vec<(GaloisGroupEl, usize)>,
            unhoisted_baby_step_count: usize,
            gk_key_limit: usize,
            _cost_model: &CircuitEvaluatorCosts
        ) -> Option<BSGSPlan<'a>> {
            baby_step_dims.sort_unstable_by_key(|(_, len)| *len);

            let baby_step_dims = baby_step_dims
                .into_iter()
                .rev()
                .scan(1, |current, (g, len)| {
                    if len * *current < unhoisted_baby_step_count + 1 {
                        *current *= len;
                        Some((g, len, 1))
                    } else if *current < unhoisted_baby_step_count + 1 {
                        let unhoisted_count = (unhoisted_baby_step_count + 1).div_ceil(*current);
                        *current *= unhoisted_count;
                        assert!(*current >= unhoisted_baby_step_count + 1);
                        let hoisted_count = len.div_ceil(unhoisted_count);
                        Some((g, unhoisted_count, hoisted_count))
                    } else {
                        Some((g, 1, len))
                    }
                })
                .collect::<Vec<_>>();

            let plan = BSGSPlan::create(Gal, base_auto, baby_step_dims, giant_step_dims);
            if plan.required_galois_keys().len() <= gk_key_limit {
                return Some(plan);
            } else {
                return None;
            }
        }

        fn plan_with_baby_step_count<'a>(
            Gal: &'a Subgroup<CyclotomicGaloisGroup>,
            base_auto: GaloisGroupEl,
            mut grid: Vec<(GaloisGroupEl, usize)>,
            approx_baby_step_count: usize,
            cost_model: &CircuitEvaluatorCosts,
            gk_key_limit: usize,
        ) -> Option<BSGSPlan<'a>> {
            let mut baby_step_dims = 0;
            let mut current_count = 1;
            for (_, len) in &grid {
                if len * current_count > approx_baby_step_count {
                    break;
                }
                baby_step_dims += 1;
                current_count *= len;
            }

            if current_count < approx_baby_step_count {
                let mixed_dim_baby_steps = approx_baby_step_count.div_ceil(current_count);
                assert!(current_count * mixed_dim_baby_steps >= approx_baby_step_count);
                let giant_step = Gal.pow(
                    &grid[baby_step_dims].0,
                    &int_cast(mixed_dim_baby_steps as i64, ZZbig, ZZi64),
                );
                let mixed_dim_giant_steps = grid[baby_step_dims].1.div_ceil(mixed_dim_baby_steps);
                grid[baby_step_dims].1 = mixed_dim_baby_steps;
                grid.push((giant_step, mixed_dim_giant_steps));
                baby_step_dims += 1;
            }

            let giant_steps = grid.drain(baby_step_dims..).collect::<Vec<_>>();
            let baby_steps = grid;
            let actual_baby_step_count = baby_steps.iter().map(|(_, len)| *len).product();

            let unhoisted_baby_step_count = minimum_somewhat_continuous_function(
                0..=actual_baby_step_count,
                |count| {
                    plan_with_unhoisted_baby_step_count(
                        Gal,
                        Gal.clone_el(&base_auto),
                        baby_steps.clone(),
                        giant_steps.clone(),
                        count,
                        gk_key_limit,
                        cost_model
                    )
                    .map(|plan| (plan.cost(cost_model) * 256.).floor() as i64)
                    .unwrap_or(i64::MAX)
                },
                4,
            );
            plan_with_unhoisted_baby_step_count(
                Gal,
                base_auto,
                baby_steps.clone(),
                giant_steps.clone(),
                unhoisted_baby_step_count,
                gk_key_limit,
                cost_model
            )
        }

        let mut base_auto = Gal.identity();
        let mut grid = grid
            .into_iter()
            .map(|(start, step, len)| {
                base_auto = Gal.op_ref_snd(start, &base_auto);
                (step, len)
            })
            .collect::<Vec<_>>();

        // long dimensions are better put into the giant steps; the reason is that for multiple short
        // dimensions, we need a lot of Galois keys, whether we evaluate them hoisted or unhoisted; on the
        // other hand, the evaluations along a single long dimension can be done with a single Galois when
        // evaluating it a sequential, unhoisted manner
        grid.sort_unstable_by_key(|(_, len)| *len);

        let total_count = grid.iter().map(|(_, len)| *len).product();
        let baby_step_count = minimum_somewhat_continuous_function(
            0..=total_count,
            |baby_step_count| {
                plan_with_baby_step_count(
                    Gal,
                    Gal.clone_el(&base_auto),
                    grid.clone(),
                    baby_step_count,
                    cost_model,
                    gk_key_limit,
                )
                .map(|plan| (plan.cost(cost_model) * 256.).floor() as i64)
                .unwrap_or(i64::MAX)
            },
            4,
        );

        return plan_with_baby_step_count(
            Gal,
            Gal.clone_el(&base_auto),
            grid.clone(),
            baby_step_count,
            cost_model,
            gk_key_limit,
        );
    }

    /// Number of wires to which the hoisted Galois gate is applied, i.e. `\prod_i n_i`
    fn hoisting_input_count(&self) -> usize { self.baby_step_dims.iter().map(|(_, n, _)| *n).product() }

    /// Number of non-identity automorphisms in each hoisted Galois gate; as in
    /// [`PlaintextCircuit::gal_many()`], duplicates are counted, identities are not
    fn hoisted_gal_len(&self) -> usize {
        gal_iter(
            self.Gal,
            &self.base_auto,
            self.baby_step_dims
                .iter()
                .map(|(step, _, m)| (self.Gal.clone_el(step), *m)),
        )
        .filter(|g| !self.Gal.is_identity(g))
        .count()
    }

    /// Returns the number of hoisted Galois automorphisms in the circuit returned by
    /// [`BSGSPlan::create_circuit()`], consistent with [`PlaintextCircuit::cost()`].
    pub fn hoisted_automorphism_count(&self) -> usize {
        let hoisted_len = self.hoisted_gal_len();
        if hoisted_len >= 2 {
            self.hoisting_input_count() * hoisted_len
        } else {
            0
        }
    }

    /// Returns the number of hoisting setups in the circuit returned by
    /// [`BSGSPlan::create_circuit()`], consistent with [`PlaintextCircuit::cost()`].
    pub fn hoisting_setup_count(&self) -> usize {
        if self.hoisted_gal_len() >= 2 {
            self.hoisting_input_count()
        } else {
            0
        }
    }

    /// Returns the number of non-hoisted Galois automorphisms in the circuit returned by
    /// [`BSGSPlan::create_circuit()`], consistent with [`PlaintextCircuit::cost()`].
    pub fn unhoisted_automorphism_count(&self) -> usize {
        let degenerate_hoisted = if self.hoisted_gal_len() == 1 {
            self.hoisting_input_count()
        } else {
            0
        };
        let baby_steps = self.hoisting_input_count() - 1;
        let giant_steps = self.giant_step_dims.iter().map(|(_, len)| *len).product::<usize>() - 1;
        return degenerate_hoisted + baby_steps + giant_steps;
    }

    pub fn cost(&self, cost_model: &CircuitEvaluatorCosts) -> f64 {
        self.hoisting_setup_count() as f64 * cost_model.cost_setup_hoisted_gal
            + self.hoisted_automorphism_count() as f64 * cost_model.cost_hoisted_gal
            + self.unhoisted_automorphism_count() as f64 * cost_model.cost_single_gal
    }

    /// Returns the Galois automorphisms for which the circuit returned by
    /// [`BSGSPlan::create_circuit()`] requires a key-switching key, in the same order as
    /// [`PlaintextCircuit::required_galois_keys()`].
    pub fn required_galois_keys(&self) -> Vec<GaloisGroupEl> {
        let iterated_baby_steps = self
            .baby_step_dims
            .iter()
            .filter(|(_, n, _)| *n > 1)
            .map(|(step, _, m)| self.Gal.pow(step, &int_cast(*m as i64, ZZbig, ZZi64)));
        let giant_steps = self
            .giant_step_dims
            .iter()
            .filter(|(_, len)| *len > 1)
            .map(|(step, _)| self.Gal.clone_el(step));
        let hoisted_baby_steps = gal_iter(
            self.Gal,
            &self.base_auto,
            self.baby_step_dims
                .iter()
                .map(|(step, _, m)| (self.Gal.clone_el(step), *m)),
        );
        let mut result = iterated_baby_steps
            .chain(giant_steps)
            .chain(hoisted_baby_steps)
            .filter(|g| !self.Gal.is_identity(g))
            .collect::<Vec<_>>();
        result.sort_unstable_by_key(|g| self.Gal.representative(g));
        result.dedup_by_key(|g| self.Gal.representative(g));
        return result;
    }

    /// Returns the circuit that computes all baby steps;
    ///
    /// The output wires are `σ \prod_i τ_i^{j_i * m_i + l_i}`, where
    /// `(j_1, ..., j_r, l_1, ..., l_r)` runs lexicographically through
    /// ```text
    ///   {0, ..., n_1 - 1} x ... x {0, ..., n_r - 1} x {0, ..., m_1 - 1} x ... x {0, ...., m_r - 1}
    /// ```
    /// This is the same order as returned by [`BSGSPlan::baby_step_conjugates()`].
    fn baby_step_circuit<S: RingStore + Copy>(&self, ring: S) -> PlaintextCircuit<S::Type> {
        let mut unhoisted_circuit = PlaintextCircuit::identity(1, ring);
        for (step, n, m) in &self.baby_step_dims {
            let step_m = self.Gal.pow(step, &int_cast(*m as i64, ZZbig, ZZi64));
            // iterate the circuit
            //  ||   |
            //  ||   |‾‾‾|
            //  ||   |  [g]
            //  ||   |   |
            let expand_dim = (1..*n).fold(PlaintextCircuit::identity(1, ring), |current, _| {
                PlaintextCircuit::identity(current.output_count() - 1, ring)
                    .tensor(
                        PlaintextCircuit::identity(1, ring)
                            .tensor(PlaintextCircuit::gal(self.Gal.clone_el(&step_m), self.Gal, ring), ring)
                            .compose(PlaintextCircuit::identity(1, ring).output_twice(ring), ring),
                        ring,
                    )
                    .compose(current, ring)
            });
            let expand_all_dim = (0..unhoisted_circuit.output_count()).fold(PlaintextCircuit::empty(), |current, _| {
                current.tensor(expand_dim.clone(ring), ring)
            });
            unhoisted_circuit = expand_all_dim.compose(unhoisted_circuit, ring);
        }

        let hoisted_gs = gal_iter(
            self.Gal,
            &self.base_auto,
            self.baby_step_dims
                .iter()
                .map(|(step, _, m)| (self.Gal.clone_el(step), *m)),
        )
        .collect::<Vec<_>>();
        let hoisted_circuit = PlaintextCircuit::gal_many(&hoisted_gs, self.Gal, ring);

        return (0..unhoisted_circuit.output_count())
            .fold(PlaintextCircuit::empty(), |current, _| {
                current.tensor(hoisted_circuit.clone(ring), ring)
            })
            .compose(unhoisted_circuit, ring);
    }

    fn baby_step_conjugates(&self) -> Vec<GaloisGroupEl> {
        let iterables = self
            .baby_step_dims
            .iter()
            .map(|(step, n, m)| {
                (0..*n)
                    .map(|j| self.Gal.pow(step, &int_cast((j * m) as i64, ZZbig, ZZi64)))
                    .collect::<Vec<_>>()
            })
            .chain(self.baby_step_dims.iter().map(|(step, _, m)| {
                (0..*m)
                    .map(|l| self.Gal.pow(step, &int_cast(l as i64, ZZbig, ZZi64)))
                    .collect::<Vec<_>>()
            }))
            .collect::<Vec<_>>();
        multi_cartesian_product(
            iterables.iter().map(|vec| vec.iter()),
            |slice| {
                slice.iter().fold(self.Gal.clone_el(&self.base_auto), |current, g| {
                    self.Gal.op_ref_snd(current, g)
                })
            },
            |_, g| *g,
        )
        .collect::<Vec<_>>()
    }

    pub fn create_circuit<S>(&self, ring: S, mut coefficients: Vec<(GaloisGroupEl, El<S>)>) -> PlaintextCircuit<S::Type>
    where
        S: RingStore + Copy,
        S::Type: NumberRingQuotient,
    {
        let bs_circuit = self.baby_step_circuit(ring);
        let bs_conjugates = self.baby_step_conjugates();

        let constants: Vec<Vec<Coefficient<S::Type>>> = gal_iter(
            self.Gal,
            &self.Gal.identity(),
            self.giant_step_dims
                .iter()
                .map(|(step, len)| (self.Gal.clone_el(step), *len)),
        )
        .map(|g| {
            bs_conjugates
                .iter()
                .map(|h| {
                    let current = self.Gal.op_ref(&g, h);
                    if let Some(idx) = coefficients.iter().position(|(g, _)| self.Gal.eq_el(&current, g)) {
                        let coeff = coefficients.swap_remove(idx).1;
                        Coefficient::from(ring.apply_galois_action(&coeff, &self.Gal.inv(&g)), ring)
                    } else {
                        Coefficient::Zero
                    }
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
        let len = constants.len();
        assert!(
            coefficients.len() == 0,
            "support of the transform must be contained in the product of baby- and giant steps, but {} isn't",
            self.Gal
                .parent()
                .underlying_ring()
                .format(self.Gal.parent().as_ring_el(&coefficients[0].0))
        );

        let mut circuit = constants
            .into_iter()
            .map(|list| PlaintextCircuit::linear_transform(&list, ring))
            .fold(PlaintextCircuit::empty(), |current, next| current.tensor(next, ring))
            .compose(bs_circuit.output_times(len, ring), ring);

        for (step, len) in self.giant_step_dims.iter().rev() {
            // iterate the circuit
            //   |   |
            //   |  [g]
            //   |___|
            //     +
            //     |
            let compress_circuit = (1..*len).fold(PlaintextCircuit::identity(1, ring), |current, _| {
                PlaintextCircuit::add(ring).compose(
                    PlaintextCircuit::identity(1, ring).tensor(
                        PlaintextCircuit::gal(self.Gal.clone_el(step), self.Gal, ring).compose(current, ring),
                        ring,
                    ),
                    ring,
                )
            });
            let repeat = circuit.output_count() / len;
            debug_assert_eq!(circuit.output_count(), len * repeat);
            circuit = (0..repeat)
                .fold(PlaintextCircuit::empty(), |current, _| {
                    current.tensor(compress_circuit.clone(ring), ring)
                })
                .compose(circuit, ring);
        }

        debug_assert_eq!(self.hoisted_automorphism_count(), circuit.hoisted_automorphism_count());
        debug_assert_eq!(self.hoisting_setup_count(), circuit.hoisting_setup_count());
        debug_assert_eq!(
            self.unhoisted_automorphism_count(),
            circuit.unhoisted_automorphism_count()
        );
        debug_assert_eq!(
            self.required_galois_keys().len(),
            circuit.required_galois_keys(self.Gal).len()
        );
        return circuit;
    }
}

impl<'a> Debug for BSGSPlan<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BSGSPlan {{ baby_step_dims: [")?;
        for (i, (base, n, m)) in self.baby_step_dims.iter().enumerate() {
            if i == 0 {
                write!(f, "({}, {}, {})", self.Gal.representative(base), n, m)?;
            } else {
                write!(f, ", ({}, {}, {})", self.Gal.representative(base), n, m)?;
            }
        }
        write!(f, "], giant_step_dims: [")?;
        for (i, (base, len)) in self.giant_step_dims.iter().enumerate() {
            if i == 0 {
                write!(f, "({}, {})", self.Gal.representative(base), len)?;
            } else {
                write!(f, ", ({}, {})", self.Gal.representative(base), len)?;
            }
        }
        write!(
            f,
            "], base_auto: {}, hoisted_automorphism_count: {}, unhoisted_automorphism_count: {}, hoisting_setup_count: {}, key_count: {} }}",
            self.Gal.representative(&self.base_auto),
            self.hoisted_automorphism_count(),
            self.unhoisted_automorphism_count(),
            self.hoisting_setup_count(),
            self.required_galois_keys().len()
        )?;
        return Ok(());
    }
}

fn gal_iter<'a, I: IntoIterator<Item = (GaloisGroupEl, usize)>>(
    Gal: &'a Subgroup<CyclotomicGaloisGroup>,
    base_auto: &'a GaloisGroupEl,
    dims: I,
) -> impl use<'a, I> + Clone + Iterator<Item = GaloisGroupEl> {
    multi_cartesian_product(
        dims.into_iter().map(|(step, len)| {
            (0..len).scan(Gal.identity(), move |current, _| {
                let result = Gal.clone_el(current);
                *current = Gal.op_ref(current, &step);
                return Some(result);
            })
        }),
        |slice| slice.iter().fold(Gal.clone_el(base_auto), |x, y| Gal.op_ref_snd(x, y)),
        |_, x| Gal.clone_el(x),
    )
}

#[cfg(test)]
use feanor_math::algorithms::matmul::ComputeInnerProduct;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::homomorphism::Homomorphism;
#[cfg(test)]
use feanor_math::rings::extension::FreeAlgebraStore;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;

#[cfg(test)]
use crate::circuit::evaluator::CircuitEvaluator;
#[cfg(test)]
use crate::number_ring::quotient_by_int::*;
#[cfg(test)]
use crate::number_ring::tensor_ring::TensorProductNumberRing;

#[test]
fn test_baby_step_circuit() {
    struct GalEvaluator<'a>(&'a Subgroup<CyclotomicGaloisGroup>);

    impl<'a, 'b, R: RingBase + ?Sized> CircuitEvaluator<'b, GaloisGroupEl, R> for GalEvaluator<'a> {
        fn add_constant(&mut self, _: GaloisGroupEl, _: &'b Coefficient<R>) -> GaloisGroupEl { unreachable!() }
        fn mul(&mut self, _: GaloisGroupEl, _: GaloisGroupEl) -> GaloisGroupEl { unreachable!() }
        fn square(&mut self, _: GaloisGroupEl) -> GaloisGroupEl { unreachable!() }
        fn supports_gal(&self) -> bool { true }
        fn supports_mul(&self) -> bool { false }

        fn inner_prod<'c, I>(&mut self, data: I) -> GaloisGroupEl
        where
            I: Iterator<Item = (&'b Coefficient<R>, &'c GaloisGroupEl)>,
            R: 'b,
        {
            data.filter_map(|(coeff, val)| match coeff {
                Coefficient::One => Some(val),
                Coefficient::Zero => None,
                _ => unreachable!(),
            })
            .reduce(|_, _| unreachable!())
            .unwrap()
            .clone()
        }

        fn gal(&mut self, val: GaloisGroupEl, gs: &'b [GaloisGroupEl]) -> Vec<GaloisGroupEl> {
            gs.iter().map(|g| self.0.op_ref(&val, g)).collect::<Vec<_>>()
        }
    }

    let Gal = CyclotomicGaloisGroupBase::new(5 * 7).into().full_subgroup();
    let plan = BSGSPlan {
        Gal: &Gal,
        base_auto: Gal.identity(),
        baby_step_dims: vec![(Gal.from_representative(22), 2, 2), (Gal.from_representative(31), 3, 2)],
        giant_step_dims: Vec::new(),
    };
    let circuit = plan.baby_step_circuit(ZZi64);
    let results = circuit.evaluate_generic(&[Gal.identity()], GalEvaluator(&Gal));
    let expected = plan.baby_step_conjugates();
    assert_eq!(expected.len(), results.len());
    for (expected, actual) in expected.iter().zip(&results) {
        assert!(Gal.eq_el(expected, actual));
    }
    assert_eq!(18, plan.hoisted_automorphism_count());
    assert_eq!(6, plan.hoisting_setup_count());
    assert_eq!(5, plan.unhoisted_automorphism_count());
    assert_eq!(plan.hoisted_automorphism_count(), circuit.hoisted_automorphism_count());
    assert_eq!(plan.hoisting_setup_count(), circuit.hoisting_setup_count());
    assert_eq!(
        plan.unhoisted_automorphism_count(),
        circuit.unhoisted_automorphism_count()
    );
}

#[test]
fn test_create_circuit() {
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5, 7), Zn::new(65537));
    let Gal = ring.acting_galois_group();
    let plan = BSGSPlan {
        Gal,
        base_auto: Gal.identity(),
        baby_step_dims: vec![(Gal.from_representative(22), 1, 2), (Gal.from_representative(31), 3, 2)],
        giant_step_dims: vec![(Gal.from_representative(29), 2)],
    };
    let coefficients = || {
        vec![
            (Gal.from_representative(1), ring.int_hom().map(1)),
            (Gal.from_representative(2), ring.int_hom().map(2)),
            (Gal.from_representative(3), ring.int_hom().map(4)),
            (Gal.from_representative(9), ring.int_hom().map(8)),
            (Gal.from_representative(11), ring.int_hom().map(16)),
            (Gal.from_representative(12), ring.int_hom().map(32)),
            (Gal.from_representative(22), ring.int_hom().map(64)),
            (Gal.from_representative(32), ring.int_hom().map(128)),
        ]
    };
    let circuit = plan.create_circuit(&ring, coefficients());
    let coefficients = coefficients();
    for x in [
        ring.one(),
        ring.canonical_gen(),
        ring.pow(ring.canonical_gen(), 2),
        ring.sub(ring.canonical_gen(), ring.one()),
    ] {
        let expected = ComputeInnerProduct::inner_product_ref_fst(
            ring.get_ring(),
            coefficients
                .iter()
                .map(|(g, coeff)| (coeff, ring.apply_galois_action(&x, g))),
        );
        assert_el_eq!(&ring, expected, &circuit.evaluate(&[x], ring.identity())[0]);
    }
    assert_eq!(plan.hoisted_automorphism_count(), circuit.hoisted_automorphism_count());
    assert_eq!(plan.hoisting_setup_count(), circuit.hoisting_setup_count());
    assert_eq!(
        plan.unhoisted_automorphism_count(),
        circuit.unhoisted_automorphism_count()
    );

    let plan = BSGSPlan {
        Gal,
        base_auto: Gal.identity(),
        baby_step_dims: vec![],
        giant_step_dims: vec![(Gal.from_representative(29), 2)],
    };
    let coefficients = || {
        vec![
            (Gal.from_representative(1), ring.int_hom().map(1)),
            (Gal.from_representative(29), ring.int_hom().map(2)),
        ]
    };
    let circuit = plan.create_circuit(&ring, coefficients());
    let coefficients = coefficients();
    for x in [
        ring.one(),
        ring.canonical_gen(),
        ring.pow(ring.canonical_gen(), 2),
        ring.sub(ring.canonical_gen(), ring.one()),
    ] {
        let expected = ComputeInnerProduct::inner_product_ref_fst(
            ring.get_ring(),
            coefficients
                .iter()
                .map(|(g, coeff)| (coeff, ring.apply_galois_action(&x, g))),
        );
        assert_el_eq!(&ring, expected, &circuit.evaluate(&[x], ring.identity())[0]);
    }
    assert_eq!(plan.hoisted_automorphism_count(), circuit.hoisted_automorphism_count());
    assert_eq!(plan.hoisting_setup_count(), circuit.hoisting_setup_count());
    assert_eq!(
        plan.unhoisted_automorphism_count(),
        circuit.unhoisted_automorphism_count()
    );
}

#[test]
fn test_plan() {
    let ring = NumberRingQuotientByIntBase::new(TensorProductNumberRing::new(5 * 7, 13), Zn::new(65537));
    let Gal = ring.acting_galois_group();
    let grid = vec![
        (Gal.from_representative(183), Gal.from_representative(92), 3), // { g_2^-1, 1, g_2 }
        (Gal.from_representative(131), Gal.from_representative(66), 4), // { g_3^-1, 1, g_3, g_3^2 }
        (Gal.from_representative(106), Gal.from_representative(106), 4), // { g_13^1, g_13^2, g_13^3, g_13^4 }
    ];

    let plan = BSGSPlan::plan(&Gal, grid.clone(), &DEFAULT_EVALUATOR_COSTS, 4).unwrap();
    _ = plan.create_circuit(&ring, Vec::new());
    assert_eq!(4, plan.required_galois_keys().len());
    assert_eq!(20, plan.unhoisted_automorphism_count());
    assert_eq!(0, plan.hoisting_setup_count());
    assert_eq!(0, plan.hoisted_automorphism_count());

    let plan = BSGSPlan::plan(&Gal, grid.clone(), &DEFAULT_EVALUATOR_COSTS, usize::MAX).unwrap();
    _ = plan.create_circuit(&ring, Vec::new());
    assert_eq!(12, plan.required_galois_keys().len());
    assert_eq!(3, plan.unhoisted_automorphism_count());
    assert_eq!(1, plan.hoisting_setup_count());
    assert_eq!(12, plan.hoisted_automorphism_count());

    let plan = BSGSPlan::plan(&Gal, grid.clone(), &DEFAULT_EVALUATOR_COSTS, 6).unwrap();
    _ = plan.create_circuit(&ring, Vec::new());
    assert_eq!(6, plan.required_galois_keys().len());
    assert_eq!(8, plan.unhoisted_automorphism_count());
    assert_eq!(2, plan.hoisting_setup_count());
    assert_eq!(8, plan.hoisted_automorphism_count());

    let grid = vec![
        (Gal.identity(), Gal.from_representative(106), 11),
    ];

    let plan = BSGSPlan::plan(&Gal, grid.clone(), &DEFAULT_EVALUATOR_COSTS, usize::MAX).unwrap();
    _ = plan.create_circuit(&ring, Vec::new());
    assert_eq!(6, plan.required_galois_keys().len());
    assert_eq!(1, plan.unhoisted_automorphism_count());
    assert_eq!(1, plan.hoisting_setup_count());
    assert_eq!(5, plan.hoisted_automorphism_count());
}
