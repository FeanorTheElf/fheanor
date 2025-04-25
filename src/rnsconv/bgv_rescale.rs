use std::alloc::Allocator;
use std::alloc::Global;

use feanor_math::algorithms::miller_rabin::prev_prime;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::homomorphism::*;
use feanor_math::matrix::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::primitive_int::*;
use feanor_math::integer::int_cast;
use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::seq::*;
use tracing::instrument;

use super::RNSOperation;

const ZZbig: BigIntRing = BigIntRing::RING;

///
/// We don't use Strassen-based [`super::matrix_lift::AlmostExactMatrixBaseConversion`], since
/// for BGV, usually we just use lifts from very small RNS bases (i.e. `t` or a single RNS factor
/// of `q`).
/// 
type UsedBaseConversion<A> = super::lift::AlmostExactBaseConversion<A>;

///
/// Computes the almost exact rescaling that "preserves" congruence modulo `t`,
/// as required in BGV.
/// 
/// Concretely, the image `y` of `x` is the closest integer to `ax/b` with `by = ax mod t`.
/// In particular, we compute the map
/// ```text
///   Z/qZ -> Z/(aq/b)Z,  x -> round*(ax / b) + lift(a b^-1 x - round*(ax / b) mod t)
/// ```
/// To allow an efficient RNS implementation, we allow `round*` to make an error of `+/- 1`.
/// This means that the "closest integer" above might only be the second-closest when there is
/// almost a tie.
/// 
/// In some cases, BGV modulus-switching can be implemented more efficiently by using
/// [`CongruencePreservingAlmostExactBaseConversion`].
/// 
pub struct CongruencePreservingRescaling<A = Global>
    where A: Allocator + Clone
{
    allocator: A,
    q_moduli: Vec<Zn>,
    b_moduli_indices: Vec<usize>,
    /// the `i`-th entry contains the index of `output_rings()[i]` in `input_rings()`, or
    /// `None` if `output_rings()[i]` belongs to `a`
    output_input_permutation: Vec<Option<usize>>,
    compute_delta: CongruencePreservingAlmostExactBaseConversion<A>,
    a_mod_q: Vec<El<Zn>>,
    b_inv_mod_aq_over_b: Vec<El<Zn>>
}

impl<A> CongruencePreservingRescaling<A>
    where A: Allocator + Clone
{
    pub fn scale_down(q_moduli: Vec<Zn>, den_moduli_indices: Vec<usize>, plaintext_modulus: Zn, allocator: A) -> Self {
        Self::new_with(q_moduli, Vec::new(), den_moduli_indices, plaintext_modulus, allocator)
    }

    ///
    /// Creates a new [`CongruencePreservingRescaling`], where
    ///  - `q` is the product of `in_moduli`
    ///  - `a` is the product of `num_moduli`
    ///  - `b` is the product of the moduli of `in_moduli` indexed by `den_moduli_indices`
    /// 
    #[instrument(skip_all)]
    pub fn new_with(in_moduli: Vec<Zn>, num_moduli: Vec<Zn>, den_moduli_indices: Vec<usize>, plaintext_modulus: Zn, allocator: A) -> Self {
        let ZZ = plaintext_modulus.integer_ring();
        for ring in &in_moduli {
            assert!(ring.integer_ring().get_ring() == ZZ.get_ring());
        }
        for ring in &num_moduli {
            assert!(ring.integer_ring().get_ring() == ZZ.get_ring());
        }
        let a_moduli_len = num_moduli.len();

        let b = ZZbig.prod(den_moduli_indices.iter().map(|i| int_cast(ZZ.clone_el(in_moduli[*i].modulus()), &ZZbig, ZZ)));
        let a = ZZbig.prod(num_moduli.iter().map(|rns_factor| int_cast(ZZ.clone_el(rns_factor.modulus()), &ZZbig, ZZ)));

        let output_rings = (0..in_moduli.len()).filter(|i| !den_moduli_indices.contains(i)).map(|i| in_moduli[i]).chain(num_moduli.into_iter()).collect::<Vec<_>>();
        let output_input_permutation = (0..in_moduli.len()).filter(|i| !den_moduli_indices.contains(i)).map(|i| Some(i)).chain((0..a_moduli_len).map(|_| None)).collect::<Vec<_>>();

        let compute_delta = CongruencePreservingAlmostExactBaseConversion::new_with(
            den_moduli_indices.iter().map(|i| in_moduli[*i]).collect(), 
            output_rings, 
            plaintext_modulus, 
            allocator.clone()
        );
        let output_rings = compute_delta.output_rings();
        
        return Self {
            a_mod_q: in_moduli.iter().map(|rns_factor| rns_factor.coerce(&ZZbig, ZZbig.clone_el(&a))).collect(),
            b_inv_mod_aq_over_b: output_rings.iter().map(|rns_factor| rns_factor.invert(&rns_factor.coerce(&ZZbig, ZZbig.clone_el(&b))).unwrap()).collect(),
            b_moduli_indices: den_moduli_indices,
            allocator: allocator,
            compute_delta: compute_delta,
            output_input_permutation: output_input_permutation,
            q_moduli: in_moduli
        };
    }
}

impl<A> RNSOperation for CongruencePreservingRescaling<A>
    where A: Allocator + Clone
{
    type Ring = Zn;

    type RingType = ZnBase;

    fn input_rings<'a>(&'a self) -> &'a [Zn] {
        &self.q_moduli
    }

    fn output_rings<'a>(&'a self) -> &'a [Zn] {
        self.compute_delta.output_rings()
    }

    ///
    /// # Implementation notes
    /// 
    /// A lot of this code is the same as for [`crate::rnsconv::bfv_rescale::AlmostExactRescaling`], but
    /// some subtle differences make it simpler to re-implement it.
    /// 
    /// In particular, we later refer to `x_mod_b_lift` again, which would not be accessible
    /// if we used [`crate::rnsconv::bfv_rescale::AlmostExactRescaling`]. Also, we currently lift to `aq`
    /// instead of `aq/b`, but I am not sure if that is really necessary.
    /// 
    #[instrument(skip_all)]
    fn apply<V1, V2>(&self, input: Submatrix<V1, El<Self::Ring>>, mut output: SubmatrixMut<V2, El<Self::Ring>>)
        where V1: AsPointerToSlice<El<Self::Ring>>,
            V2: AsPointerToSlice<El<Self::Ring>>
    {
        assert_eq!(input.row_count(), self.input_rings().len());
        assert_eq!(output.row_count(), self.output_rings().len());
        assert_eq!(input.col_count(), output.col_count());

        let col_count = input.col_count();

        let mut ax_mod_b = Vec::with_capacity_in(self.b_moduli_indices.len() * col_count, self.allocator.clone());
        for i in &self.b_moduli_indices {
            for j in 0..col_count {
                ax_mod_b.push(self.q_moduli[*i].mul_ref(input.at(*i, j), &self.a_mod_q[*i]));
            }
        }
        let ax_mod_b = Submatrix::from_1d(&ax_mod_b, self.b_moduli_indices.len(), col_count);

        self.compute_delta.apply(ax_mod_b, output.reborrow());

        for i in 0..self.output_rings().len() {
            for j in 0..col_count {
                if let Some(input_i) = self.output_input_permutation[i] {
                    debug_assert!(self.output_rings()[i].get_ring() == self.input_rings()[input_i].get_ring());
                    *output.at_mut(i, j) = self.output_rings()[i].mul(
                        self.output_rings()[i].sub(
                            self.output_rings()[i].mul(*input.at(input_i, j), self.a_mod_q[input_i]),
                            *output.at(i, j)
                        ),
                        self.b_inv_mod_aq_over_b[i]
                    );
                } else {
                    *output.at_mut(i, j) = self.output_rings()[i].mul(
                        self.output_rings()[i].negate(*output.at(i, j)),
                        self.b_inv_mod_aq_over_b[i]
                    );
                }
            }
        }
    }
}

///
/// Computes the base conversion that preserves the congruence modulo some `t` in a certain sense. 
/// In particular, this can be used as alternative to [`CongruencePreservingRescaling`] during BGV
/// modulus switching.
/// 
/// Concretely, the image `y` of `x` is the almost-smallest integer that is `= x mod b` and `= 0 mod t`.
/// In particular, assuming that `b | q`, we compute the map
/// ```text
///   Z/bZ -> Z/qZ,  x -> lift*(x) - b lift(lift*(x) b^-1 mod t)
/// ```
/// To allow an efficient RNS implementation, we allow `lift*` to make an error of `+/- b`.
/// Hence, "almost-smallest" could be the smallest, or second-smallest integer if there is
/// almost a tie.
/// 
/// # Difference to [`CongruencePreservingRescaling`]
/// 
/// [`CongruencePreservingRescaling`] computes the whole BGV modulus-switch. On the other hand, after
/// performing [`CongruencePreservingAlmostExactBaseConversion`], it is still necessary to subtract the result and
/// scale by `b^-1` to achieve the same effect. However, the advantage is that these steps can already
/// be performed in double-RNS representation, which means that we only need to convert the part `x mod b`
/// to coefficient/small-basis representation.
/// 
pub struct CongruencePreservingAlmostExactBaseConversion<A = Global>
    where A: Allocator + Clone
{
    /// ordered as supplied when instantiating the object
    b_moduli: Vec<Zn>,
    /// moduli corresponding to `q`, possibly with a additional helper moduli
    intermediate_moduli: Vec<Zn>,
    /// the first this many moduli of `intermediate_moduli` are the output moduli
    q_moduli_count: usize,
    /// moduli of `q` are sorted as in `intermediate_moduli`
    b_to_intermediate_lift: UsedBaseConversion<A>,
    /// moduli of `q` are sorted as in `q_over_b_moduli`
    intermediate_to_t_conv: UsedBaseConversion<A>,
    allocator: A,
    /// `b^-1` as an element of `Z/tZ`
    b_inv_mod_t: El<Zn>,
    /// `b` as an element of `Z/qZ`
    b_mod_q: Vec<El<Zn>>
}

impl<A> CongruencePreservingAlmostExactBaseConversion<A>
    where A: Allocator + Clone
{
    ///
    /// Creates a new [`CongruencePreservingAlmostExactBaseConversion`], where
    ///  - `b` is the product of the moduli in `in_moduli`
    ///  - `q` is the product of the moduli in `out_moduli`
    ///  - `t` is the modulus of `plaintext_modulus`
    /// 
    #[instrument(skip_all)]
    pub fn new_with(in_moduli: Vec<Zn>, out_moduli: Vec<Zn>, plaintext_modulus: Zn, allocator: A) -> Self {
        let ZZ = plaintext_modulus.integer_ring();
        for ring in &in_moduli {
            assert!(ring.integer_ring().get_ring() == ZZ.get_ring());
        }
        for ring in &out_moduli {
            assert!(ring.integer_ring().get_ring() == ZZ.get_ring());
        }
        
        let b = ZZbig.prod(in_moduli.iter().map(|rns_factor| int_cast(ZZ.clone_el(rns_factor.modulus()), &ZZbig, ZZ)));

        let b_moduli = in_moduli.clone();
        let q_moduli_count = out_moduli.len();
        let mut intermediate_moduli = out_moduli;

        // after the lifting to `intermediate`, we have a value `<= 2b` in absolute value; this must be `<= intermediate/4` for
        // the mod-`t` base conversion to not cause any error
        let mut current = (1 << 62) / 9;
        while ZZbig.is_lt(
            &ZZbig.prod(intermediate_moduli.iter().map(|rns_factor| int_cast(*rns_factor.modulus(), &ZZbig, ZZ))), 
            &ZZbig.int_hom().mul_ref_map(&b, &8))
        {
            current = prev_prime(StaticRing::<i64>::RING, current).unwrap();
            while intermediate_moduli.iter().any(|rns_factor| ZZ.divides(rns_factor.modulus(), &current)) {
                current = prev_prime(StaticRing::<i64>::RING, current).unwrap();
            }
            intermediate_moduli.push(Zn::new(current as u64));
        }

        Self {
            intermediate_moduli: intermediate_moduli.clone(),
            q_moduli_count: q_moduli_count,
            b_mod_q: intermediate_moduli[..q_moduli_count].iter().map(|rns_factor| rns_factor.coerce(&ZZbig, ZZbig.clone_el(&b))).collect(),
            b_inv_mod_t: plaintext_modulus.invert(&plaintext_modulus.coerce(&ZZbig, b)).unwrap(),
            b_to_intermediate_lift: UsedBaseConversion::new_with(b_moduli.clone(), intermediate_moduli.clone(), allocator.clone()),
            intermediate_to_t_conv: UsedBaseConversion::new_with(intermediate_moduli, vec![plaintext_modulus], allocator.clone()),
            b_moduli: b_moduli,
            allocator: allocator
        }
    }

    fn t_modulus(&self) -> &Zn {
        &self.intermediate_to_t_conv.output_rings()[0]
    }
}

impl<A> RNSOperation for CongruencePreservingAlmostExactBaseConversion<A>
    where A: Allocator + Clone
{
    type Ring = Zn;

    type RingType = ZnBase;

    fn input_rings<'a>(&'a self) -> &'a [Zn] {
        &self.b_moduli
    }

    fn output_rings<'a>(&'a self) -> &'a [Zn] {
        &self.intermediate_moduli[..self.q_moduli_count]
    }

    #[instrument(skip_all)]
    fn apply<V1, V2>(&self, input: Submatrix<V1, El<Self::Ring>>, mut output: SubmatrixMut<V2, El<Self::Ring>>)
        where V1: AsPointerToSlice<El<Self::Ring>>,
            V2: AsPointerToSlice<El<Self::Ring>>
    {
        // `input` is ordered as in `b_moduli`
        assert_eq!(input.row_count(), self.input_rings().len());
        assert_eq!(output.row_count(), self.output_rings().len());
        assert_eq!(input.col_count(), output.col_count());

        // Compute `lift(x) mod intermediate`
        let mut x_lift: Vec<ZnEl, A> = Vec::with_capacity_in(self.intermediate_moduli.len() * input.col_count(), self.allocator.clone());
        x_lift.extend((0..(self.intermediate_moduli.len() * input.col_count())).map(|idx| self.intermediate_moduli.at(idx / input.col_count()).zero()));
        let mut x_lift = SubmatrixMut::from_1d(&mut x_lift, self.intermediate_moduli.len(), input.col_count());
        self.b_to_intermediate_lift.apply(input, x_lift.reborrow());

        // now compute `lift(x_lift b^-1 mod t)`, which we use to take care of the congruence modulo `t` later;
        // because of the helper moduli, this is small enough not to cause any error
        let mut diff_mod_t = Vec::with_capacity_in(input.col_count(), self.allocator.clone());
        diff_mod_t.extend((0..input.col_count()).map(|_j| self.t_modulus().zero()));
        let mut diff_mod_t = SubmatrixMut::from_1d(&mut diff_mod_t, 1, input.col_count());
        self.intermediate_to_t_conv.apply(x_lift.as_const(), diff_mod_t.reborrow());
        for j in 0..input.col_count() {
            self.t_modulus().mul_assign_ref(diff_mod_t.at_mut(0, j), &self.b_inv_mod_t);
        }

        // compute the result as `x_mod_b_lift - b * diff_mod_t`
        for i in 0..self.q_moduli_count {
            debug_assert!(self.intermediate_moduli[i].get_ring() == self.output_rings()[i].get_ring());
            let Zp = &self.intermediate_moduli[i];
            let modulo = Zp.can_hom(self.t_modulus().integer_ring()).unwrap();
            debug_assert!(Zp.integer_ring().get_ring() == self.t_modulus().integer_ring().get_ring());
            let b = self.b_mod_q.at(i);
            for j in 0..input.col_count() {
                *output.at_mut(i, j) = Zp.sub_ref_fst(x_lift.at(i, j), Zp.mul_ref_fst(b, modulo.map(self.t_modulus().smallest_lift(*diff_mod_t.at(0, j)))));
            }
        }
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;

#[test]
fn test_rescale_complete() {
    let from = vec![Zn::new(17), Zn::new(23), Zn::new(29)];
    let to = vec![Zn::new(19), Zn::new(31), Zn::new(37), Zn::new(39)];
    let Zt = Zn::new(5);
    let q = 17 * 23 * 29;
    let qprime = 19 * 31 * 37 * 39;

    let rescaling = CongruencePreservingRescaling::new_with(
        from.clone(), 
        to.clone(), 
        vec![0, 1, 2],
        Zt.clone(), 
        Global
    );

    let ZZ_to_Zt = Zt.can_hom(&StaticRing::<i64>::RING).unwrap();
    
    for i in -(q/2)..=(q/2) {
        let input = i;
        let rescaled = (input as f64 * qprime as f64 / q as f64).round() as i64;
        let expected = rescaled + Zt.smallest_lift(Zt.sub(
            Zt.checked_div(&ZZ_to_Zt.map(input * qprime), &ZZ_to_Zt.map(q)).unwrap(),
            ZZ_to_Zt.map(rescaled)
        ));

        assert!(Zt.is_zero(&ZZ_to_Zt.map(input * qprime - expected * q)));

        let input = from.iter().map(|Zn| Zn.int_hom().map(input as i32)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected as i32)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        rescaling.apply(Submatrix::from_1d(&input, 3, 1), SubmatrixMut::from_1d(&mut actual, 4, 1));

        for j in 0..expected.len() {
            assert!(
                to.at(j).eq_el(expected.at(j), actual.at(j)) ||
                to.at(j).eq_el(&to.at(j).add_ref_fst(expected.at(j), to.at(j).int_hom().map(5)), actual.at(j)) ||
                to.at(j).eq_el(&to.at(j).sub_ref_fst(expected.at(j), to.at(j).int_hom().map(5)), actual.at(j)),
                "Got {}, expected one of {}, {}, {} (mod {})",
                to.at(j).format(actual.at(j)),
                to.at(j).format(expected.at(j)),
                to.at(j).format(&to.at(j).add_ref_fst(expected.at(j), to.at(j).int_hom().map(5))),
                to.at(j).format(&to.at(j).sub_ref_fst(expected.at(j), to.at(j).int_hom().map(5))),
                to.at(j).modulus()
            );
        }        
    }
}

#[test]
fn test_rescale_partial() {
    let from = vec![Zn::new(17), Zn::new(23), Zn::new(29)];
    let to = vec![Zn::new(17), Zn::new(29), Zn::new(13)];
    let Zt = Zn::new(7);
    let q = 17 * 23 * 29;
    let qprime = 17 * 29 * 13;

    let rescaling = CongruencePreservingRescaling::new_with(
        from.clone(), 
        vec![Zn::new(13)], 
        vec![1],
        Zt.clone(), 
        Global
    );

    let ZZ_to_Zt = Zt.int_hom();
    
    for i in -(q/2)..=(q/2) {
        let input = i;
        let rescaled = (input as f64 * qprime as f64 / q as f64).round() as i32;
        let expected = rescaled + Zt.smallest_lift(Zt.sub(
            Zt.checked_div(&ZZ_to_Zt.map(input * qprime), &ZZ_to_Zt.map(q)).unwrap(),
            ZZ_to_Zt.map(rescaled)
        )) as i32;

        assert!(Zt.is_zero(&ZZ_to_Zt.map(input * qprime - expected * q)));

        let input = from.iter().map(|Zn| Zn.int_hom().map(input)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        rescaling.apply(Submatrix::from_1d(&input, 3, 1), SubmatrixMut::from_1d(&mut actual, 3, 1));

        for j in 0..expected.len() {
            assert!(
                to.at(j).eq_el(expected.at(j), actual.at(j)) ||
                to.at(j).eq_el(&to.at(j).add_ref_fst(expected.at(j), to.at(j).int_hom().map(7)), actual.at(j)) ||
                to.at(j).eq_el(&to.at(j).sub_ref_fst(expected.at(j), to.at(j).int_hom().map(7)), actual.at(j)),
                "Got {}, expected one of {}, {}, {} (mod {})",
                to.at(j).format(actual.at(j)),
                to.at(j).format(expected.at(j)),
                to.at(j).format(&to.at(j).add_ref_fst(expected.at(j), to.at(j).int_hom().map(7))),
                to.at(j).format(&to.at(j).sub_ref_fst(expected.at(j), to.at(j).int_hom().map(7))),
                to.at(j).modulus()
            );
        }        
    }
}

#[test]
fn test_rescale_down() {
    let from = vec![Zn::new(17), Zn::new(23), Zn::new(29)];
    let to = vec![Zn::new(23), Zn::new(29)];
    let Zt = Zn::new(5);
    let q = 17 * 23 * 29;
    let qprime = 23 * 29;

    let rescaling = CongruencePreservingRescaling::scale_down(
        from.clone(), 
        vec![0],
        Zt.clone(), 
        Global
    );

    let ZZ_to_Zt = Zt.int_hom();

    for i in -(q/2)..=(q/2) {
        let input = i;
        let rescaled = (input as f64 * qprime as f64 / q as f64).round() as i32;
        let expected = rescaled + Zt.smallest_lift(Zt.sub(
            Zt.checked_div(&ZZ_to_Zt.map(input * qprime), &ZZ_to_Zt.map(q)).unwrap(),
            ZZ_to_Zt.map(rescaled)
        )) as i32;

        assert!(Zt.is_zero(&ZZ_to_Zt.map(input * qprime - expected * q)));

        let input = from.iter().map(|Zn| Zn.int_hom().map(input)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        rescaling.apply(Submatrix::from_1d(&input, 3, 1), SubmatrixMut::from_1d(&mut actual, 2, 1));

        for j in 0..expected.len() {
            // we currently assume no error happens
            assert_el_eq!(to.at(j), expected.at(j), actual.at(j));
        }
    }
}

#[test]
fn test_congruence_preserving_baseconv_small() {
    let from = vec![Zn::new(23)];
    let to = vec![Zn::new(17), Zn::new(29)];
    let Zt = Zn::new(5);
    let Zb = Zn::new(23);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;
    
    let baseconv = CongruencePreservingAlmostExactBaseConversion::new_with(
        from.clone(),
        to.clone(),
        Zt.clone(), 
        Global
    );

    let ZZ_to_Zt = Zt.int_hom();
    let ZZ_to_Zb = Zb.int_hom();

    for i in -(b/2)..=(b/2) {
        let input = i;
        let input_mod_b = Zb.smallest_lift(ZZ_to_Zb.map(input)) as i32;
        let expected = input_mod_b - b * Zt.smallest_lift(Zt.checked_div(&ZZ_to_Zt.map(input_mod_b), &ZZ_to_Zt.map(b)).unwrap()) as i32;
        assert_el_eq!(&Zb, ZZ_to_Zb.map(input), ZZ_to_Zb.map(expected));
        assert_eq!(0, expected % t);
        assert!(expected.abs() <= b * t / 2);

        let input = from.iter().map(|Zn| Zn.int_hom().map(input)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        baseconv.apply(Submatrix::from_1d(&input, 1, 1), SubmatrixMut::from_1d(&mut actual, 2, 1));
        
        for j in 0..expected.len() {
            // we currently assume no error happens
            assert_el_eq!(to.at(j), expected.at(j), actual.at(j));
        }
    }
}

#[test]
fn test_congruence_preserving_baseconv_two_denominators() {
    let from = vec![Zn::new(23), Zn::new(7)];
    let to = vec![Zn::new(17), Zn::new(5), Zn::new(11)];
    let Zt = Zn::new(3);
    let Zb = Zn::new(23 * 7);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;
    
    let baseconv = CongruencePreservingAlmostExactBaseConversion::new_with(
        from.clone(),
        to.clone(),
        Zt.clone(), 
        Global
    );

    let ZZ_to_Zt = Zt.int_hom();
    let ZZ_to_Zb = Zb.int_hom();

    for i in -(b/2)..=(b/2) {
        let input = i;
        let input_mod_b = Zb.smallest_lift(ZZ_to_Zb.map(input)) as i32;
        let expected = input_mod_b - b * Zt.smallest_lift(Zt.checked_div(&ZZ_to_Zt.map(input_mod_b), &ZZ_to_Zt.map(b)).unwrap()) as i32;
        assert_el_eq!(&Zb, ZZ_to_Zb.map(input), ZZ_to_Zb.map(expected));
        assert_eq!(0, expected % t);
        assert!(expected.abs() <= b * t / 2);

        let input = from.iter().map(|Zn| Zn.int_hom().map(input)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        baseconv.apply(Submatrix::from_1d(&input, 2, 1), SubmatrixMut::from_1d(&mut actual, 3, 1));
        
        for j in 0..expected.len() {
            // we currently assume no error happens
            assert_el_eq!(to.at(j), expected.at(j), actual.at(j));
        }
    }
}

#[test]
fn test_congruence_preserving_baseconv_unordered() {
    let from = vec![Zn::new(19), Zn::new(7), Zn::new(13)];
    let to = vec![Zn::new(17), Zn::new(5), Zn::new(3)];
    let Zt = Zn::new(11);
    let Zb = Zn::new(19 * 7 * 13);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;
    
    let baseconv = CongruencePreservingAlmostExactBaseConversion::new_with(
        from.clone(),
        to.clone(),
        Zt.clone(), 
        Global
    );

    let ZZ_to_Zt = Zt.int_hom();
    let ZZ_to_Zb = Zb.int_hom();

    for i in -(b/2)..=(b/2) {
        let input = i;
        let input_mod_b = Zb.smallest_lift(ZZ_to_Zb.map(input)) as i32;
        let expected = input_mod_b - b * Zt.smallest_lift(Zt.checked_div(&ZZ_to_Zt.map(input_mod_b), &ZZ_to_Zt.map(b)).unwrap()) as i32;
        assert_el_eq!(&Zb, ZZ_to_Zb.map(input), ZZ_to_Zb.map(expected));
        assert_eq!(0, expected % t);
        assert!(expected.abs() <= b * t / 2);

        let input = from.iter().map(|Zn| Zn.int_hom().map(input)).collect::<Vec<_>>();
        let expected = to.iter().map(|Zn| Zn.int_hom().map(expected)).collect::<Vec<_>>();
        let mut actual = to.iter().map(|Zn| Zn.zero()).collect::<Vec<_>>();

        baseconv.apply(Submatrix::from_1d(&input, 3, 1), SubmatrixMut::from_1d(&mut actual, 3, 1));
        
        for j in 0..expected.len() {
            // we currently assume no error happens
            assert_el_eq!(to.at(j), expected.at(j), actual.at(j));
        }
    }
}