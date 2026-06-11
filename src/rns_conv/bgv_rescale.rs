use std::alloc::Allocator;
use std::alloc::Global;

use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::homomorphism::*;
use feanor_math::matrix::*;
use feanor_math::rings::zn::*;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::integer::int_cast;
use feanor_math::ring::*;
use feanor_math::seq::*;
use tracing::instrument;

use crate::ZZi64;
use crate::rns_conv::UsedBaseConversion;
use crate::ZZbig;
use crate::rns_conv::RNSOperation;

type BGVUsedBaseConversion<A> = UsedBaseConversion<A>;

///
/// Computes the base conversion that preserves the congruence modulo some `t` in a certain sense,
/// which is required during BGV modulus-switching.
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
/// 
pub struct RNSCongruencePreservingBaseConversion<A = Global>
    where A: Allocator
{
    /// ordered as supplied when instantiating the object
    b_moduli: Vec<Zn>,
    /// moduli corresponding to `qt`
    intermediate_moduli: Vec<Zn>,
    /// the first this many moduli of `intermediate_moduli` are the output moduli
    q_moduli_count: usize,
    /// moduli of `q` are sorted as in `intermediate_moduli`
    b_to_intermediate_lift: BGVUsedBaseConversion<A>,
    /// `b^-1` as an element of `Z/tZ`
    b_inv_mod_t: El<Zn>,
    /// `b` as an element of `Z/qZ`
    b_mod_q: Vec<El<Zn>>
}

impl RNSCongruencePreservingBaseConversion {

    ///
    /// Creates a new [`RNSCongruencePreservingBaseConversion`], where
    ///  - `b` is the product of the moduli in `in_moduli`
    ///  - `q` is the product of the moduli in `out_moduli`
    ///  - `t` is the modulus of `plaintext_modulus`
    /// 
    pub fn new(in_moduli: Vec<Zn>, out_moduli: Vec<Zn>, plaintext_modulus: Zn) -> Self {
        Self::new_with_alloc(in_moduli, out_moduli, plaintext_modulus, Global)
    }
}

impl<A> RNSCongruencePreservingBaseConversion<A>
    where A: Allocator
{
    ///
    /// Creates a new [`RNSCongruencePreservingBaseConversion`], where
    ///  - `b` is the product of the moduli in `in_moduli`
    ///  - `q` is the product of the moduli in `out_moduli`
    ///  - `t` is the modulus of `plaintext_modulus`
    /// 
    #[instrument(skip_all)]
    pub fn new_with_alloc(in_moduli: Vec<Zn>, out_moduli: Vec<Zn>, plaintext_modulus: Zn, allocator: A) -> Self {
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
        intermediate_moduli.push(plaintext_modulus);

        Self {
            intermediate_moduli: intermediate_moduli.clone(),
            q_moduli_count: q_moduli_count,
            b_mod_q: intermediate_moduli[..q_moduli_count].iter().map(|rns_factor| rns_factor.coerce(&ZZbig, ZZbig.clone_el(&b))).collect(),
            b_inv_mod_t: plaintext_modulus.invert(&plaintext_modulus.coerce(&ZZbig, b)).unwrap(),
            b_to_intermediate_lift: BGVUsedBaseConversion::new_with_alloc(b_moduli.clone(), intermediate_moduli.clone(), allocator),
            b_moduli: b_moduli
        }
    }

    pub fn t_modulus(&self) -> &Zn {
        self.intermediate_moduli.last().unwrap()
    }

    pub fn allocator(&self) -> &A {
        self.b_to_intermediate_lift.allocator()
    }
}

impl<A> RNSOperation for RNSCongruencePreservingBaseConversion<A>
    where A: Allocator
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
        let Zt = self.t_modulus();

        // Compute `lift(x) mod intermediate`
        let mut x_lift: Vec<ZnEl, &A> = Vec::with_capacity_in(self.intermediate_moduli.len() * input.col_count(), self.allocator());
        x_lift.extend((0..(self.intermediate_moduli.len() * input.col_count())).map(|idx| self.intermediate_moduli.at(idx / input.col_count()).zero()));
        let mut x_lift = SubmatrixMut::from_1d(&mut x_lift, self.intermediate_moduli.len(), input.col_count());
        self.b_to_intermediate_lift.apply(input, x_lift.reborrow());

        // now compute `lift(x_lift b^-1 mod t)`, which we use to take care of the congruence modulo `t` later;
        // because of the helper moduli, this is small enough not to cause any error
        let row_count = x_lift.row_count();
        let (x_mod_q, mut x_mod_t) = x_lift.split_rows(0..(row_count - 1), (row_count - 1)..row_count);
        for j in 0..input.col_count() {
            Zt.mul_assign_ref(x_mod_t.at_mut(0, j), &self.b_inv_mod_t);
        }
        let mod_t_correction = x_mod_t;

        // compute the result as `x_mod_q - b * mod_t_correction`
        for i in 0..self.q_moduli_count {
            debug_assert!(self.intermediate_moduli[i].get_ring() == self.output_rings()[i].get_ring());
            let Zp = &self.intermediate_moduli[i];
            let b_mod_p = self.b_mod_q[i];

            if Zt.modulus() <= Zp.modulus() {
                let t = *Zt.modulus();
                let neg_t_Zp = Zp.coerce(&ZZi64, -t);
                for j in 0..output.col_count() {
                    let val = Zt.smallest_lift(*mod_t_correction.at(0, j));
                    let correction = if val < 0 {
                        Zp.add(Zp.get_ring().from_int_promise_reduced(val + t), neg_t_Zp)
                    } else {
                        Zp.get_ring().from_int_promise_reduced(val)
                    };
                    *output.at_mut(i, j) = Zp.sub(*x_mod_q.at(i, j), Zp.mul(correction, b_mod_p));
                }
            } else {
                let mod_p = Zp.can_hom(&ZZi64).unwrap();
                for j in 0..output.col_count() {
                    let correction = mod_p.map(Zt.smallest_lift(*mod_t_correction.at(0, j)));
                    *output.at_mut(i, j) = Zp.sub(*x_mod_q.at(i, j), Zp.mul(correction, b_mod_p));
                }
            }
        }
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;

#[test]
fn test_congruence_preserving_baseconv_small() {
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(23)];
    let to = vec![Zn::new(17), Zn::new(29)];
    let Zt = Zn::new(5);
    let Zb = Zn::new(23);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;
    
    let baseconv = RNSCongruencePreservingBaseConversion::new_with_alloc(
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
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(23), Zn::new(7)];
    let to = vec![Zn::new(17), Zn::new(5), Zn::new(11)];
    let Zt = Zn::new(3);
    let Zb = Zn::new(23 * 7);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;
    
    let baseconv = RNSCongruencePreservingBaseConversion::new_with_alloc(
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
    feanor_tracing::DelayedLogger::init_test();
    let from = vec![Zn::new(19), Zn::new(7), Zn::new(13)];
    let to = vec![Zn::new(17), Zn::new(5), Zn::new(3)];
    let Zt = Zn::new(11);
    let Zb = Zn::new(19 * 7 * 13);
    let b = *Zb.modulus() as i32;
    let t = *Zt.modulus() as i32;
    
    let baseconv = RNSCongruencePreservingBaseConversion::new_with_alloc(
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