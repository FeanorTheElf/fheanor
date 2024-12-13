use dense_poly::DensePolyRing;
use feanor_math::algorithms::linsolve::LinSolveRing;
use feanor_math::assert_el_eq;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::*;
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
use feanor_math::rings::extension::*;
use feanor_math::rings::poly::*;
use feanor_math::rings::zn::zn_64::Zn;

///
/// Interpolation data for a list of moduli `f1, ..., fn` that can be used
/// to derive from remainders `r1, ..., rn` an "interpolation polynomial" `h`
/// such that `h = ri mod fi`.
/// 
/// Clearly this requires that the moduli `fi` are pairwise coprime. Additionally,
/// we currently require that all interpolation unit vectors `ei` (defined
/// by `ei = 1 mod fi`, `ei = 0 mod fj` for `j != i`) exist over the base
/// ring (e.g. they might not be integral, even if the base ring is `Z`).
/// 
pub struct FastPolyInterpolation<P>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: LinSolveRing
{
    poly_ring: P,
    // input_moduli: Vec<El<P>>,
    unit_vectors: Vec<Vec<(El<P>, El<P>)>>,
    final_modulus: El<P>,
    n: usize
}

///
/// Computes a polynomial `h` of degree `< deg(fg)` such that `h = 1 mod f` and `h = 0 mod g`.
/// 
fn crt_unit_vectors<P>(poly_ring: P, f: &El<P>, g: &El<P>) -> El<P>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: LinSolveRing
{
    assert!(poly_ring.base_ring().is_one(poly_ring.lc(f).unwrap()));
    assert!(poly_ring.base_ring().is_one(poly_ring.lc(g).unwrap()));
    let deg_f = poly_ring.degree(&f).unwrap();

    let mod_f_ring = FreeAlgebraImpl::new(poly_ring.base_ring(), deg_f, (0..deg_f).map(|i| poly_ring.base_ring().negate(poly_ring.base_ring().clone_el(poly_ring.coefficient_at(&f, i)))).collect::<Vec<_>>());
    let g_mod_f = poly_ring.div_rem_monic(poly_ring.clone_el(&g), &f).1;
    let g_mod_f = mod_f_ring.from_canonical_basis((0..deg_f).map(|i| poly_ring.base_ring().clone_el(poly_ring.coefficient_at(&g_mod_f, i))));
    let normalization_factor = mod_f_ring.invert(&g_mod_f);
    assert!(normalization_factor.is_some(), "crt unit vector modulo {} and {} does not exist", poly_ring.format(f), poly_ring.format(g));
    let g_mod_f_inv = mod_f_ring.poly_repr(&poly_ring, &normalization_factor.unwrap(), poly_ring.base_ring().identity());
    let first_unit_vector = poly_ring.mul_ref_snd(g_mod_f_inv, &g);

    debug_assert!(poly_ring.is_one(&poly_ring.div_rem_monic(poly_ring.clone_el(&first_unit_vector), &f).1));
    debug_assert!(poly_ring.is_zero(&poly_ring.div_rem_monic(poly_ring.clone_el(&first_unit_vector), &g).1));

    return first_unit_vector;
}

impl<P> FastPolyInterpolation<P>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: LinSolveRing
{
    pub fn new(poly_ring: P, moduli: Vec<El<P>>) -> Self {
        let n = moduli.len();
        let mut current = moduli.iter().map(|f| poly_ring.clone_el(f)).collect::<Vec<_>>();
        let mut result = Vec::new();
        while current.len() > 1 {
            let mut result_part = Vec::new();
            let mut new = Vec::new();
            let mut moduli_it = current.array_chunks::<2>();
            for [f, g] in moduli_it.by_ref() {
                let new_modulus = poly_ring.mul_ref(f, g);
                let unit_vectors = (crt_unit_vectors(&poly_ring, f, g), crt_unit_vectors(&poly_ring, g, f));
                result_part.push(unit_vectors);
                new.push(new_modulus);
            }
            if let Some(last) = moduli_it.remainder().get(0) {
                new.push(poly_ring.clone_el(last));
            }
            current = new;
            result.push(result_part);
        }
        return Self {
            final_modulus: current.pop().unwrap(),
            // input_moduli: moduli,
            n: n,
            poly_ring: poly_ring,
            unit_vectors: result
        };
    }

    pub fn poly_ring(&self) -> &P {
        &self.poly_ring
    }

    // pub fn input_moduli(&self) -> &[El<P>] {
    //     &self.input_moduli
    // }

    pub fn final_modulus(&self) -> &El<P> {
        &self.final_modulus
    }

    ///
    /// Computes a polynomial of degree `< 2 * deg(prod(moduli))` that is congruent
    /// to `remainders[i]` modulo `moduli[i]`.
    /// 
    /// It is unreduced, since we can reduce its degree to `< deg(prod(moduli))` by
    /// taking the remainder modulo `prod(moduli)`.
    /// 
    /// However, this can be computed really fast, in time `n log(n)^2` if FFT-based
    /// polynomial multiplication is used by the underlying polynomial ring. It is also
    /// very fast in practice, since we don't perform any polynomial division.
    /// 
    pub fn interpolate_unreduced(&self, remainders: Vec<El<P>>) -> El<P> {
        assert_eq!(self.n, remainders.len());
        // for i in 0..self.n {
        //     assert!(self.poly_ring.degree(&remainders[i]).unwrap_or(0) < self.poly_ring.degree(&self.input_moduli()[i]).unwrap());
        // }
        let mut current = remainders;
        for i in 0..self.unit_vectors.len() {
            let mut new = Vec::new();
            let mut current_it = current.array_chunks::<2>();
            for ([f0, f1], (e0, e1)) in current_it.by_ref().zip(self.unit_vectors[i].iter()) {
                new.push(self.poly_ring.add(
                    self.poly_ring.mul_ref(f0, e0),
                    self.poly_ring.mul_ref(f1, e1)
                ));
            }
            if let Some(last) = current_it.remainder().get(0) {
                new.push(self.poly_ring.clone_el(last));
            }
            current = new;
        }
        debug_assert_eq!(1, current.len());
        let result = current.pop().unwrap();
        debug_assert!(self.poly_ring.degree(&result).unwrap_or(0) < 2 * self.poly_ring.degree(self.final_modulus()).unwrap());
        return result;
    }
}

#[test]
fn test_interpolate() {
    let base_ring = Zn::new(257);
    let poly_ring = DensePolyRing::new(base_ring, "X");

    let moduli = poly_ring.with_wrapped_indeterminate(|X| [
        X.pow_ref(2) - 1,
        X.pow_ref(3) + X - 1,
        X.pow_ref(2) - X + 2,
        X.pow_ref(2) - 2 * X
    ]);
    let remainders = poly_ring.with_wrapped_indeterminate(|X| [
        -1 * X + 3,
        -5 * X.pow_ref(2) + 21 * X - 12,
        -728 * X + 16,
        720896 * X
    ]);
    let interpolation = FastPolyInterpolation::new(&poly_ring, moduli.iter().map(|f| poly_ring.clone_el(f)).collect());
    let result = interpolation.interpolate_unreduced(remainders.iter().map(|f| poly_ring.clone_el(f)).collect());
    for i in 0..4 {
        assert_el_eq!(&poly_ring, &remainders[i], poly_ring.div_rem_monic(poly_ring.clone_el(&result), &moduli[i]).1);
    }

    let moduli = poly_ring.with_wrapped_indeterminate(|X| [
        X.pow_ref(2) - 1,
        X.pow_ref(3) + X - 1,
        X.pow_ref(2) - X + 2
    ]);
    let remainders = poly_ring.with_wrapped_indeterminate(|X| [
        -1 * X + 3,
        -5 * X.pow_ref(2) + 21 * X - 12,
        -728 * X + 16
    ]);
    let interpolation = FastPolyInterpolation::new(&poly_ring, moduli.iter().map(|f| poly_ring.clone_el(f)).collect());
    let result = interpolation.interpolate_unreduced(remainders.iter().map(|f| poly_ring.clone_el(f)).collect());
    for i in 0..3 {
        assert_el_eq!(&poly_ring, &remainders[i], poly_ring.div_rem_monic(poly_ring.clone_el(&result), &moduli[i]).1);
    }
    
    let moduli = poly_ring.with_wrapped_indeterminate(|X| [
        X.pow_ref(2) - 1,
        X.pow_ref(2) - 2,
        X.pow_ref(2) - 3,
        X.pow_ref(2) - 4,
        X.pow_ref(2) - 5,
        X.pow_ref(2) - 6,
        X.pow_ref(2) - 7,
        X.pow_ref(2) - 8,
        X.pow_ref(2) - 9,
        X.pow_ref(2) - 10,
    ]);
    let remainders = poly_ring.with_wrapped_indeterminate(|X| [
        5 * X + 10,
        5 * X + 9,
        5 * X + 8,
        5 * X + 7,
        5 * X + 6,
        5 * X + 5,
        5 * X + 4,
        5 * X + 3,
        5 * X + 2,
        5 * X + 1,
    ]);
    let interpolation = FastPolyInterpolation::new(&poly_ring, moduli.iter().map(|f| poly_ring.clone_el(f)).collect());
    let result = interpolation.interpolate_unreduced(remainders.iter().map(|f| poly_ring.clone_el(f)).collect());
    for i in 0..10 {
        assert_el_eq!(&poly_ring, &remainders[i], poly_ring.div_rem_monic(poly_ring.clone_el(&result), &moduli[i]).1);
    }
}