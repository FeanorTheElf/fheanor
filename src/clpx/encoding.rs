use feanor_math::algorithms::eea::*;
use feanor_math::algorithms::resultant::resultant_local;
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::field::FieldStore;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::ring::*;
use feanor_math::algorithms::cyclotomic::cyclotomic_polynomial;
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::rings::field::*;
use feanor_math::rings::poly::*;
use feanor_math::rings::poly::dense_poly::*;
use feanor_math::rings::poly::sparse_poly::*;
use feanor_math::primitive_int::*;
use feanor_math::rings::rational::RationalField;
use feanor_math::rings::zn::*;
use feanor_math::integer::*;
use feanor_math::seq::sparse::SparseMapVector;
use feanor_math::seq::VectorFn;
use feanor_math::rings::zn::zn_64::Zn;
use feanor_math::seq::VectorViewMut;
use crate::cyclotomic::{CyclotomicRing, CyclotomicRingStore};
use crate::ciphertext_ring::BGFVCiphertextRing;
use crate::log_time;

const ZZi64: StaticRing<i64> = StaticRing::RING;
const ZZbig: BigIntRing = BigIntRing::RING;

///
/// Implements the isomorphism
/// ```text
///   Z[𝝵]/(p, t(𝝵)) -> Fp
/// ```
/// that exists when `t(𝝵) in Z[𝝵]` and `p` is a prime that divides
/// `N(t(𝝵))` exactly once.
///
pub struct CLPXBaseEncoding {
    n: usize,
    ZZi64X: DensePolyRing<StaticRing<i64>>,
    ZZbigX: DensePolyRing<BigIntRing>,
    t: El<DensePolyRing<StaticRing<i64>>>,
    /// The (algebraic) norm `N(t)` of `t`, which is equivalent to `Res(t(X), Phi_n(X))`
    normt: El<BigIntRing>,
    /// The cyclotomic polynomial `Phi_n(X)`
    Phi_n: El<DensePolyRing<StaticRing<i64>>>,
    /// the value `N(t) t^-1`, which is an element of `Z[𝝵]`
    normt_t_inv: El<DensePolyRing<BigIntRing>>,
    Fp: AsField<zn_big::Zn<BigIntRing>>,
    /// The image of `𝝵` under the isomorphism `Z[𝝵]/(p, t) -> Fp`
    zeta_im: El<AsField<zn_big::Zn<BigIntRing>>>
}

impl CLPXBaseEncoding {

    pub fn new<const LOG: bool>(n: usize, ZZi64X: DensePolyRing<StaticRing<i64>>, t: El<DensePolyRing<StaticRing<i64>>>, prime: El<BigIntRing>) -> Self {
        let ZZbigX = DensePolyRing::new(ZZbig, "X");
        let ZZi64X_to_ZZbigX = ZZbigX.can_hom(&ZZi64X).unwrap();
        let QQX = DensePolyRing::new(RationalField::new(ZZbig), "X");
        let QQ = QQX.base_ring();
        let ZZi64X_to_QQX = QQX.can_hom(&ZZi64X).unwrap();

        let Phi_n = cyclotomic_polynomial(&ZZi64X, n);

        // we compute `N(t) = Res(t(X), Phi_n(X))`; this is large, so use big integers
        let norm = log_time::<_, _, LOG, _>("Compute Resultant", |[]| 
            ZZbig.abs(resultant_local(&ZZbigX, ZZi64X_to_ZZbigX.map_ref(&Phi_n), ZZi64X_to_ZZbigX.map_ref(&t)))
        );
        let rest = ZZbig.checked_div(&norm, &prime).unwrap();
        assert!(!ZZbig.divides(&rest, &prime));

        // compute the inverse of `t(X)` modulo `Phi_n(X)`, which is required for encoding
        let (mut s, _, d) = log_time::<_, _, LOG, _>("Compute Inverse", |[]| 
            eea(ZZi64X_to_QQX.map_ref(&t), ZZi64X_to_QQX.map_ref(&Phi_n), &QQX)
        );
        assert_eq!(0, QQX.degree(&d).unwrap());
        QQX.inclusion().mul_assign_map(&mut s, QQ.div(&QQ.inclusion().map_ref(&norm), QQX.coefficient_at(&d, 0)));
        let normt_t_inv = ZZbigX.from_terms(QQX.terms(&s).map(|(c, i)| (
            ZZbig.checked_div(QQ.num(c), QQ.den(c)).unwrap(),
            i
        )));

        // compute the image of `𝝵` under `Z[𝝵]/(p, t) -> Fp`, by observing that it must be zero of both `t(X)` and `Phi_n(X)` mod `p`
        let Fp = zn_big::Zn::new(ZZbig, prime).as_field().ok().unwrap();
        let FpX = DensePolyRing::new(&Fp, "X");
        let ZZi64X_to_FpX = FpX.can_hom(&ZZi64X).unwrap();

        let gcd = log_time::<_, _, LOG, _>("Compute GCD", |[]| {
            gcd(ZZi64X_to_FpX.map_ref(&Phi_n), ZZi64X_to_FpX.map_ref(&t), &FpX)
        });
        assert_eq!(1, FpX.degree(&gcd).unwrap());
        let zeta_im = Fp.negate(Fp.checked_div(FpX.coefficient_at(&gcd, 0), FpX.coefficient_at(&gcd, 1)).unwrap());
        return Self {
            n: n,
            Phi_n: Phi_n,
            zeta_im: zeta_im,
            ZZbigX: ZZbigX,
            ZZi64X: ZZi64X,
            Fp: Fp,
            normt: norm,
            normt_t_inv: normt_t_inv,
            t: t
        };
    }

    ///
    /// Returns the multiplicative order of `𝝵` (also sometimes called conductor of `R`).
    /// 
    pub fn n(&self) -> usize {
        self.n
    }

    pub fn Fp(&self) -> &AsField<zn_big::Zn<BigIntRing>> {
        &self.Fp
    }

    pub fn ZZX(&self) -> &DensePolyRing<BigIntRing> {
        &self.ZZbigX
    }

    ///
    /// Computes the map
    /// ```text
    ///   Z[𝝵]/(p, t(𝝵)) -> Z[𝝵]/(Q),  x -> round(Q lift(x) / t(𝝵))
    /// ```
    /// where `lift(x)` is an arbitrary lift of `x` to `Z[𝝵]/(t)`.
    /// 
    /// The result is returned as an iterator over its coefficients w.r.t. `𝝵`.
    /// 
    pub fn encode_impl<'a>(&'a self, ZQ: &'a zn_rns::Zn<zn_64::Zn, BigIntRing>, x: El<AsField<zn_big::Zn<BigIntRing>>>) -> impl 'a + ExactSizeIterator<Item = El<zn_rns::Zn<zn_64::Zn, BigIntRing>>> + DoubleEndedIterator {
        let x_lift = self.Fp().smallest_lift(x);
        let mod_Q = ZQ.can_hom(&ZZbig).unwrap();
        return (0..self.ZZi64X.degree(&self.Phi_n).unwrap()).map(move |i| ZZbig.rounded_div(
            ZZbig.mul_ref_snd(ZZbig.mul_ref(&x_lift, self.ZZX().coefficient_at(&self.normt_t_inv, i)), ZQ.modulus()),
            &self.normt
        )).map(move |c| mod_Q.map(c));
    }

    ///
    /// Computes the map
    /// ```text
    ///   Z[𝝵]/(Q) -> Z[𝝵]/(p, t(𝝵)),  x -> round(t(𝝵) x / Q) mod p
    /// ```
    /// 
    pub fn decode_impl<'a, I>(&'a self, ZQ: &'a zn_rns::Zn<zn_64::Zn, BigIntRing>, coeffs: I) -> El<AsField<zn_big::Zn<BigIntRing>>>
        where I: Iterator<Item = El<zn_rns::Zn<zn_64::Zn, BigIntRing>>>
    {
        let f = self.ZZX().from_terms(coeffs.enumerate().map(|(i, c)| (ZQ.smallest_lift(c), i)));
        let ZZi64X_to_ZZbigX = self.ZZbigX.can_hom(&self.ZZi64X).unwrap();
        let t_f = self.ZZX().div_rem_monic(self.ZZX().mul(f, ZZi64X_to_ZZbigX.map_ref(&self.t)), &ZZi64X_to_ZZbigX.map_ref(&self.Phi_n)).1;
        let mut current = self.Fp().zero();
        let mod_p = self.Fp().can_hom(&ZZbig).unwrap();
        for i in (0..self.ZZi64X.degree(&self.Phi_n).unwrap()).rev() {
            self.Fp().mul_assign_ref(&mut current, &self.zeta_im);
            self.Fp().add_assign(&mut current, mod_p.map(ZZbig.rounded_div(ZZbig.clone_el(self.ZZX().coefficient_at(&t_f, i)), ZQ.modulus())));
        }
        return current;
    }

    ///
    /// Finds a small preimage under the map `Z[X] -> Z[X]/(p, t(X), Phi_n(X)) -> Fp`
    /// 
    pub fn small_preimage(&self, x: El<AsField<zn_big::Zn<BigIntRing>>>) -> El<DensePolyRing<BigIntRing>> {
        let x_lift = self.Fp().smallest_lift(x);
        // `y in Z[X]` such that `yt` is close to `x_lift` modulo `Phi_n`
        let y = self.ZZX().from_terms(self.ZZX().terms(&self.normt_t_inv).map(|(c, i)| (
            ZZbig.rounded_div(ZZbig.mul_ref(c, &x_lift), &self.normt),
            i
        )));
        let ZZi64X_to_ZZbigX = self.ZZX().can_hom(&self.ZZi64X).unwrap();
        let close_point = self.ZZX().div_rem_monic(
            self.ZZX().mul(y, ZZi64X_to_ZZbigX.map_ref(&self.t)), 
            &ZZi64X_to_ZZbigX.map_ref(&self.Phi_n)
        ).1;
        return self.ZZX().sub(self.ZZX().inclusion().map(x_lift), close_point);
    }

    ///
    /// Evaluates the map `Z[X] -> Z[X]/(p, t(X), Phi_n(X)) -> Fp`
    /// 
    pub fn map(&self, f: &El<DensePolyRing<BigIntRing>>) -> El<AsField<zn_big::Zn<BigIntRing>>> {
        self.ZZX().evaluate(f, &self.zeta_im, self.Fp().can_hom(&ZZbig).unwrap())
    }
}

pub type IsomorphicRing = FreeAlgebraImpl<AsField<zn_big::Zn<BigIntRing>>, SparseMapVector<AsField<zn_big::Zn<BigIntRing>>>>;

///
/// Implements the isomorphism
/// ```text
///   Z[𝝵]/(p, t(𝝵^n2)) -> Fp[X]/(Phi_n2(X))
/// ```
/// where `n = n1 * n2` for integers `n1`, `n2` and `p` is a prime
/// that divides `N(t(𝝵^n2))` exactly once (where the norm here is the norm in
/// the smaller field extension `Q[𝝵^n2]/Q`).
/// 
/// In this sense, this is the result of tensoring [`CLPXBaseEncoding`] (for `n = n1`)
/// with `Z[X]/(Phi_n2(X))`.
///
pub struct CLPXEncoding {
    n2: usize,
    encoding: CLPXBaseEncoding,
    plaintext_ring: IsomorphicRing,
    Phi_n: El<DensePolyRing<BigIntRing>>,
    normt_t_inv: El<DensePolyRing<BigIntRing>>,
    t: El<DensePolyRing<BigIntRing>>
}

impl CLPXEncoding {

    pub fn new<const LOG: bool>(n2: usize, encoding: CLPXBaseEncoding) -> Self {
        // TODO: drop this constraint
        assert_eq!(1, signed_gcd(encoding.n() as i64, n2 as i64, ZZi64));
        let sparse_ZZi64X = SparsePolyRing::new(ZZi64, "X");
        let Phi_n2 = cyclotomic_polynomial(&sparse_ZZi64X, n2);
        let mut X_pow_phi_n2_mod_Phi_n2 = SparseMapVector::new(sparse_ZZi64X.degree(&Phi_n2).unwrap(), encoding.Fp().clone());
        for (c, i) in sparse_ZZi64X.terms(&Phi_n2) {
            if i != sparse_ZZi64X.degree(&Phi_n2).unwrap() {
                *X_pow_phi_n2_mod_Phi_n2.at_mut(i) = encoding.Fp().coerce(&ZZi64, -*c);
            }
        }
        let plaintext_ring = FreeAlgebraImpl::new(encoding.Fp().clone(), sparse_ZZi64X.degree(&Phi_n2).unwrap(), X_pow_phi_n2_mod_Phi_n2);

        let Phi_n = encoding.ZZX().coerce(&sparse_ZZi64X, cyclotomic_polynomial(&sparse_ZZi64X, encoding.n() * n2));
        let t = log_time::<_, _, LOG, _>("Compute tensor t ⊗ 1", |[]|
            encoding.ZZX().div_rem_monic(encoding.ZZX().from_terms(encoding.ZZi64X.terms(&encoding.t).map(|(c, i)| (int_cast(*c, ZZbig, ZZi64), i * n2))), &Phi_n).1
        );
        let normt_t_inv = log_time::<_, _, LOG, _>("Compute t^-1 ⊗ 1", |[]|
            encoding.ZZX().div_rem_monic(encoding.ZZX().from_terms(encoding.ZZX().terms(&encoding.normt_t_inv).map(|(c, i)| (ZZbig.clone_el(c), i * n2))), &Phi_n).1
        );
        Self {
            n2: n2,
            t: t,
            normt_t_inv: normt_t_inv,
            Phi_n: Phi_n,
            plaintext_ring: plaintext_ring,
            encoding: encoding
        }
    }

    pub fn n1(&self) -> usize {
        self.encoding.n()
    }

    pub fn n2(&self) -> usize {
        self.n2
    }

    pub fn n(&self) -> usize {
        self.n1() * self.n2()
    }

    pub fn plaintext_ring(&self) -> &IsomorphicRing {
        &self.plaintext_ring
    }

    pub fn ZZX(&self) -> &DensePolyRing<BigIntRing> {
        self.encoding.ZZX()
    }

    pub fn t(&self) -> &El<DensePolyRing<BigIntRing>> {
        &self.t
    }

    pub fn base_t(&self) -> &El<DensePolyRing<StaticRing<i64>>> {
        &self.encoding.t
    }

    pub fn base_encoding(&self) -> &CLPXBaseEncoding {
        &self.encoding
    }

    ///
    /// Computes the image under the isomorphism
    /// ```text
    ///   Z[𝝵]/(p, t(𝝵^n2)) -> Fp[X]/(Phi_n2(X))
    /// ```
    /// 
    pub fn map(&self, f: &El<DensePolyRing<BigIntRing>>) -> El<IsomorphicRing> {
        // the idea is to decompose the input as a sum of tensor products `𝝵_n2^i ⊗ ai(𝝵_n1)` and evaluate
        // the base encoding on each `ai(𝝵_n1)`; the point is that `t(𝝵^n2) = 1 ⊗ t(𝝵_n1)`
        let Zn1 = Zn::new(self.n1() as u64);
        let n2_inv = Zn1.invert(&Zn1.coerce(&ZZi64, self.n2() as i64)).unwrap();
        let Zn2 = Zn::new(self.n2() as u64);
        let n1_inv = Zn2.invert(&Zn2.coerce(&ZZi64, self.n1() as i64)).unwrap();
        let phi_n = self.ZZX().degree(&self.Phi_n).unwrap();
        let mut decoded_tensor = Vec::new();
        decoded_tensor.resize_with(self.n2(), || self.ZZX().zero());
        for (c, idx) in self.ZZX().terms(f) {
            let i = Zn2.smallest_positive_lift(Zn2.mul(Zn2.coerce(&ZZi64, idx as i64), n1_inv)) as usize;
            let j = Zn1.smallest_positive_lift(Zn1.mul(Zn1.coerce(&ZZi64, idx as i64), n2_inv)) as usize;
            debug_assert!(i * self.n1() + j * self.n2() >= phi_n || i * self.n1() + j * self.n2() == idx);
            self.ZZX().add_assign(&mut decoded_tensor[i], self.ZZX().from_terms([(ZZbig.clone_el(c), j)]));
        }
        return self.plaintext_ring().sum(decoded_tensor.into_iter().scan(self.plaintext_ring.one(), |current_gen_power, f| {
            let result = self.plaintext_ring().inclusion().mul_ref_map(current_gen_power, &self.encoding.map(&f));
            self.plaintext_ring().mul_assign(current_gen_power, self.plaintext_ring().canonical_gen());
            return Some(result);
        }));
    }

    ///
    /// Finds a small preimage under the map `Z[X] -> Z[𝝵]/(p, t(𝝵^n2)) -> Fp[X]/(Phi_n2(X))`
    /// 
    pub fn small_preimage(&self, x: &El<IsomorphicRing>) -> El<DensePolyRing<BigIntRing>> {
        // again, the idea is to note that the `i`-th input coefficient relates to the basis vectors
        // `𝝵_n2^i ⊗ 𝝵_n1^j` for all the `j`; thus we can take a small preimage of each coefficient
        // separately; this works because `t(𝝵^n2) = 1 ⊗ t(𝝵_n1)`
        let result = self.ZZX().from_terms(self.plaintext_ring().wrt_canonical_basis(&x).iter().enumerate().flat_map(|(i, c)|
            self.ZZX().terms(&self.encoding.small_preimage(c)).map(move |(c, j)| (
                ZZbig.clone_el(c),
                (i * self.n1() + j * self.n2()) % self.n()
            )).collect::<Vec<_>>()
        ));
        return self.ZZX().div_rem_monic(result, &self.Phi_n).1;
    }

    ///
    /// Computes the map
    /// ```text
    ///   Z[𝝵]/(p, t(𝝵^n2)) -> Z[𝝵]/(Q),  x -> round(Q lift(x) / t(𝝵^n2))
    /// ```
    /// where `lift(x)` is an arbitrary lift of `x` to `Z[𝝵]/(t(𝝵^n2))`.
    /// 
    pub fn encode<C>(&self, ciphertext_ring: C, x: &El<IsomorphicRing>) -> El<C>
        where C: RingStore,
            C::Type: BGFVCiphertextRing + CyclotomicRing
    {
        assert_eq!(self.n(), ciphertext_ring.n() as usize);
        let x_lift = self.ZZX().from_terms(self.plaintext_ring().wrt_canonical_basis(x).iter().enumerate().map(|(i, c)| (self.plaintext_ring().base_ring().smallest_lift(c), i * self.n1())));
        let ZQ = ciphertext_ring.base_ring();
        let mod_Q = ZQ.can_hom(&ZZbig).unwrap();
        let normt_x_lift_over_t = self.ZZX().div_rem_monic(self.ZZX().mul_ref_snd(x_lift, &self.normt_t_inv), &self.Phi_n).1;
        return ciphertext_ring.from_canonical_basis((0..ciphertext_ring.rank()).map(|i| mod_Q.map(ZZbig.rounded_div(
            ZZbig.mul_ref(self.ZZX().coefficient_at(&normt_x_lift_over_t, i), ZQ.modulus()),
            &self.encoding.normt
        ))));
    }
    
    ///
    /// Computes the map
    /// ```text
    ///   Z[𝝵]/(Q) -> Z[𝝵]/(p, t(𝝵^n2)),  x -> round(t(𝝵^n2) x / Q) mod (p, t(𝝵^n2))
    /// ```
    /// 
    pub fn decode<C>(&self, ciphertext_ring: C, x: &El<C>) -> El<IsomorphicRing>
        where C: RingStore,
            C::Type: BGFVCiphertextRing + CyclotomicRing
    {
        assert_eq!(self.n(), ciphertext_ring.n() as usize);
        let x_poly = self.ZZX().from_terms(ciphertext_ring.wrt_canonical_basis(x).iter().enumerate().map(|(i, c)| (ciphertext_ring.base_ring().smallest_lift(c), i)));
        let t = self.ZZX().from_terms(self.encoding.ZZi64X.terms(&self.encoding.t).map(|(c, i)| (int_cast(*c, ZZbig, ZZi64), i * self.n2())));
        let x_t = self.ZZX().div_rem_monic(self.ZZX().mul(x_poly, t), &self.Phi_n).1;
        let x_t_over_Q = self.ZZX().from_terms(self.ZZX().terms(&x_t).map(|(c, i)| (ZZbig.rounded_div(ZZbig.clone_el(c), ciphertext_ring.base_ring().modulus()), i)));
        return self.map(&x_t_over_Q);
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::number_ring::odd_cyclotomic::CompositeCyclotomicNumberRing;
#[cfg(test)]
use crate::ciphertext_ring::double_rns_managed::*;

#[cfg(test)]
fn test_rns_base() -> zn_rns::Zn<zn_64::Zn, BigIntRing> {
    zn_rns::Zn::create_from_primes(vec![167116801, 200540161, 284098561, 317521921, 384368641, 451215361, 501350401, 651755521, 752025601, 802160641], ZZbig)
}

#[test]
fn test_clpx_base_encoding_new() {
    let ZZX = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X - 2]);
    let n = 32;
    let encoding = CLPXBaseEncoding::new::<true>(n, ZZX.clone(), t, ZZbig.int_hom().map(65537));
    let Fp = encoding.Fp();
    assert_el_eq!(Fp, Fp.int_hom().map(2), &encoding.zeta_im);

    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    let n = 64;
    let encoding = CLPXBaseEncoding::new::<true>(n, ZZX.clone(), ZZX.clone_el(&t), ZZbig.int_hom().map(6700417));
    let Fp = encoding.Fp();
    assert_el_eq!(Fp, Fp.zero(), ZZX.evaluate(&t, &encoding.zeta_im, Fp.can_hom(&ZZi64).unwrap()));
}

#[test]
fn test_clpx_base_encoding_map() {
    let ZZX = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X - 2]);
    let n = 32;
    let encoding = CLPXBaseEncoding::new::<true>(n, ZZX.clone(), t, ZZbig.int_hom().map(65537));
    let Fp = encoding.Fp();
    let ZZX = encoding.ZZX();
    let elements = (0..16).map(|i| Fp.int_hom().map(1 << i)).collect::<Vec<_>>();
    for a in &elements {
        for b in &elements {
            assert_el_eq!(Fp, Fp.mul_ref(a, b), encoding.map(&ZZX.mul(encoding.small_preimage(Fp.clone_el(a)), encoding.small_preimage(Fp.clone_el(b)))));
        }
    }
    for a in &elements {
        assert!(ZZX.terms(&encoding.small_preimage(Fp.clone_el(a))).all(|(c, _)| int_cast(ZZbig.clone_el(c), ZZi64, ZZbig).abs() <= 1));
    }

    let ZZX = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    let n = 64;
    let encoding = CLPXBaseEncoding::new::<true>(n, ZZX.clone(), ZZX.clone_el(&t), ZZbig.int_hom().map(6700417));
    let Fp = encoding.Fp();
    let ZZX = encoding.ZZX();
    let elements = (0..30).map(|i| Fp.int_hom().map(1 << i)).collect::<Vec<_>>();
    for a in &elements {
        for b in &elements {
            assert_el_eq!(Fp, Fp.mul_ref(a, b), encoding.map(&ZZX.mul(encoding.small_preimage(Fp.clone_el(a)), encoding.small_preimage(Fp.clone_el(b)))));
        }
    }
    for a in &elements {
        assert!(ZZX.terms(&encoding.small_preimage(Fp.clone_el(a))).all(|(c, _)| int_cast(ZZbig.clone_el(c), ZZi64, ZZbig).abs() <= 1));
    }
}

#[test]
fn test_clpx_encoding_map() {
    let ZZX = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X - 2]);
    let n1 = 17;
    let n2 = 15;
    let base_encoding = CLPXBaseEncoding::new::<false>(n1, ZZX.clone(), t, ZZbig.int_hom().map(131071));
    let encoding = CLPXEncoding::new::<false>(n2, base_encoding);
    let P = encoding.plaintext_ring();
    let ZZX = encoding.ZZX();
    let rank = encoding.plaintext_ring().rank();
    let elements = [
        P.zero(),
        P.one(),
        P.int_hom().map(363),
        P.canonical_gen(),
        P.int_hom().mul_map(P.canonical_gen(), 363),
        P.add(P.canonical_gen(), P.one()),
        P.pow(P.canonical_gen(), rank - 1),
        P.int_hom().mul_map(P.pow(P.canonical_gen(), rank - 1), 363),
    ];
    for a in &elements {
        for b in &elements {
            assert_el_eq!(P, P.mul_ref(a, b), encoding.map(&ZZX.mul(encoding.small_preimage(a), encoding.small_preimage(b))));
        }
    }
    for a in &elements {
        assert!(ZZX.terms(&encoding.small_preimage(a)).all(|(c, _)| int_cast(ZZbig.clone_el(c), ZZi64, ZZbig).abs() <= 3));
    }

    let ZZX = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    let n1 = 17;
    let n2 = 15;
    let base_encoding = CLPXBaseEncoding::new::<false>(n1, ZZX.clone(), t, ZZbig.int_hom().map(43691));
    let encoding = CLPXEncoding::new::<false>(n2, base_encoding);
    let P = encoding.plaintext_ring();
    let ZZX = encoding.ZZX();
    let rank = encoding.plaintext_ring().rank();
    let elements = [
        P.zero(),
        P.one(),
        P.int_hom().map(363),
        P.canonical_gen(),
        P.int_hom().mul_map(P.canonical_gen(), 363),
        P.add(P.canonical_gen(), P.one()),
        P.pow(P.canonical_gen(), rank - 1),
        P.int_hom().mul_map(P.pow(P.canonical_gen(), rank - 1), 363),
    ];
    for a in &elements {
        for b in &elements {
            assert_el_eq!(P, P.mul_ref(a, b), encoding.map(&ZZX.mul(encoding.small_preimage(a), encoding.small_preimage(b))));
        }
    }
    for a in &elements {
        assert!(ZZX.terms(&encoding.small_preimage(a)).all(|(c, _)| int_cast(ZZbig.clone_el(c), ZZi64, ZZbig).abs() <= 3));
    }
}

#[test]
fn test_clpx_base_encoding_encode_decode() {
    let ZZX = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X - 2]);
    let n = 32;
    let encoding = CLPXBaseEncoding::new::<true>(n, ZZX.clone(), t, ZZbig.int_hom().map(65537));
    let Fp = encoding.Fp();
    let elements = (0..16).map(|i| Fp.int_hom().map(1 << i)).collect::<Vec<_>>();
    let ZQ = test_rns_base();
    for a in &elements {
        assert_el_eq!(&Fp, a, encoding.decode_impl(&ZQ, encoding.encode_impl(&ZQ, Fp.clone_el(a))));
    }

    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    let n = 17;
    let encoding = CLPXBaseEncoding::new::<true>(n, ZZX.clone(), ZZX.clone_el(&t), ZZbig.int_hom().map(43691));
    let Fp = encoding.Fp();
    let elements = (0..20).map(|i| Fp.int_hom().map(1 << i)).collect::<Vec<_>>();
    let ZQ = test_rns_base();
    for a in &elements {
        assert_el_eq!(&Fp, a, encoding.decode_impl(&ZQ, encoding.encode_impl(&ZQ, Fp.clone_el(a))));
    }
}

#[test]
fn test_clpx_encoding_encode_decode() {
    let ZZX = DensePolyRing::new(ZZi64, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X| [X.pow_ref(2) + X - 2]);
    let n1 = 17;
    let n2 = 15;
    let base_encoding = CLPXBaseEncoding::new::<false>(n1, ZZX.clone(), t, ZZbig.int_hom().map(43691));
    let encoding = CLPXEncoding::new::<false>(n2, base_encoding);
    let P = encoding.plaintext_ring();
    let rank = encoding.plaintext_ring().rank();
    let elements = [
        P.zero(),
        P.one(),
        P.int_hom().map(363),
        P.canonical_gen(),
        P.int_hom().mul_map(P.canonical_gen(), 363),
        P.add(P.canonical_gen(), P.one()),
        P.pow(P.canonical_gen(), rank - 1),
        P.int_hom().mul_map(P.pow(P.canonical_gen(), rank - 1), 363),
    ];
    let C = ManagedDoubleRNSRingBase::new(CompositeCyclotomicNumberRing::new(17, 15), test_rns_base());
    for a in &elements {
        assert_el_eq!(P, a, encoding.decode(&C, &encoding.encode(&C, a)));
    }
}