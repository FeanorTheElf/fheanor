use std::alloc::{Allocator, Global};
use std::sync::*;

use feanor_math::algorithms::convolution::*;
use feanor_math::algorithms::matmul::ComputeInnerProduct;
use feanor_math::homomorphism::*;
use feanor_math::integer::*;
use feanor_math::matrix::*;
use feanor_math::ring::*;
use feanor_math::rings::extension::*;
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::zn::*;
use feanor_math::seq::VectorView;
use feanor_math::serialization::{DeserializeSeedNewtype, DeserializeWithRing, SerializableElementRing, SerializableNewtype, SerializeWithRing};
use feanor_math::specialization::{FiniteRingOperation, FiniteRingSpecializable};
use serde::{Deserialize, Serialize};
use serde::de::DeserializeSeed;
use tracing::instrument;

use crate::cyclotomic::CyclotomicGaloisGroupEl;
use crate::cyclotomic::CyclotomicRing;
use crate::number_ring::HECyclotomicNumberRing;
use crate::number_ring::HENumberRing;

use super::double_rns_ring::*;
use super::single_rns_ring::*;
use super::BGFVCiphertextRing;
use super::PreparedMultiplicationRing;

///
/// Like [`DoubleRNSRing`] but stores element in whatever representation they
/// currently are available, and automatically switches representation when 
/// necessary.
/// 
/// # Implementation notes
/// 
/// Elements can be stored both as [`DoubleRNSEl`] and [`SmallBasisEl`].
/// Note that this includes the option of storing the element in both representations
/// simultaneously. When a multiplication is performed, elements are automatically converted
/// to [`DoubleRNSEl`] representation. When a small-basis representation is required (e.g. via 
/// [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`]), the element is
/// automatically converted to [`SmallBasisEl`] representation. These conversions can also be
/// manually triggered using [`ManagedDoubleRNSRingBase::to_small_basis()`] and
/// [`ManagedDoubleRNSRingBase::to_doublerns()`].
/// 
/// Internally, elements are stored using [`Arc`] pointers, and the pointees are logically
/// immutable, which leads to maximal reuse of representations. For example, the following
/// code only requires a single representation conversion:
/// ```
/// # use fheanor::ciphertext_ring::double_rns_managed::*;
/// # use fheanor::ciphertext_ring::*;
/// # use fheanor::number_ring::*;
/// # use fheanor::number_ring::pow2_cyclotomic::*;
/// # use feanor_math::assert_el_eq;
/// # use feanor_math::rings::zn::*;
/// # use feanor_math::rings::extension::FreeAlgebraStore;
/// # use feanor_math::rings::zn::zn_64::*;
/// # use feanor_math::homomorphism::*;
/// # use feanor_math::ring::*;
/// # use feanor_math::integer::*;
/// # use feanor_math::seq::VectorFn;
/// let rns_base = zn_rns::Zn::new(vec![Zn::new(97), Zn::new(193)], BigIntRing::RING);
/// let ring = ManagedDoubleRNSRingBase::new(Pow2CyclotomicNumberRing::new(16), rns_base);
/// // `element` is stored in small-basis representation
/// let element = ring.get_ring().from_small_basis_repr(ring.get_ring().unmanaged_ring().get_ring().from_non_fft(ring.base_ring().int_hom().map(2)));
/// // this will point to the same payload as `element`
/// let mut element_copy = ring.clone_el(&element);
/// // this will convert `element` to double-rns representation; it is now stored once w.r.t. small-basis
/// // and once w.r.t. double-rns representation
/// ring.square(&mut element_copy);
/// // `element_copy` is of course only available in double-rns representation here, but `element` is available in
/// // both double-rns and small-basis representation; hence, the next statement does not require a conversion
/// let result = ring.pow(ring.clone_el(&element), 2);
/// assert_el_eq!(ring, element_copy, result);
/// // similarly, we don't need a conversion for `wrt_canonical_basis()`, since `element` is available in small-basis representation
/// assert_el_eq!(ring.base_ring(), ring.base_ring().int_hom().map(2), ring.wrt_canonical_basis(&element).at(0));
/// ```
/// 
pub struct ManagedDoubleRNSRingBase<NumberRing, A = Global> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    base: DoubleRNSRingBase<NumberRing, A>,
    zero: SmallBasisEl<NumberRing, A>
}

pub type ManagedDoubleRNSRing<NumberRing, A = Global> = RingValue<ManagedDoubleRNSRingBase<NumberRing, A>>;

impl<NumberRing> ManagedDoubleRNSRingBase<NumberRing, Global> 
    where NumberRing: HENumberRing,
{
    pub fn new(number_ring: NumberRing, rns_base: zn_rns::Zn<zn_64::Zn, BigIntRing>) -> RingValue<Self> {
        Self::new_with(number_ring, rns_base, Global)
    }
}

enum ManagedDoubleRNSElRepresentation<'a, NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    Sum(MappedRwLockReadGuard<'a, (SmallBasisEl<NumberRing, A>, DoubleRNSEl<NumberRing, A>)>),
    SmallBasis(&'a SmallBasisEl<NumberRing, A>),
    DoubleRNS(&'a DoubleRNSEl<NumberRing, A>),
    Both(&'a SmallBasisEl<NumberRing, A>, &'a DoubleRNSEl<NumberRing, A>),
    Zero
}

struct DoubleRNSElInternal<NumberRing, A = Global> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    small_basis_repr: OnceLock<SmallBasisEl<NumberRing, A>>,
    double_rns_repr: OnceLock<DoubleRNSEl<NumberRing, A>>,
    sum_repr: RwLock<Option<(SmallBasisEl<NumberRing, A>, DoubleRNSEl<NumberRing, A>)>>
}

impl<NumberRing, A> DoubleRNSElInternal<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn get_repr<'a>(&'a self) -> ManagedDoubleRNSElRepresentation<'a, NumberRing, A> {
        let sum_repr = self.sum_repr.read().unwrap();
        if sum_repr.is_some() {
            return ManagedDoubleRNSElRepresentation::Sum(RwLockReadGuard::map(sum_repr, |sum_repr: &Option<_>| sum_repr.as_ref().unwrap()));
        }
        // we can unlock `sum_repr` here, since if `sum_repr` was empty previously, it will always remain empty
        drop(sum_repr);
        if let Some(small_basis_repr) = self.small_basis_repr.get() {
            if let Some(double_rns_repr) = self.double_rns_repr.get() {
                return ManagedDoubleRNSElRepresentation::Both(small_basis_repr, double_rns_repr);
            } else {
                return ManagedDoubleRNSElRepresentation::SmallBasis(small_basis_repr);
            }
        } else if let Some(double_rns_repr) = self.double_rns_repr.get() {
            return ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr);
        } else {
            return ManagedDoubleRNSElRepresentation::Zero;
        }
    }
}

pub struct ManagedDoubleRNSEl<NumberRing, A = Global> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    internal: Arc<DoubleRNSElInternal<NumberRing, A>>
}

impl<NumberRing, A> Clone for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing + Clone,
        A: Allocator + Clone
{
    fn clone(&self) -> Self {
        Self {
            base: self.base.clone(),
            zero: self.base.zero_non_fft()
        }
    }
}

impl<NumberRing, A> ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    pub fn new_with(number_ring: NumberRing, rns_base: zn_rns::Zn<zn_64::Zn, BigIntRing>, allocator: A) -> RingValue<ManagedDoubleRNSRingBase<NumberRing, A>> {
        let result = DoubleRNSRingBase::new_with(number_ring, rns_base, allocator);
        let zero = result.get_ring().zero_non_fft();
        ManagedDoubleRNSRing::from(ManagedDoubleRNSRingBase { base: result.into(), zero: zero })
    }

    ///
    /// Returns a reference to the underlying [`DoubleRNSRing`], which can be used
    /// to manually manage the representation of elements.
    /// 
    /// This is most useful in combination with [`ManagedDoubleRNSRingBase::to_small_basis()`] and
    /// [`ManagedDoubleRNSRingBase::to_doublerns()`], which can be used to access the underlying
    /// representation of elements.
    /// 
    pub fn unmanaged_ring(&self) -> RingRef<DoubleRNSRingBase<NumberRing, A>> {
        RingRef::new(&self.base)
    }

    ///
    /// Returns the representation of the given element w.r.t. the small basis, possibly computing
    /// this representation if it is not available. If the element is zero, `None` is returned.
    /// 
    pub fn to_small_basis<'a>(&self, value: &'a ManagedDoubleRNSEl<NumberRing, A>) -> Option<&'a SmallBasisEl<NumberRing, A>> {
        match value.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::Sum(sum_repr) => {
                drop(sum_repr);
                let mut sum_repr_lock = value.internal.sum_repr.write().unwrap();
                // if some other thread already cleared `sum_repr` between unlocking and relocking
                if sum_repr_lock.is_none() {
                    drop(sum_repr_lock);
                    return self.to_small_basis(value);
                }
                let sum_repr = std::mem::replace(&mut *sum_repr_lock, None).unwrap();
                let mut result = sum_repr.0;
                self.base.add_assign_non_fft(&mut result, &self.base.undo_fft(sum_repr.1));
                // no other thread is able to update this, since the previous call to `get_repr()` would alway return `Sum` (or run
                // after we unlocked `sum_repr_lock`)
                value.internal.small_basis_repr.set(result).ok().unwrap();
                // keep the `sum_repr_lock` until we initialized `small_basis_repr`, otherwise threads querying this in the meantime
                // might think the element stores zero
                drop(sum_repr_lock);
                return Some(value.internal.small_basis_repr.get().unwrap());
            },
            ManagedDoubleRNSElRepresentation::SmallBasis(small_basis_repr) | ManagedDoubleRNSElRepresentation::Both(small_basis_repr, _) => {
                return Some(small_basis_repr);
            },
            ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) => {
                let result = self.base.undo_fft(self.base.clone_el(double_rns_repr));
                // here another thread might have set `small_basis_repr` in the meantime, so this might return `Err(_)`
                _ = value.internal.small_basis_repr.set(result);
                return Some(value.internal.small_basis_repr.get().unwrap());
            },
            ManagedDoubleRNSElRepresentation::Zero => {
                return None;
            }
        }
    }

    ///
    /// Returns the representation of the given element w.r.t. the multiplicative basis, possibly computing
    /// this representation if it is not available. If the element is zero, `None` is returned.
    /// 
    pub fn to_doublerns<'a>(&self, value: &'a ManagedDoubleRNSEl<NumberRing, A>) -> Option<&'a DoubleRNSEl<NumberRing, A>> {
        match value.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::Sum(sum_repr) => {
                drop(sum_repr);
                let mut sum_repr_lock = value.internal.sum_repr.write().unwrap();
                // if some other thread already cleared `sum_repr` between unlocking and relocking
                if sum_repr_lock.is_none() {
                    drop(sum_repr_lock);
                    return self.to_doublerns(value);
                }
                let sum_repr = std::mem::replace(&mut *sum_repr_lock, None).unwrap();
                let mut result = sum_repr.1;
                self.base.add_assign(&mut result, self.base.do_fft(sum_repr.0));
                // no other thread is able to update this, since the previous call to `get_repr()` would alway return `Sum` (or run
                // after we unlocked `sum_repr_lock`)
                value.internal.double_rns_repr.set(result).ok().unwrap();
                // keep the `sum_repr_lock` until we initialized `small_basis_repr`, otherwise threads querying this in the meantime
                // might think the element stores zero
                drop(sum_repr_lock);
                return Some(value.internal.double_rns_repr.get().unwrap());
            },
            ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) | ManagedDoubleRNSElRepresentation::Both(_, double_rns_repr) => {
                return Some(double_rns_repr);
            },
            ManagedDoubleRNSElRepresentation::SmallBasis(small_basis_repr) => {
                let result = self.base.do_fft(self.base.clone_el_non_fft(small_basis_repr));
                // here another thread might have set `double_rns_repr` in the meantime, so this might return `Err(_)`
                _ = value.internal.double_rns_repr.set(result);
                return Some(value.internal.double_rns_repr.get().unwrap());
            },
            ManagedDoubleRNSElRepresentation::Zero => {
                return None;
            }
        }
    }

    fn new_element_sum(&self, small_basis_part: SmallBasisEl<NumberRing, A>, double_rns_part: DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A> {
        ManagedDoubleRNSEl {
            internal: Arc::new(DoubleRNSElInternal {
                small_basis_repr: OnceLock::new(),
                double_rns_repr: OnceLock::new(),
                sum_repr: RwLock::new(Some((small_basis_part, double_rns_part)))
            })
        }
    }

    pub fn from_small_basis_repr(&self, small_basis_repr: SmallBasisEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A> {
        ManagedDoubleRNSEl {
            internal: Arc::new(DoubleRNSElInternal {
                small_basis_repr: {
                    let result = OnceLock::new();
                    result.set(small_basis_repr).ok().unwrap();
                    result
                },
                double_rns_repr: OnceLock::new(),
                sum_repr: RwLock::new(None)
            })
        }
    }

    pub fn from_double_rns_repr(&self, double_rns_repr: DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A> {
        ManagedDoubleRNSEl {
            internal: Arc::new(DoubleRNSElInternal {
                small_basis_repr: OnceLock::new(),
                double_rns_repr: {
                    let result = OnceLock::new();
                    result.set(double_rns_repr).ok().unwrap();
                    result
                },
                sum_repr: RwLock::new(None)
            })
        }
    }

    fn new_element_both(&self, small_basis_repr: SmallBasisEl<NumberRing, A>, double_rns_repr: DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A> {
        ManagedDoubleRNSEl {
            internal: Arc::new(DoubleRNSElInternal {
                small_basis_repr: {
                    let result = OnceLock::new();
                    result.set(small_basis_repr).ok().unwrap();
                    result
                },
                double_rns_repr: {
                    let result = OnceLock::new();
                    result.set(double_rns_repr).ok().unwrap();
                    result
                },
                sum_repr: RwLock::new(None)
            })
        }
    }

    fn apply_linear_operation<F_coeff_bin, F_doublerns_bin, F_coeff_un, F_doublerns_un>(
        &self, 
        lhs: &ManagedDoubleRNSEl<NumberRing, A>, 
        rhs: &ManagedDoubleRNSEl<NumberRing, A>, 
        f1: F_coeff_bin, 
        f2: F_doublerns_bin, 
        f3: F_coeff_un, 
        f4: F_doublerns_un
    ) -> ManagedDoubleRNSEl<NumberRing, A> 
        where F_coeff_bin: FnOnce(&mut SmallBasisEl<NumberRing, A>, &SmallBasisEl<NumberRing, A>),
            F_doublerns_bin: FnOnce(&mut DoubleRNSEl<NumberRing, A>, &DoubleRNSEl<NumberRing, A>),
            F_coeff_un: FnOnce(&mut SmallBasisEl<NumberRing, A>),
            F_doublerns_un: FnOnce(&mut DoubleRNSEl<NumberRing, A>),
    {
        match (lhs.internal.get_repr(), rhs.internal.get_repr()) {
            (_, ManagedDoubleRNSElRepresentation::Zero) => self.clone_el(lhs),
            (ManagedDoubleRNSElRepresentation::Zero, ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) => {
                let mut result_fft = self.base.clone_el(rhs_double_rns_repr);
                f4(&mut result_fft);
                return self.from_double_rns_repr(result_fft);
            },
            (ManagedDoubleRNSElRepresentation::Zero, ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) => {
                let mut result_coeff = self.base.clone_el_non_fft(rhs_small_basis_repr);
                f3(&mut result_coeff);
                return self.from_small_basis_repr(result_coeff);
            },
            (ManagedDoubleRNSElRepresentation::Zero, ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(&rhs_sum_repr.1);
                let mut result_coeff = self.base.clone_el_non_fft(&rhs_sum_repr.0);
                f3(&mut result_coeff);
                f4(&mut result_fft);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::Zero, ManagedDoubleRNSElRepresentation::Both(rhs_small_basis_repr, rhs_double_rns_repr)) => {
                let mut result_fft = self.base.clone_el(rhs_double_rns_repr);
                let mut result_coeff = self.base.clone_el_non_fft(rhs_small_basis_repr);
                f3(&mut result_coeff);
                f4(&mut result_fft);
                return self.new_element_both(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::Sum(lhs_sum_repr), ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(&lhs_sum_repr.1);
                let mut result_coeff = self.base.clone_el_non_fft(&lhs_sum_repr.0);
                f1(&mut result_coeff, &rhs_sum_repr.0);
                f2(&mut result_fft, &rhs_sum_repr.1);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::Sum(lhs_sum_repr), ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) => {
                let mut result_coeff = self.base.clone_el_non_fft(&lhs_sum_repr.0);
                let result_fft = self.base.clone_el(&lhs_sum_repr.1);
                f1(&mut result_coeff, rhs_small_basis_repr);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::Sum(lhs_sum_repr), ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) => {
                let result_coeff = self.base.clone_el_non_fft(&lhs_sum_repr.0);
                let mut result_fft = self.base.clone_el(&lhs_sum_repr.1);
                f2(&mut result_fft, rhs_double_rns_repr);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::Sum(lhs_sum_repr), ManagedDoubleRNSElRepresentation::Both(rhs_small_basis_repr, _)) => {
                let mut result_coeff = self.base.clone_el_non_fft(&lhs_sum_repr.0);
                let result_fft = self.base.clone_el(&lhs_sum_repr.1);
                f1(&mut result_coeff, rhs_small_basis_repr);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::SmallBasis(lhs_small_basis_repr), ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(&rhs_sum_repr.1);
                let mut result_coeff = self.base.clone_el_non_fft(lhs_small_basis_repr);
                f1(&mut result_coeff, &rhs_sum_repr.0);
                f4(&mut result_fft);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::SmallBasis(lhs_small_basis_repr), ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) | 
                (ManagedDoubleRNSElRepresentation::SmallBasis(lhs_small_basis_repr), ManagedDoubleRNSElRepresentation::Both(rhs_small_basis_repr, _)) | 
                (ManagedDoubleRNSElRepresentation::Both(lhs_small_basis_repr, _), ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) => 
            {
                let mut result_coeff = self.base.clone_el_non_fft(lhs_small_basis_repr);
                f1(&mut result_coeff, rhs_small_basis_repr);
                return self.from_small_basis_repr(result_coeff);
            },
            (ManagedDoubleRNSElRepresentation::SmallBasis(lhs_small_basis_repr), ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) => {
                let result_coeff = self.base.clone_el_non_fft(lhs_small_basis_repr);
                let mut result_fft = self.base.clone_el(rhs_double_rns_repr);
                f4(&mut result_fft);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::DoubleRNS(lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(lhs_double_rns_repr);
                let mut result_coeff = self.base.clone_el_non_fft(&rhs_sum_repr.0);
                f2(&mut result_fft, &rhs_sum_repr.1);
                f3(&mut result_coeff);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::DoubleRNS(lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) => {
                let mut result_coeff = self.base.clone_el_non_fft(rhs_small_basis_repr);
                let result_fft = self.base.clone_el(lhs_double_rns_repr);
                f3(&mut result_coeff);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::DoubleRNS(lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) | 
                (ManagedDoubleRNSElRepresentation::DoubleRNS(lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::Both(_, rhs_double_rns_repr)) | 
                (ManagedDoubleRNSElRepresentation::Both(_, lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) =>
            {
                let mut result_fft = self.base.clone_el(lhs_double_rns_repr);
                f2(&mut result_fft, rhs_double_rns_repr);
                return self.from_double_rns_repr(result_fft);
            },
            (ManagedDoubleRNSElRepresentation::Both(lhs_small_basis_repr, _), ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(&rhs_sum_repr.1);
                let mut result_coeff = self.base.clone_el_non_fft(lhs_small_basis_repr);
                f1(&mut result_coeff, &rhs_sum_repr.0);
                f4(&mut result_fft);
                return self.new_element_sum(result_coeff, result_fft);
            },
            (ManagedDoubleRNSElRepresentation::Both(lhs_small_basis_repr, lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::Both(rhs_small_basis_repr, rhs_double_rns_repr)) => {
                let mut result_fft = self.base.clone_el(lhs_double_rns_repr);
                let mut result_coeff = self.base.clone_el_non_fft(lhs_small_basis_repr);
                f1(&mut result_coeff, rhs_small_basis_repr);
                f2(&mut result_fft, rhs_double_rns_repr);
                return self.new_element_both(result_coeff, result_fft);
            },
        }
    }
}

impl<NumberRing, A> PreparedMultiplicationRing for ManagedDoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone
{
    type PreparedMultiplicant = Self::Element;

    fn mul_prepared(&self, lhs: &Self::PreparedMultiplicant, rhs: &Self::PreparedMultiplicant) -> Self::Element {
        self.mul_ref(lhs, rhs)
    }

    fn prepare_multiplicant(&self, x: &Self::Element) -> Self::PreparedMultiplicant {
        _ = self.to_doublerns(x);
        return self.clone_el(x);
    }

    fn inner_product_prepared<'a, I>(&self, parts: I) -> Self::Element
        where I: IntoIterator<Item = (&'a Self::PreparedMultiplicant, &'a Self::PreparedMultiplicant)>,
            Self: 'a
    {
        <_ as ComputeInnerProduct>::inner_product_ref(self, parts.into_iter())
    }
}

impl<NumberRing, A> BGFVCiphertextRing for ManagedDoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone
{
    type NumberRing = NumberRing;

    fn number_ring(&self) -> &NumberRing {
        self.base.number_ring()
    }

    fn drop_rns_factor(&self, drop_rns_factors: &[usize]) -> Self {
        let new_base = self.base.drop_rns_factor(drop_rns_factors);
        Self {
            zero: new_base.get_ring().zero_non_fft(),
            base: new_base.into()
        }
    }
    
    fn drop_rns_factor_element(&self, from: &Self, dropped_rns_factors: &[usize], value: Self::Element) -> Self::Element {
        match value.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::Zero => self.zero(),
            ManagedDoubleRNSElRepresentation::Sum(sum_repr) => self.new_element_sum(
                self.base.drop_rns_factor_non_fft_element(&from.base, dropped_rns_factors, &sum_repr.0),
                self.base.drop_rns_factor_element(&from.base, dropped_rns_factors, &sum_repr.1)
            ),
            ManagedDoubleRNSElRepresentation::SmallBasis(small_basis_repr) => self.from_small_basis_repr(
                self.base.drop_rns_factor_non_fft_element(&from.base, dropped_rns_factors, small_basis_repr)
            ),
            ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) => self.from_double_rns_repr(
                self.base.drop_rns_factor_element(&from.base, dropped_rns_factors, double_rns_repr)
            ),
            ManagedDoubleRNSElRepresentation::Both(small_basis_repr, double_rns_repr) => self.new_element_both(
                self.base.drop_rns_factor_non_fft_element(&from.base, dropped_rns_factors, small_basis_repr),
                self.base.drop_rns_factor_element(&from.base, dropped_rns_factors, double_rns_repr)
            )
        }
    }

    fn drop_rns_factor_prepared(&self, from: &Self, drop_factors: &[usize], value: Self::PreparedMultiplicant) -> Self::PreparedMultiplicant {
        self.drop_rns_factor_element(from, drop_factors, value)
    }

    fn small_generating_set_len(&self) -> usize {
        self.rank()
    }

    fn as_representation_wrt_small_generating_set<V>(&self, x: &Self::Element, mut output: SubmatrixMut<V, zn_64::ZnEl>)
        where V: AsPointerToSlice<zn_64::ZnEl>
    {
        let matrix = self.base.as_matrix_wrt_small_basis(self.to_small_basis(x).unwrap_or(&self.zero));
        assert_eq!(output.row_count(), matrix.row_count());
        assert_eq!(output.col_count(), matrix.col_count());
        for i in 0..matrix.row_count() {
            for j in 0..matrix.col_count() {
                *output.at_mut(i, j) = *matrix.at(i, j);
            }
        }
    }

    ///
    /// Computes a subset of the rows of the representation that would be returned by
    /// [`BGFVCiphertextRing::as_representation_wrt_small_generating_set()`]. Since not all rows
    /// have to be computed, this may be faster than `as_representation_wrt_small_generating_set()`.
    /// 
    /// However, this also means that this function will not cache the element in small-basis
    /// representation, if that was computed (unlike `as_representation_wrt_small_generating_set()`).
    /// Thus, if you want to access the element in small-basis representation afterwards anyway,
    /// it will be faster to use `as_representation_wrt_small_generating_set()`.
    /// 
    fn partial_representation_wrt_small_generating_set<V>(&self, x: &Self::Element, row_indices: &[usize], mut output: SubmatrixMut<V, zn_64::ZnEl>)
        where V: AsPointerToSlice<zn_64::ZnEl>
    {
        assert_eq!(output.row_count(), row_indices.len());
        assert_eq!(output.col_count(), self.base.rank());

        match x.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) => self.base.undo_fft_partial(double_rns_repr, row_indices, output),
            ManagedDoubleRNSElRepresentation::Sum(parts) => {
                let small_basis_part = &parts.0;
                let double_rns_part = &parts.1;
                self.base.undo_fft_partial(double_rns_part, row_indices, output.reborrow());
                let matrix = self.base.as_matrix_wrt_small_basis(small_basis_part);
                for (i_out, i_in) in row_indices.iter().enumerate() {
                    for j in 0..matrix.col_count() {
                        self.base.base_ring().at(*i_in).add_assign(output.at_mut(i_out, j), *matrix.at(*i_in, j));
                    }
                }
            },
            ManagedDoubleRNSElRepresentation::Both(small_basis_repr, _) | ManagedDoubleRNSElRepresentation::SmallBasis(small_basis_repr) => {   
                let matrix = self.base.as_matrix_wrt_small_basis(small_basis_repr);
                for (i_out, i_in) in row_indices.iter().enumerate() {
                    for j in 0..matrix.col_count() {
                        *output.at_mut(i_out, j) = *matrix.at(*i_in, j);
                    }
                }
            },
            ManagedDoubleRNSElRepresentation::Zero => {
                for (i_out, i_in) in row_indices.iter().enumerate() {
                    for j in 0..self.base.rank() {
                        *output.at_mut(i_out, j) = self.base.base_ring().at(*i_in).zero();
                    }
                }
            }
        }

    }

    fn from_representation_wrt_small_generating_set<V>(&self, data: Submatrix<V, zn_64::ZnEl>) -> Self::Element
        where V: AsPointerToSlice<zn_64::ZnEl>
    {
        let mut x = self.base.zero_non_fft();
        let mut x_as_matrix = self.base.as_matrix_wrt_small_basis_mut(&mut x);
        assert_eq!(data.row_count(), x_as_matrix.row_count());
        assert_eq!(data.col_count(), x_as_matrix.col_count());
        for i in 0..data.row_count() {
            for j in 0..data.col_count() {
                *x_as_matrix.at_mut(i, j) = self.base.base_ring().at(i).clone_el(data.at(i, j));
            }
        }
        return self.from_small_basis_repr(x);
    }
}

impl<NumberRing, A> CyclotomicRing for ManagedDoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HECyclotomicNumberRing,
        A: Allocator + Clone
{
    fn m(&self) -> usize {
        self.base.m()
    }

    fn apply_galois_action(&self, el: &Self::Element, g: CyclotomicGaloisGroupEl) -> Self::Element {
        let result = if let Some(value) = self.to_doublerns(el) {
            self.base.apply_galois_action(&*value, g)
        } else {
            return self.zero();
        };
        return self.from_double_rns_repr(result);
    }
}

impl<NumberRing, A> PartialEq for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn eq(&self, other: &Self) -> bool {
        self.base == other.base
    }
}

impl<NumberRing, A> RingBase for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type Element = ManagedDoubleRNSEl<NumberRing, A>;

    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        ManagedDoubleRNSEl { internal: val.internal.clone() }
    }

    fn eq_el(&self, lhs: &Self::Element, rhs: &Self::Element) -> bool {
        match (lhs.internal.get_repr(), rhs.internal.get_repr()) {
            (ManagedDoubleRNSElRepresentation::Zero, _) | (_, ManagedDoubleRNSElRepresentation::Zero) => self.is_zero(lhs),
            (ManagedDoubleRNSElRepresentation::SmallBasis(_), _) | (_, ManagedDoubleRNSElRepresentation::SmallBasis(_)) => self.base.eq_el_non_fft(&*self.to_small_basis(lhs).unwrap(), &*self.to_small_basis(rhs).unwrap()),
            _ => self.base.eq_el(&*self.to_doublerns(lhs).unwrap(), &*self.to_doublerns(rhs).unwrap())
        }
    }

    fn is_zero(&self, value: &Self::Element) -> bool {
        match value.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::Zero => true,
            ManagedDoubleRNSElRepresentation::Sum(_) | ManagedDoubleRNSElRepresentation::SmallBasis(_) | ManagedDoubleRNSElRepresentation::Both(_, _) => self.base.eq_el_non_fft(&*self.to_small_basis(value).unwrap(), &self.zero),
            ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) => self.base.is_zero(&double_rns_repr)
        }
    }

    fn zero(&self) -> Self::Element {
        ManagedDoubleRNSEl { internal: Arc::new(DoubleRNSElInternal { 
            sum_repr: RwLock::new(None), 
            small_basis_repr: OnceLock::new(), 
            double_rns_repr: OnceLock::new()
        }) }
    }
    
    fn dbg_within<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>, env: EnvBindingStrength) -> std::fmt::Result {
        if let Some(nonzero) = self.to_doublerns(value) {
            self.base.dbg_within(&*nonzero, out, env)
        } else {
            write!(out, "0")
        }
    }

    fn square(&self, value: &mut Self::Element) {
        let mut result = if let Some(nonzero) = self.to_doublerns(value) {
            self.base.clone_el(&*nonzero)
        } else {
            return
        };
        self.base.square(&mut result);
        *value = self.from_double_rns_repr(result);
    }

    fn negate(&self, value: Self::Element) -> Self::Element {
        self.apply_linear_operation(
            &self.zero(), 
            &value,
            |_, _| unreachable!(),
            |_, _| unreachable!(),
            |a| self.base.negate_inplace_non_fft(a),
            |a| self.base.negate_inplace(a)
        )
    }
    
    #[instrument(skip_all)]
    fn mul_int_ref(&self, lhs: &Self::Element, rhs: i32) -> Self::Element {
        self.apply_linear_operation(
            &self.zero(), 
            lhs,
            |_, _| unreachable!(),
            |_, _| unreachable!(),
            |a| self.base.mul_scalar_assign_non_fft(a, &self.base_ring().int_hom().map(rhs)),
            |a| self.base.mul_assign_int(a, rhs)
        )
    }

    fn add_ref(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        self.apply_linear_operation(
            lhs, 
            rhs,
            |a, b| self.base.add_assign_non_fft(a, b),
            |a, b| self.base.add_assign_ref(a, b),
            |_| {},
            |_| {}
        )
    }

    fn sub_ref(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        self.apply_linear_operation(
            lhs,
            rhs,
            |a, b| self.base.sub_assign_non_fft(a, b),
            |a, b| self.base.sub_assign_ref(a, b),
            |a| self.base.negate_inplace_non_fft(a),
            |a| self.base.negate_inplace(a)
        )
    }

    fn mul_ref(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        let result = if let (Some(lhs), Some(rhs)) = (self.to_doublerns(lhs), self.to_doublerns(rhs)) {
            self.base.mul_ref(&*lhs, &*rhs)
        } else {
            return self.zero();
        };
        return self.from_double_rns_repr(result);
    }

    fn pow_gen<R: IntegerRingStore>(&self, x: Self::Element, power: &El<R>, integers: R) -> Self::Element 
        where R::Type: IntegerRing
    {
        let result = if let Some(nonzero) = self.to_doublerns(&x) {
            self.base.pow_gen(self.base.clone_el(&*nonzero), power, integers)
        } else {
            return self.zero();
        };
        return self.from_double_rns_repr(result);
    }

    fn characteristic<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        self.base_ring().characteristic(ZZ)
    }

    fn add_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        lhs.internal = self.add_ref(lhs, rhs).internal;
    }

    fn add_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        lhs.internal = self.add_ref(lhs, &rhs).internal;
    }

    fn sub_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        lhs.internal = self.sub_ref(lhs, rhs).internal;
    }

    fn negate_inplace(&self, lhs: &mut Self::Element) {
        lhs.internal = self.negate(self.clone_el(lhs)).internal;
    }

    fn mul_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        lhs.internal = self.mul_ref(lhs, &rhs).internal;
    }

    fn mul_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        lhs.internal = self.mul_ref(lhs, rhs).internal;
    }

    fn is_commutative(&self) -> bool { true }
    fn is_noetherian(&self) -> bool { true }
    fn is_approximate(&self) -> bool { false }

    fn from_int(&self, value: i32) -> Self::Element {
        self.from(self.base_ring().get_ring().from_int(value))
    }

    fn dbg<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>) -> std::fmt::Result {
        self.dbg_within(value, out, EnvBindingStrength::Weakest)
    }

    fn sub_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        lhs.internal = self.sub_ref(lhs, &rhs).internal;
    }

    fn mul_assign_int(&self, lhs: &mut Self::Element, rhs: i32) {
        lhs.internal = self.mul_int(self.clone_el(lhs), rhs).internal;
    }

    fn mul_int(&self, lhs: Self::Element, rhs: i32) -> Self::Element {
        self.mul_int_ref(&lhs, rhs)
    }

    fn sub_self_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        lhs.internal = self.sub_ref(&rhs, lhs).internal;
    }

    fn sub_self_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        lhs.internal = self.sub_ref(rhs, lhs).internal;
    }

    fn add_ref_fst(&self, lhs: &Self::Element, rhs: Self::Element) -> Self::Element {
        self.add_ref(lhs, &rhs)
    }

    fn add_ref_snd(&self, lhs: Self::Element, rhs: &Self::Element) -> Self::Element {
        self.add_ref(&lhs, rhs)
    }

    fn add(&self, lhs: Self::Element, rhs: Self::Element) -> Self::Element {
        self.add_ref(&lhs, &rhs)
    }

    fn sub_ref_fst(&self, lhs: &Self::Element, rhs: Self::Element) -> Self::Element {
        self.sub_ref(lhs, &rhs)
    }

    fn sub_ref_snd(&self, lhs: Self::Element, rhs: &Self::Element) -> Self::Element {
        self.sub_ref(&lhs, rhs)
    }

    fn sub(&self, lhs: Self::Element, rhs: Self::Element) -> Self::Element {
        self.sub_ref(&lhs, &rhs)
    }

    fn mul_ref_fst(&self, lhs: &Self::Element, rhs: Self::Element) -> Self::Element {
        self.mul_ref(lhs, &rhs)
    }

    fn mul_ref_snd(&self, lhs: Self::Element, rhs: &Self::Element) -> Self::Element {
        self.mul_ref(&lhs, rhs)
    }

    fn mul(&self, lhs: Self::Element, rhs: Self::Element) -> Self::Element {
        self.mul_ref(&lhs, &rhs)
    }
}

impl<NumberRing, A> ComputeInnerProduct for ManagedDoubleRNSRingBase<NumberRing, A> 
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    default fn inner_product<I: Iterator<Item = (Self::Element, Self::Element)>>(&self, els: I) -> Self::Element {
        let data = els.collect::<Vec<_>>();
        return self.inner_product_ref(data.iter().map(|(l, r)| (l, r)));
    }

    default fn inner_product_ref<'a, I: Iterator<Item = (&'a Self::Element, &'a Self::Element)>>(&self, els: I) -> Self::Element
        where Self: 'a
    {
        self.from_double_rns_repr(<_ as ComputeInnerProduct>::inner_product_ref(
            &self.base, 
            els.map(|(l, r)| (self.to_doublerns(l), self.to_doublerns(r)))
                .filter_map(|(l, r)| l.and_then(|l| r.map(|r| (l, r))))
        ))
    }

    default fn inner_product_ref_fst<'a, I: Iterator<Item = (&'a Self::Element, Self::Element)>>(&self, els: I) -> Self::Element
        where Self::Element: 'a,
            Self: 'a
    {
        let data = els.collect::<Vec<_>>();
        return self.inner_product_ref(data.iter().map(|(l, r)| (*l, r)));
    }
}

impl<NumberRing, A> RingExtension for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type BaseRing = <DoubleRNSRingBase<NumberRing, A> as RingExtension>::BaseRing;

    fn base_ring<'a>(&'a self) -> &'a Self::BaseRing {
        self.base.base_ring()
    }

    fn from(&self, x: El<Self::BaseRing>) -> Self::Element {
        let result_fft = self.base.from(self.base_ring().clone_el(&x));
        let result_coeff = self.base.from_non_fft(x);
        return self.new_element_both(result_coeff, result_fft);
    }

    fn mul_assign_base(&self, lhs: &mut Self::Element, rhs: &El<Self::BaseRing>) {
        *lhs = self.apply_linear_operation(
            &self.zero(), 
            lhs,
            |_, _| unreachable!(),
            |_, _| unreachable!(),
            |a| self.base.mul_scalar_assign_non_fft(a, rhs),
            |a| self.base.mul_assign_base(a, rhs)
        )
    }
}

impl<NumberRing, A> FreeAlgebra for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type VectorRepresentation<'a> = DoubleRNSRingBaseElVectorRepresentation<'a, NumberRing, A> 
        where Self: 'a;

    fn canonical_gen(&self) -> Self::Element {
        let result = self.base.canonical_gen();
        return self.from_double_rns_repr(result);
    }

    fn rank(&self) -> usize { 
        self.base.rank()
    }

    fn wrt_canonical_basis<'a>(&'a self, el: &'a Self::Element) -> Self::VectorRepresentation<'a> {
        if let Some(result) = self.to_small_basis(el) {
            self.base.wrt_canonical_basis_non_fft(self.base.clone_el_non_fft(&result))
        } else {
            self.base.wrt_canonical_basis_non_fft(self.base.clone_el_non_fft(&self.zero))
        }
    }

    fn from_canonical_basis<V>(&self, vec: V) -> Self::Element
        where V: IntoIterator<Item = El<Self::BaseRing>>,
            V::IntoIter: DoubleEndedIterator
    {
        let result = self.base.from_canonical_basis_non_fft(vec);
        return self.from_small_basis_repr(result);
    }
}

impl<NumberRing, A> FiniteRingSpecializable for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn specialize<O: FiniteRingOperation<Self>>(op: O) -> O::Output {
        op.execute()
    }
}

impl<NumberRing, A> FiniteRing for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    type ElementsIter<'a> = std::iter::Map<<DoubleRNSRingBase<NumberRing, A> as FiniteRing>::ElementsIter<'a>, fn(DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A>>
        where Self: 'a;

    fn elements<'a>(&'a self) -> Self::ElementsIter<'a> {
        fn from_doublerns<NumberRing, A>(x: DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A>
            where NumberRing: HENumberRing,
                A: Allocator + Clone
        {
            return ManagedDoubleRNSEl { internal: Arc::new(DoubleRNSElInternal {
                double_rns_repr: {
                    let result = OnceLock::new();
                    result.set(x).ok().unwrap();
                    result
                },
                sum_repr: RwLock::new(None),
                small_basis_repr: OnceLock::new()
            })};
        }
        self.base.elements().map(from_doublerns)
    }

    fn random_element<G: FnMut() -> u64>(&self, rng: G) -> <Self as RingBase>::Element {
        return self.from_double_rns_repr(self.base.random_element(rng));
    }

    fn size<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        self.base.size(ZZ)
    }
}

impl<NumberRing, A> SerializableElementRing for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: HENumberRing,
        A: Allocator + Clone
{
    fn serialize<S>(&self, el: &Self::Element, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        if serializer.is_human_readable() {
            return SerializableNewtype::new("ManagedDoubleRNSEl", &SerializableSmallBasisElWithRing::new(&self.base, self.to_small_basis(el).unwrap_or(&self.zero))).serialize(serializer);
        }
        if let ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) = el.internal.get_repr() {
            serializer.serialize_newtype_variant("ManagedDoubleRNSEl", 0, "DoubleRNS", &SerializeWithRing::new(double_rns_repr, RingRef::new(&self.base)))
        } else if let Some(small_basis_repr) = self.to_small_basis(el) {
            serializer.serialize_newtype_variant("ManagedDoubleRNSEl", 1, "SmallBasis", &SerializableSmallBasisElWithRing::new(&self.base, small_basis_repr))
        } else {
            serializer.serialize_newtype_variant("ManagedDoubleRNSEl", 2, "Zero", &())
        }
    }

    fn deserialize<'de, D>(&self, deserializer: D) -> Result<Self::Element, D::Error>
        where D: serde::Deserializer<'de>
    {
        use serde::de::EnumAccess;
        use serde::de::VariantAccess;

        if deserializer.is_human_readable() {
            return DeserializeSeedNewtype::new("ManagedDoubleRNSEl", DeserializeSeedSmallBasisElWithRing::new(&self.base)).deserialize(deserializer).map(|small_basis_repr| self.from_small_basis_repr(small_basis_repr));
        }

        struct ResultVisitor<'a, NumberRing, A>
            where NumberRing: HENumberRing,
                A: Allocator + Clone
        {
            ring: &'a ManagedDoubleRNSRingBase<NumberRing, A>,
        }
        impl<'a, 'de, NumberRing, A> serde::de::Visitor<'de> for ResultVisitor<'a, NumberRing, A>
            where NumberRing: HENumberRing,
                A: Allocator + Clone
        {
            type Value = ManagedDoubleRNSEl<NumberRing, A>;

            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "either ManagedDoubleRNSEl::DoubleRNS, ManagedDoubleRNSEl::SmallBasis or ManagedDoubleRNSEl::Zero")
            }
    
            fn visit_enum<E>(self, data: E) -> Result<Self::Value, E::Error>
                where E: EnumAccess<'de>
            {
                enum Discriminant {
                    DoubleRNS,
                    SmallBasis,
                    Zero
                }
                struct DiscriminantVisitor;
                impl<'de> serde::de::Visitor<'de> for DiscriminantVisitor {
                    type Value = Discriminant;
                    fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                        write!(f, "one of the enum discriminants `DoubleRNS` = 0, `SmallBasis` = 1 or `Zero` = 2")
                    }
                    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                        where E: serde::de::Error
                    {
                        match v {
                            "DoubleRNS" => Ok(Discriminant::DoubleRNS),
                            "SmallBasis" => Ok(Discriminant::SmallBasis),
                            "Zero" => Ok(Discriminant::Zero),
                            _ => Err(serde::de::Error::unknown_variant(v, &["DoubleRNS", "SmallBasis", "Zero"]))
                        }
                    }
                    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
                        where E: serde::de::Error
                    {
                        match v {
                            0 => Ok(Discriminant::DoubleRNS),
                            1 => Ok(Discriminant::SmallBasis),
                            2 => Ok(Discriminant::Zero),
                            _ => Err(serde::de::Error::unknown_variant(format!("{}", v).as_str(), &["0", "1", "2"]))
                        }
                    }
                }
                impl<'de> Deserialize<'de> for Discriminant {
                    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                        where D: serde::Deserializer<'de>
                    {
                        deserializer.deserialize_identifier(DiscriminantVisitor)
                    }
                }
                let (discriminant, variant): (Discriminant, _) = data.variant()?;
                match discriminant {
                    Discriminant::DoubleRNS => variant.newtype_variant_seed(DeserializeWithRing::new(self.ring.unmanaged_ring())).map(|double_rns_repr| self.ring.from_double_rns_repr(double_rns_repr)),
                    Discriminant::SmallBasis => variant.newtype_variant_seed(DeserializeSeedSmallBasisElWithRing::new(self.ring.unmanaged_ring().get_ring())).map(|small_basis_repr| self.ring.from_small_basis_repr(small_basis_repr)),
                    Discriminant::Zero => variant.unit_variant().map(|()| self.ring.zero())
                }
            }
        }
        return deserializer.deserialize_enum("ManagedDoubleRNSEl", &["DoubleRNS", "SmallBasis", "Zero"], ResultVisitor { ring: self });
    }
}

impl<NumberRing, A1, A2, C> CanHomFrom<SingleRNSRingBase<NumberRing, A1, C>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C: ConvolutionAlgorithm<zn_64::ZnBase>
{
    type Homomorphism = <DoubleRNSRingBase<NumberRing, A2> as CanHomFrom<SingleRNSRingBase<NumberRing, A1, C>>>::Homomorphism;

    fn has_canonical_hom(&self, from: &SingleRNSRingBase<NumberRing, A1, C>) -> Option<Self::Homomorphism> {
        self.base.has_canonical_hom(from)
    }

    fn map_in(&self, from: &SingleRNSRingBase<NumberRing, A1, C>, el: <SingleRNSRingBase<NumberRing, A1, C> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        if from.is_zero(&el) {
            return self.zero();
        }
        return self.from_small_basis_repr(self.base.map_in_from_singlerns(from, el, hom));
    }
}

impl<NumberRing, A1, A2> CanHomFrom<DoubleRNSRingBase<NumberRing, A1>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone
{
    type Homomorphism = <DoubleRNSRingBase<NumberRing, A2> as CanHomFrom<DoubleRNSRingBase<NumberRing, A2>>>::Homomorphism;

    fn has_canonical_hom(&self, from: &DoubleRNSRingBase<NumberRing, A1>) -> Option<Self::Homomorphism> {
        self.base.has_canonical_hom(from)
    }

    fn map_in(&self, from: &DoubleRNSRingBase<NumberRing, A1>, el: <DoubleRNSRingBase<NumberRing, A1> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        if from.is_zero(&el) {
            return self.zero();
        }
        return self.from_double_rns_repr(self.base.map_in(from, el, hom));
    }
}

impl<NumberRing, A1, A2> CanHomFrom<ManagedDoubleRNSRingBase<NumberRing, A1>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone
{
    type Homomorphism = <DoubleRNSRingBase<NumberRing, A2> as CanHomFrom<DoubleRNSRingBase<NumberRing, A2>>>::Homomorphism;

    fn has_canonical_hom(&self, from: &ManagedDoubleRNSRingBase<NumberRing, A1>) -> Option<Self::Homomorphism> {
        self.base.has_canonical_hom(&from.base)
    }

    fn map_in_ref(&self, from: &ManagedDoubleRNSRingBase<NumberRing, A1>, el: &<ManagedDoubleRNSRingBase<NumberRing, A1> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        if let Some(el) = from.to_doublerns(el) {
            return self.from_double_rns_repr(self.base.map_in_ref(&from.base, &*el, hom));
        } else {
            self.zero()
        }
    }

    fn map_in(&self, from: &ManagedDoubleRNSRingBase<NumberRing, A1>, el: <ManagedDoubleRNSRingBase<NumberRing, A1> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.map_in_ref(from, &el, hom)
    }
}

impl<NumberRing, A1, A2, C> CanIsoFromTo<SingleRNSRingBase<NumberRing, A1, C>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone,
        C: ConvolutionAlgorithm<zn_64::ZnBase>
{
    type Isomorphism = <DoubleRNSRingBase<NumberRing, A2> as CanIsoFromTo<SingleRNSRingBase<NumberRing, A1, C>>>::Isomorphism;

    fn has_canonical_iso(&self, to: &SingleRNSRingBase<NumberRing, A1, C>) -> Option<Self::Isomorphism> {
        self.base.has_canonical_iso(to)
    }

    fn map_out(&self, to: &SingleRNSRingBase<NumberRing, A1, C>, el: Self::Element, iso: &Self::Isomorphism) -> <SingleRNSRingBase<NumberRing, A1, C> as RingBase>::Element {
        if let Some(el) = self.to_small_basis(&el) {
            self.base.map_out_to_singlerns(to, self.base.clone_el_non_fft(&*&el), iso)
        } else {
            to.zero()
        }
    }
}

impl<NumberRing, A1, A2> CanIsoFromTo<DoubleRNSRingBase<NumberRing, A1>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone
{
    type Isomorphism = <DoubleRNSRingBase<NumberRing, A2> as CanIsoFromTo<DoubleRNSRingBase<NumberRing, A2>>>::Isomorphism;

    fn has_canonical_iso(&self, to: &DoubleRNSRingBase<NumberRing, A1>) -> Option<Self::Isomorphism> {
        self.base.has_canonical_iso(to)
    }

    fn map_out(&self, to: &DoubleRNSRingBase<NumberRing, A1>, el: Self::Element, iso: &Self::Isomorphism) -> <DoubleRNSRingBase<NumberRing, A1> as RingBase>::Element {
        if let Some(el) = self.to_doublerns(&el) {
            self.base.map_out(to, self.base.clone_el(&*&el), iso)
        } else {
            to.zero()
        }
    }
}

impl<NumberRing, A1, A2> CanIsoFromTo<ManagedDoubleRNSRingBase<NumberRing, A1>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: HECyclotomicNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone
{
    type Isomorphism = <DoubleRNSRingBase<NumberRing, A1> as CanHomFrom<DoubleRNSRingBase<NumberRing, A2>>>::Homomorphism;

    fn has_canonical_iso(&self, to: &ManagedDoubleRNSRingBase<NumberRing, A1>) -> Option<Self::Isomorphism> {
        to.has_canonical_hom(self)
    }

    fn map_out(&self, to: &ManagedDoubleRNSRingBase<NumberRing, A1>, el: Self::Element, iso: &Self::Isomorphism) -> <ManagedDoubleRNSRingBase<NumberRing, A1> as RingBase>::Element {
        to.map_in(self, el, iso)
    }
}

#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use crate::number_ring::pow2_cyclotomic::*;
#[cfg(test)]
use crate::DefaultConvolution;

#[cfg(test)]
fn ring_and_elements() -> (ManagedDoubleRNSRing<Pow2CyclotomicNumberRing>, Vec<El<ManagedDoubleRNSRing<Pow2CyclotomicNumberRing>>>) {
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let ring = ManagedDoubleRNSRingBase::new(Pow2CyclotomicNumberRing::new(16), rns_base);
    
    let elements = vec![
        ring.zero(),
        ring.one(),
        ring.neg_one(),
        ring.int_hom().map(17),
        ring.int_hom().map(97),
        ring.canonical_gen(),
        ring.pow(ring.canonical_gen(), 15),
        ring.int_hom().mul_map(ring.canonical_gen(), 17),
        ring.int_hom().mul_map(ring.pow(ring.canonical_gen(), 15), 17),
        ring.add(ring.canonical_gen(), ring.one())
    ];
    return (ring, elements);
}

#[test]
fn test_ring_axioms() {
    let (ring, elements) = ring_and_elements();
    feanor_math::ring::generic_tests::test_ring_axioms(&ring, elements.iter().map(|x| ring.clone_el(x)));
    feanor_math::ring::generic_tests::test_self_iso(&ring, elements.iter().map(|x| ring.clone_el(x)));
}

#[test]
fn test_thread_safe() {
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let ring = Arc::new(ManagedDoubleRNSRingBase::new(Pow2CyclotomicNumberRing::new(16), rns_base));

    let test_element = Arc::new(ring.get_ring().new_element_sum(
        ring.get_ring().base.from_non_fft(ring.get_ring().base.base_ring().int_hom().map(1)), 
        ring.get_ring().base.from(ring.get_ring().base.base_ring().int_hom().map(10))
    ));
    let mut threads = Vec::new();
    let n = 5;
    let barrier = Arc::new(Barrier::new(n));
    for _ in 0..n {
        let barrier = barrier.clone();
        let test_element = test_element.clone();
        let ring = ring.clone();
        threads.push(std::thread::spawn(move || {
            barrier.wait();
            assert_el_eq!(ring, ring.int_hom().map(121), ring.pow(ring.clone_el(&*test_element), 2));
        }))
    }
    for future in threads {
        future.join().unwrap();
    }
}

#[test]
fn test_canonical_hom_from_doublerns() {
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let ring = ManagedDoubleRNSRingBase::new(Pow2CyclotomicNumberRing::new(16), rns_base);

    let doublerns_ring = RingRef::new(&ring.get_ring().base);
    let elements = vec![
        doublerns_ring.zero(),
        doublerns_ring.one(),
        doublerns_ring.neg_one(),
        doublerns_ring.int_hom().map(17),
        doublerns_ring.int_hom().map(97),
        doublerns_ring.canonical_gen(),
        doublerns_ring.pow(doublerns_ring.canonical_gen(), 15),
        doublerns_ring.int_hom().mul_map(doublerns_ring.canonical_gen(), 17),
        doublerns_ring.int_hom().mul_map(doublerns_ring.pow(doublerns_ring.canonical_gen(), 15), 17),
        doublerns_ring.add(doublerns_ring.canonical_gen(), doublerns_ring.one())
    ];

    feanor_math::ring::generic_tests::test_hom_axioms(doublerns_ring, &ring, elements.iter().map(|x| doublerns_ring.clone_el(x)));
}

#[test]
fn test_canonical_hom_from_singlerns() {
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(97), zn_64::Zn::new(193)], BigIntRing::RING);
    let ring = ManagedDoubleRNSRingBase::new(Pow2CyclotomicNumberRing::new(16), rns_base.clone());

    let singlerns_ring = SingleRNSRingBase::<_, _, DefaultConvolution>::new(Pow2CyclotomicNumberRing::new(16), rns_base);
    let elements = vec![
        singlerns_ring.zero(),
        singlerns_ring.one(),
        singlerns_ring.neg_one(),
        singlerns_ring.int_hom().map(97),
        singlerns_ring.int_hom().map(193),
        singlerns_ring.canonical_gen(),
        singlerns_ring.pow(singlerns_ring.canonical_gen(), 15),
        singlerns_ring.int_hom().mul_map(singlerns_ring.canonical_gen(), 97),
        singlerns_ring.int_hom().mul_map(singlerns_ring.pow(singlerns_ring.canonical_gen(), 15), 97),
        singlerns_ring.add(singlerns_ring.canonical_gen(), singlerns_ring.one())
    ];

    feanor_math::ring::generic_tests::test_hom_axioms(&singlerns_ring, &ring, elements.iter().map(|x| singlerns_ring.clone_el(x)));
}

#[test]
fn test_add_result_independent_of_repr() {
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let ring = ManagedDoubleRNSRingBase::new(Pow2CyclotomicNumberRing::new(4), rns_base);
    let base = &ring.get_ring().base;
    let reprs_of_11: [Box<dyn Fn() -> ManagedDoubleRNSEl<_, _>>; 4] = [
        Box::new(|| ring.get_ring().from_small_basis_repr(base.from_non_fft(base.base_ring().int_hom().map(11)))),
        Box::new(|| ring.get_ring().from_double_rns_repr(base.from(base.base_ring().int_hom().map(11)))),
        Box::new(|| ring.get_ring().new_element_sum(base.from_non_fft(base.base_ring().int_hom().map(10)), base.from(base.base_ring().int_hom().map(1)))),
        Box::new(|| ring.get_ring().new_element_both(base.from_non_fft(base.base_ring().int_hom().map(11)), base.from(base.base_ring().int_hom().map(11))))
    ];
    let reprs_of_102: [Box<dyn Fn() -> ManagedDoubleRNSEl<_, _>>; 4] = [
        Box::new(|| ring.get_ring().from_small_basis_repr(base.from_non_fft(base.base_ring().int_hom().map(102)))),
        Box::new(|| ring.get_ring().from_double_rns_repr(base.from(base.base_ring().int_hom().map(102)))),
        Box::new(|| ring.get_ring().new_element_sum(base.from_non_fft(base.base_ring().int_hom().map(100)), base.from(base.base_ring().int_hom().map(2)))),
        Box::new(|| ring.get_ring().new_element_both(base.from_non_fft(base.base_ring().int_hom().map(102)), base.from(base.base_ring().int_hom().map(102))))
    ];
    for a in &reprs_of_11 {
        for b in &reprs_of_102 {
            let x = a();
            assert_el_eq!(RingRef::new(base), base.from_int(22), ring.get_ring().to_doublerns(&ring.add_ref(&x, &x)).unwrap());

            let x = a();
            let y = b();
            assert_el_eq!(RingRef::new(base), base.from_int(113), ring.get_ring().to_doublerns(&ring.add_ref(&x, &y)).unwrap());

            let x = a();
            let y = b();
            assert!(base.eq_el_non_fft(&base.from_non_fft(base.base_ring().int_hom().map(113)), &*ring.get_ring().to_small_basis(&ring.add_ref(&x, &y)).unwrap()));

            let x = a();
            let y = b();
            assert_el_eq!(RingRef::new(base), base.from_int(-91), ring.get_ring().to_doublerns(&ring.sub_ref(&x, &y)).unwrap());

            let x = a();
            let y = b();
            assert!(base.eq_el_non_fft(&base.from_non_fft(base.base_ring().int_hom().map(-91)), &*ring.get_ring().to_small_basis(&ring.sub_ref(&x, &y)).unwrap()));

            let x = a();
            assert_el_eq!(RingRef::new(base), base.from_int(121), ring.get_ring().to_doublerns(&ring.mul_ref(&x, &x)).unwrap());

            let x = a();
            let y = b();
            assert_el_eq!(RingRef::new(base), base.from_int(1122), ring.get_ring().to_doublerns(&ring.mul_ref(&x, &y)).unwrap());

            let x = a();
            let y = b();
            assert!(base.eq_el_non_fft(&base.from_non_fft(base.base_ring().int_hom().map(1122)), &*ring.get_ring().to_small_basis(&ring.mul_ref(&x, &y)).unwrap()));
        }
    }
}

#[test]
fn test_serialization() {
    let (ring, elements) = ring_and_elements();
    feanor_math::serialization::generic_tests::test_serialization(&ring, elements.iter().map(|x| ring.clone_el(x)));

    for a in &elements {
        if ring.is_zero(a) {
            continue;
        }
        let a_small_basis = ring.get_ring().from_small_basis_repr(ring.get_ring().unmanaged_ring().get_ring().clone_el_non_fft(ring.get_ring().to_small_basis(a).unwrap()));
        let serializer = serde_assert::Serializer::builder().is_human_readable(true).build();
        let tokens = ring.get_ring().serialize(&a_small_basis, &serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(true).build();
        let result = ring.get_ring().deserialize(&mut deserializer).unwrap();
        assert_el_eq!(ring, &a_small_basis, &result);
        match result.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::SmallBasis(_) => {},
            _ => panic!("wrong representation")
        };

        let a_small_basis = ring.get_ring().from_small_basis_repr(ring.get_ring().unmanaged_ring().get_ring().clone_el_non_fft(ring.get_ring().to_small_basis(a).unwrap()));
        let serializer = serde_assert::Serializer::builder().is_human_readable(false).build();
        let tokens = ring.get_ring().serialize(&a_small_basis, &serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(false).build();
        let result = ring.get_ring().deserialize(&mut deserializer).unwrap();
        assert_el_eq!(ring, &a_small_basis, &result);
        match result.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::SmallBasis(_) => {},
            _ => panic!("wrong representation")
        };

        let a_doublerns = ring.get_ring().from_double_rns_repr(ring.get_ring().unmanaged_ring().clone_el(ring.get_ring().to_doublerns(a).unwrap()));
        let serializer = serde_assert::Serializer::builder().is_human_readable(true).build();
        let tokens = ring.get_ring().serialize(&a_doublerns, &serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(true).build();
        let result = ring.get_ring().deserialize(&mut deserializer).unwrap();
        assert_el_eq!(ring, &a_doublerns, &result);
        match result.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::SmallBasis(_) => {},
            _ => panic!("wrong representation")
        };

        let a_doublerns = ring.get_ring().from_double_rns_repr(ring.get_ring().unmanaged_ring().clone_el(ring.get_ring().to_doublerns(a).unwrap()));
        let serializer = serde_assert::Serializer::builder().is_human_readable(false).build();
        let tokens = ring.get_ring().serialize(&a_doublerns, &serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(false).build();
        let result = ring.get_ring().deserialize(&mut deserializer).unwrap();
        assert_el_eq!(ring, &a_doublerns, &result);
        match result.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::DoubleRNS(_) => {},
            _ => panic!("wrong representation")
        };
    }
}