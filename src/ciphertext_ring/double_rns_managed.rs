use std::alloc::{Allocator, Global};
use std::sync::*;

use feanor_math::algorithms::convolution::*;
use feanor_math::algorithms::discrete_log::Subgroup;
use feanor_math::algorithms::matmul::ComputeInnerProduct;
use feanor_math::homomorphism::*;
use feanor_math::integer::*;
use feanor_math::matrix::*;
use feanor_math::ring::*;
use feanor_math::rings::extension::*;
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::zn::*;
use feanor_math::seq::VectorView;
use feanor_math::serialization::*;
use feanor_math::specialization::{FiniteRingOperation, FiniteRingSpecializable};
use feanor_serde::newtype_struct::{DeserializeSeedNewtypeStruct, SerializableNewtypeStruct};
use serde::{Deserialize, Serialize};
use serde::de::DeserializeSeed;
use tracing::instrument;

use crate::boo::{Boo, MappedRwLockReadGuardType};
use crate::ciphertext_ring::indices::RNSFactorIndexList;
use crate::ciphertext_ring::RNSFactorCongruence;
use crate::number_ring::galois::*;
use crate::number_ring::{AbstractNumberRing, NumberRingQuotient};

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
/// ```rust
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
/// let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(16);
/// let ring = ManagedDoubleRNSRingBase::new(number_ring, rns_base);
/// // `element` is stored in small-basis representation
/// let element = ring.get_ring()..from_small_basis(ring.get_ring().unmanaged_ring().get_ring().from_non_fft(ring.base_ring().int_hom().map(2)));
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
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    base: DoubleRNSRingBase<NumberRing, A>,
    zero: SmallBasisEl<NumberRing, A>
}

pub type ManagedDoubleRNSRing<NumberRing, A = Global> = RingValue<ManagedDoubleRNSRingBase<NumberRing, A>>;

impl<NumberRing> ManagedDoubleRNSRingBase<NumberRing, Global> 
    where NumberRing: AbstractNumberRing,
{
    pub fn new(number_ring: NumberRing, rns_base: zn_rns::Zn<zn_64::Zn, BigIntRing>) -> RingValue<Self> {
        Self::new_with_alloc(number_ring, rns_base, Global)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ManagedDoubleRNSElRepresentationKind {
    Sum,
    SmallBasis,
    DoubleRNS,
    Both,
    Zero
}

impl ManagedDoubleRNSElRepresentationKind {

    fn joint(self, other: Self) -> Self {
        match (self, other) {
            (ManagedDoubleRNSElRepresentationKind::Zero, other) => other,
            (other, ManagedDoubleRNSElRepresentationKind::Zero) => other,
            (ManagedDoubleRNSElRepresentationKind::Sum, _) => ManagedDoubleRNSElRepresentationKind::Sum,
            (_, ManagedDoubleRNSElRepresentationKind::Sum) => ManagedDoubleRNSElRepresentationKind::Sum,
            (ManagedDoubleRNSElRepresentationKind::SmallBasis, ManagedDoubleRNSElRepresentationKind::DoubleRNS) => ManagedDoubleRNSElRepresentationKind::Sum,
            (ManagedDoubleRNSElRepresentationKind::DoubleRNS, ManagedDoubleRNSElRepresentationKind::SmallBasis) => ManagedDoubleRNSElRepresentationKind::Sum,
            (ManagedDoubleRNSElRepresentationKind::DoubleRNS, ManagedDoubleRNSElRepresentationKind::DoubleRNS) => ManagedDoubleRNSElRepresentationKind::DoubleRNS,
            (ManagedDoubleRNSElRepresentationKind::SmallBasis, ManagedDoubleRNSElRepresentationKind::SmallBasis) => ManagedDoubleRNSElRepresentationKind::SmallBasis,
            (ManagedDoubleRNSElRepresentationKind::Both, other) => other,
            (other, ManagedDoubleRNSElRepresentationKind::Both) => other,
        }
    }
}

enum ManagedDoubleRNSElRepresentation<'a, NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    Sum(Boo<'a, (SmallBasisEl<NumberRing, A>, DoubleRNSEl<NumberRing, A>), MappedRwLockReadGuardType<(SmallBasisEl<NumberRing, A>, DoubleRNSEl<NumberRing, A>)>>),
    SmallBasis(Boo<'a, SmallBasisEl<NumberRing, A>>),
    DoubleRNS(Boo<'a, DoubleRNSEl<NumberRing, A>>),
    Both(Boo<'a, SmallBasisEl<NumberRing, A>>, Boo<'a, DoubleRNSEl<NumberRing, A>>),
    Zero
}

impl<'a, NumberRing, A> ManagedDoubleRNSElRepresentation<'a, NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    fn get_kind(&self) -> ManagedDoubleRNSElRepresentationKind {
        match self {
            ManagedDoubleRNSElRepresentation::Sum(_) => ManagedDoubleRNSElRepresentationKind::Sum,
            ManagedDoubleRNSElRepresentation::SmallBasis(_) => ManagedDoubleRNSElRepresentationKind::SmallBasis,
            ManagedDoubleRNSElRepresentation::DoubleRNS(_) => ManagedDoubleRNSElRepresentationKind::DoubleRNS,
            ManagedDoubleRNSElRepresentation::Both(_, _) => ManagedDoubleRNSElRepresentationKind::Both,
            ManagedDoubleRNSElRepresentation::Zero => ManagedDoubleRNSElRepresentationKind::Zero
        }
    }
}

struct DoubleRNSElInternal<NumberRing, A = Global> 
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    small_basis_repr: OnceLock<SmallBasisEl<NumberRing, A>>,
    double_rns_repr: OnceLock<DoubleRNSEl<NumberRing, A>>,
    sum_repr: RwLock<Option<(SmallBasisEl<NumberRing, A>, DoubleRNSEl<NumberRing, A>)>>
}

impl<NumberRing, A> DoubleRNSElInternal<NumberRing, A> 
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    fn get_repr<'a>(&'a self) -> ManagedDoubleRNSElRepresentation<'a, NumberRing, A> {
        let sum_repr = self.sum_repr.read().unwrap();
        if sum_repr.is_some() {
            return ManagedDoubleRNSElRepresentation::Sum(Boo::GuardedBorrowed(RwLockReadGuard::map(sum_repr, |sum_repr: &Option<_>| sum_repr.as_ref().unwrap())));
        }
        // we can unlock `sum_repr` here, since if `sum_repr` was empty previously, it will always remain empty
        drop(sum_repr);
        if let Some(small_basis_repr) = self.small_basis_repr.get() {
            if let Some(double_rns_repr) = self.double_rns_repr.get() {
                return ManagedDoubleRNSElRepresentation::Both(Boo::Borrowed(small_basis_repr), Boo::Borrowed(double_rns_repr));
            } else {
                return ManagedDoubleRNSElRepresentation::SmallBasis(Boo::Borrowed(small_basis_repr));
            }
        } else if let Some(double_rns_repr) = self.double_rns_repr.get() {
            return ManagedDoubleRNSElRepresentation::DoubleRNS(Boo::Borrowed(double_rns_repr));
        } else {
            return ManagedDoubleRNSElRepresentation::Zero;
        }
    }

    fn into_repr<'a>(self) -> ManagedDoubleRNSElRepresentation<'a, NumberRing, A> {
        let sum_repr = self.sum_repr.into_inner().unwrap();
        if let Some(sum_repr) = sum_repr {
            return ManagedDoubleRNSElRepresentation::Sum(Boo::Owned(sum_repr));
        }
        // we can unlock `sum_repr` here, since if `sum_repr` was empty previously, it will always remain empty
        drop(sum_repr);
        if let Some(small_basis_repr) = self.small_basis_repr.into_inner() {
            if let Some(double_rns_repr) = self.double_rns_repr.into_inner() {
                return ManagedDoubleRNSElRepresentation::Both(Boo::Owned(small_basis_repr), Boo::Owned(double_rns_repr));
            } else {
                return ManagedDoubleRNSElRepresentation::SmallBasis(Boo::Owned(small_basis_repr));
            }
        } else if let Some(double_rns_repr) = self.double_rns_repr.into_inner() {
            return ManagedDoubleRNSElRepresentation::DoubleRNS(Boo::Owned(double_rns_repr));
        } else {
            return ManagedDoubleRNSElRepresentation::Zero;
        }
    }

    fn with_repr<F, R>(self: Arc<Self>, f: F) -> R
        where F: for<'a> FnOnce(ManagedDoubleRNSElRepresentation<'a, NumberRing, A>) -> R
    {
        match Arc::try_unwrap(self) {
            Ok(val) => f(val.into_repr()),
            Err(val) => f(val.get_repr())
        }
    }
}

pub struct ManagedDoubleRNSEl<NumberRing, A = Global> 
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    internal: Arc<DoubleRNSElInternal<NumberRing, A>>
}

impl<NumberRing, A> Clone for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: AbstractNumberRing + Clone,
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
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    pub fn new_with_alloc(number_ring: NumberRing, rns_base: zn_rns::Zn<zn_64::Zn, BigIntRing>, allocator: A) -> RingValue<ManagedDoubleRNSRingBase<NumberRing, A>> {
        let result = DoubleRNSRingBase::new_with_alloc(number_ring, rns_base, allocator);
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
    pub fn unmanaged_ring(&self) -> RingRef<'_, DoubleRNSRingBase<NumberRing, A>> {
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
                return Some(small_basis_repr.unwrap_borrowed());
            },
            ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) => {
                let result = self.base.undo_fft(double_rns_repr.to_owned(|x| self.base.clone_el(x)));
                // here another thread might have set `small_basis_repr` in the meantime, so this might return `Err(_)`
                _ = value.internal.small_basis_repr.set(result);
                return Some(value.internal.small_basis_repr.get().unwrap());
            },
            ManagedDoubleRNSElRepresentation::Zero => {
                return None;
            }
        }
    }

    pub fn element_allocation_size(&self) -> usize {
        2 * self.unmanaged_ring().get_ring().element_allocation_size()
    }

    ///
    /// Returns the representation of the given element w.r.t. the small basis, possibly computing
    /// this representation if it is not available. If the element is zero, `None` is returned.
    /// 
    pub fn into_small_basis(&self, value: ManagedDoubleRNSEl<NumberRing, A>) -> Option<SmallBasisEl<NumberRing, A>> {
        if self.to_small_basis(&value).is_some() {
            value.internal.with_repr(|repr| match repr {
                ManagedDoubleRNSElRepresentation::SmallBasis(small_basis) | ManagedDoubleRNSElRepresentation::Both(small_basis, _) => 
                    Some(small_basis.to_owned(|x| self.base.clone_el_non_fft(x))),
                _ => unreachable!()
            })
        } else {
            None
        }
    }

    ///
    /// Returns the representation of the given element w.r.t. the multiplicative basis, possibly computing
    /// this representation if it is not available. If the element is zero, `None` is returned.
    /// 
    pub fn into_doublerns(&self, value: ManagedDoubleRNSEl<NumberRing, A>) -> Option<DoubleRNSEl<NumberRing, A>> {
        if self.to_doublerns(&value).is_some() {
            value.internal.with_repr(|repr| match repr {
                ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns) | ManagedDoubleRNSElRepresentation::Both(_, double_rns) => 
                    Some(double_rns.to_owned(|x| self.base.clone_el(x))),
                _ => unreachable!()
            })
        } else {
            None
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
                return Some(double_rns_repr.unwrap_borrowed());
            },
            ManagedDoubleRNSElRepresentation::SmallBasis(small_basis_repr) => {
                let result = self.base.do_fft(small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x)));
                // here another thread might have set `double_rns_repr` in the meantime, so this might return `Err(_)`
                _ = value.internal.double_rns_repr.set(result);
                return Some(value.internal.double_rns_repr.get().unwrap());
            },
            ManagedDoubleRNSElRepresentation::Zero => {
                return None;
            }
        }
    }

    fn from_sum(&self, small_basis_part: SmallBasisEl<NumberRing, A>, double_rns_part: DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A> {
        ManagedDoubleRNSEl {
            internal: Arc::new(DoubleRNSElInternal {
                small_basis_repr: OnceLock::new(),
                double_rns_repr: OnceLock::new(),
                sum_repr: RwLock::new(Some((small_basis_part, double_rns_part)))
            })
        }
    }

    pub fn from_small_basis(&self, small_basis_repr: SmallBasisEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A> {
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

    pub fn from_doublerns(&self, double_rns_repr: DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A> {
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

    fn from_both(&self, small_basis_repr: SmallBasisEl<NumberRing, A>, double_rns_repr: DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A> {
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

    fn add_internal(&self, lhs: Arc<DoubleRNSElInternal<NumberRing, A>>, rhs: Arc<DoubleRNSElInternal<NumberRing, A>>) -> Arc<DoubleRNSElInternal<NumberRing, A>> {
        self.apply_linear_operation(
            lhs, 
            rhs,
            |a, b| self.base.add_assign_non_fft(a, b),
            |a, b| self.base.add_assign_ref(a, b),
            |_| {},
            |_| {}
        )
    }

    fn sub_internal(&self, lhs: Arc<DoubleRNSElInternal<NumberRing, A>>, rhs: Arc<DoubleRNSElInternal<NumberRing, A>>) -> Arc<DoubleRNSElInternal<NumberRing, A>> {
        self.apply_linear_operation(
            lhs,
            rhs,
            |a, b| self.base.sub_assign_non_fft(a, b),
            |a, b| self.base.sub_assign_ref(a, b),
            |a| self.base.negate_inplace_non_fft(a),
            |a| self.base.negate_inplace(a)
        )
    }

    fn negate_internal(&self, value: Arc<DoubleRNSElInternal<NumberRing, A>>) -> Arc<DoubleRNSElInternal<NumberRing, A>> {
        self.apply_linear_operation(
            self.zero().internal, 
            value,
            |_, _| unreachable!(),
            |_, _| unreachable!(),
            |a| self.base.negate_inplace_non_fft(a),
            |a| self.base.negate_inplace(a)
        )
    }

    fn mul_base_internal(&self, lhs: Arc<DoubleRNSElInternal<NumberRing, A>>, rhs: &El<zn_rns::Zn<zn_64::Zn, BigIntRing>>) -> Arc<DoubleRNSElInternal<NumberRing, A>> {
        self.apply_linear_operation(
            self.zero().internal, 
            lhs,
            |_, _| unreachable!(),
            |_, _| unreachable!(),
            |a| self.base.mul_scalar_assign_non_fft(a, rhs),
            |a| self.base.mul_assign_base(a, rhs)
        )
    }

    fn apply_linear_operation<F_coeff_bin, F_doublerns_bin, F_coeff_un, F_doublerns_un>(
        &self, 
        lhs: Arc<DoubleRNSElInternal<NumberRing, A>>, 
        rhs: Arc<DoubleRNSElInternal<NumberRing, A>>, 
        f1: F_coeff_bin, 
        f2: F_doublerns_bin, 
        f3: F_coeff_un, 
        f4: F_doublerns_un
    ) -> Arc<DoubleRNSElInternal<NumberRing, A>>
        where F_coeff_bin: FnOnce(&mut SmallBasisEl<NumberRing, A>, &SmallBasisEl<NumberRing, A>),
            F_doublerns_bin: FnOnce(&mut DoubleRNSEl<NumberRing, A>, &DoubleRNSEl<NumberRing, A>),
            F_coeff_un: FnOnce(&mut SmallBasisEl<NumberRing, A>),
            F_doublerns_un: FnOnce(&mut DoubleRNSEl<NumberRing, A>),
    {
        if let ManagedDoubleRNSElRepresentation::Zero = rhs.get_repr() {
            return lhs;
        }
        lhs.with_repr(|lhs| rhs.with_repr(|rhs| match (lhs, rhs) {
            (_, ManagedDoubleRNSElRepresentation::Zero) => unreachable!(),
            (ManagedDoubleRNSElRepresentation::Zero, ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) => {
                let mut result_fft = rhs_double_rns_repr.to_owned(|x| self.base.clone_el(x));
                f4(&mut result_fft);
                return self.from_doublerns(result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::Zero, ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) => {
                let mut result_coeff = rhs_small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x));
                f3(&mut result_coeff);
                return self.from_small_basis(result_coeff).internal;
            },
            (ManagedDoubleRNSElRepresentation::Zero, ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(&rhs_sum_repr.1);
                let mut result_coeff = self.base.clone_el_non_fft(&rhs_sum_repr.0);
                f3(&mut result_coeff);
                f4(&mut result_fft);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::Zero, ManagedDoubleRNSElRepresentation::Both(rhs_small_basis_repr, rhs_double_rns_repr)) => {
                let mut result_fft = rhs_double_rns_repr.to_owned(|x| self.base.clone_el(x));
                let mut result_coeff = rhs_small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x));
                f3(&mut result_coeff);
                f4(&mut result_fft);
                return self.from_both(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::Sum(lhs_sum_repr), ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(&lhs_sum_repr.1);
                let mut result_coeff = self.base.clone_el_non_fft(&lhs_sum_repr.0);
                f1(&mut result_coeff, &rhs_sum_repr.0);
                f2(&mut result_fft, &rhs_sum_repr.1);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::Sum(lhs_sum_repr), ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) => {
                let mut result_coeff = self.base.clone_el_non_fft(&lhs_sum_repr.0);
                let result_fft = self.base.clone_el(&lhs_sum_repr.1);
                f1(&mut result_coeff, &rhs_small_basis_repr);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::Sum(lhs_sum_repr), ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) => {
                let result_coeff = self.base.clone_el_non_fft(&lhs_sum_repr.0);
                let mut result_fft = self.base.clone_el(&lhs_sum_repr.1);
                f2(&mut result_fft, &rhs_double_rns_repr);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::Sum(lhs_sum_repr), ManagedDoubleRNSElRepresentation::Both(rhs_small_basis_repr, _)) => {
                let mut result_coeff = self.base.clone_el_non_fft(&lhs_sum_repr.0);
                let result_fft = self.base.clone_el(&lhs_sum_repr.1);
                f1(&mut result_coeff, &rhs_small_basis_repr);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::SmallBasis(lhs_small_basis_repr), ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(&rhs_sum_repr.1);
                let mut result_coeff = lhs_small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x));
                f1(&mut result_coeff, &rhs_sum_repr.0);
                f4(&mut result_fft);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::SmallBasis(lhs_small_basis_repr), ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) | 
                (ManagedDoubleRNSElRepresentation::SmallBasis(lhs_small_basis_repr), ManagedDoubleRNSElRepresentation::Both(rhs_small_basis_repr, _)) | 
                (ManagedDoubleRNSElRepresentation::Both(lhs_small_basis_repr, _), ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) => 
            {
                let mut result_coeff = lhs_small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x));
                f1(&mut result_coeff, &rhs_small_basis_repr);
                return self.from_small_basis(result_coeff).internal;
            },
            (ManagedDoubleRNSElRepresentation::SmallBasis(lhs_small_basis_repr), ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) => {
                let result_coeff = lhs_small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x));
                let mut result_fft = rhs_double_rns_repr.to_owned(|x| self.base.clone_el(x));
                f4(&mut result_fft);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::DoubleRNS(lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = lhs_double_rns_repr.to_owned(|x| self.base.clone_el(x));
                let mut result_coeff = self.base.clone_el_non_fft(&rhs_sum_repr.0);
                f2(&mut result_fft, &rhs_sum_repr.1);
                f3(&mut result_coeff);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::DoubleRNS(lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::SmallBasis(rhs_small_basis_repr)) => {
                let mut result_coeff = rhs_small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x));
                let result_fft = lhs_double_rns_repr.to_owned(|x| self.base.clone_el(x));
                f3(&mut result_coeff);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::DoubleRNS(lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) | 
                (ManagedDoubleRNSElRepresentation::DoubleRNS(lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::Both(_, rhs_double_rns_repr)) | 
                (ManagedDoubleRNSElRepresentation::Both(_, lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::DoubleRNS(rhs_double_rns_repr)) =>
            {
                let mut result_fft = lhs_double_rns_repr.to_owned(|x| self.base.clone_el(x));
                f2(&mut result_fft, &rhs_double_rns_repr);
                return self.from_doublerns(result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::Both(lhs_small_basis_repr, _), ManagedDoubleRNSElRepresentation::Sum(rhs_sum_repr)) => {
                let mut result_fft = self.base.clone_el(&rhs_sum_repr.1);
                let mut result_coeff = lhs_small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x));
                f1(&mut result_coeff, &rhs_sum_repr.0);
                f4(&mut result_fft);
                return self.from_sum(result_coeff, result_fft).internal;
            },
            (ManagedDoubleRNSElRepresentation::Both(lhs_small_basis_repr, lhs_double_rns_repr), ManagedDoubleRNSElRepresentation::Both(rhs_small_basis_repr, rhs_double_rns_repr)) => {
                let mut result_fft = lhs_double_rns_repr.to_owned(|x| self.base.clone_el(x));
                let mut result_coeff = lhs_small_basis_repr.to_owned(|x| self.base.clone_el_non_fft(x));
                f1(&mut result_coeff, &rhs_small_basis_repr);
                f2(&mut result_fft, &rhs_double_rns_repr);
                return self.from_both(result_coeff, result_fft).internal;
            },
        }))
    }
}

impl<NumberRing, A> PreparedMultiplicationRing for ManagedDoubleRNSRingBase<NumberRing, A> 
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    type PreparedMultiplicant = ();

    fn mul_prepared(&self, lhs: &Self::Element, _: Option<&()>, rhs: &Self::Element, _: Option<&()>) -> Self::Element {
        self.mul_ref(lhs, rhs)
    }

    fn prepare_multiplicant(&self, x: &Self::Element) -> Self::PreparedMultiplicant {
        _ = self.to_doublerns(x);
        return ();
    }

    fn fma_prepared(&self, lhs: &Self::Element, _: Option<&()>, rhs: &Self::Element, _: Option<&()>, dst: Self::Element) -> Self::Element {
        self.fma(lhs, rhs, dst)
    }

    fn inner_product_prepared<'a, I>(&self, parts: I) -> Self::Element
        where I: IntoIterator<Item = (&'a Self::Element, Option<&'a ()>, &'a Self::Element, Option<&'a ()>)>,
            Self: 'a
    {
        <_ as ComputeInnerProduct>::inner_product_ref(self, parts.into_iter().map(|(lhs, _, rhs, _)| (lhs, rhs)))
    }
}

impl<NumberRing, A> BGFVCiphertextRing for ManagedDoubleRNSRingBase<NumberRing, A> 
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    fn drop_rns_factor(&self, drop_rns_factors: &RNSFactorIndexList) -> Self {
        let new_base = self.base.drop_rns_factor(drop_rns_factors);
        Self {
            zero: new_base.zero_non_fft(),
            base: new_base
        }
    }
    
    fn collect_rns_factors<'a, I>(&self, congruences: I) -> Self::Element
        where I: Iterator<Item = super::RNSFactorCongruence<'a, Self, Self::Element>>,
            Self: 'a
    {
        let rns_factors = congruences.collect::<Vec<_>>();
        assert_eq!(self.base_ring().len(), rns_factors.len());
        for (congruence, rns_factor) in rns_factors.iter().zip(self.base_ring().as_iter()) {
            if let RNSFactorCongruence::CongruentTo(other_ring, i, _) = congruence {
                assert!(other_ring.base_ring().at(*i).get_ring() == rns_factor.get_ring());
            }
        }

        let output_format = rns_factors.iter()
            .filter_map(|congruence| if let RNSFactorCongruence::CongruentTo(_, _, el) = congruence { Some(el.internal.get_repr()) } else { None })
            .map(|repr| repr.get_kind())
            .fold(ManagedDoubleRNSElRepresentationKind::Zero, ManagedDoubleRNSElRepresentationKind::joint);

        let congruences_small_basis = rns_factors.iter().map(|congruence| match congruence {
            RNSFactorCongruence::Zero => RNSFactorCongruence::Zero,
            RNSFactorCongruence::CongruentTo(other_ring, i, el) => match other_ring.to_small_basis(el) {
                Some(congruence) => RNSFactorCongruence::CongruentTo(&other_ring.base, *i, congruence),
                None => RNSFactorCongruence::Zero
            }
        });
        let congruences_doublerns = rns_factors.iter().map(|congruence| match congruence {
            RNSFactorCongruence::Zero => RNSFactorCongruence::Zero,
            RNSFactorCongruence::CongruentTo(other_ring, i, el) => match other_ring.to_doublerns(el) {
                Some(congruence) => RNSFactorCongruence::CongruentTo(&other_ring.base, *i, congruence),
                None => RNSFactorCongruence::Zero
            }
        });

        match output_format {
            ManagedDoubleRNSElRepresentationKind::Zero => self.zero(),
            ManagedDoubleRNSElRepresentationKind::Both => self.from_both(
                self.base.collect_rns_factors_non_fft(congruences_small_basis),
                self.base.collect_rns_factors(congruences_doublerns)
            ),
            ManagedDoubleRNSElRepresentationKind::SmallBasis => self.from_small_basis(
                self.base.collect_rns_factors_non_fft(congruences_small_basis)
            ),
            ManagedDoubleRNSElRepresentationKind::DoubleRNS => self.from_doublerns(
                self.base.collect_rns_factors(congruences_doublerns)
            ),
            ManagedDoubleRNSElRepresentationKind::Sum => {
                // collect reprs here because we need refs to the RwMappedLockGuard's content
                let reprs = rns_factors.iter().map(|congruence| match congruence {
                    RNSFactorCongruence::Zero => ManagedDoubleRNSElRepresentation::Zero,
                    RNSFactorCongruence::CongruentTo(_, _, el) => el.internal.get_repr()
                }).collect::<Vec<_>>();
                let congruences_small_basis = rns_factors.iter().zip(reprs.iter()).map(|(congruence, repr)| match (congruence, repr) {
                    (_, ManagedDoubleRNSElRepresentation::Zero) | 
                        (_, ManagedDoubleRNSElRepresentation::DoubleRNS(_)) => RNSFactorCongruence::Zero,
                    (RNSFactorCongruence::CongruentTo(other_ring, other_i, _), ManagedDoubleRNSElRepresentation::Both(small_basis_part, _)) |
                        (RNSFactorCongruence::CongruentTo(other_ring, other_i, _), ManagedDoubleRNSElRepresentation::SmallBasis(small_basis_part)) => RNSFactorCongruence::CongruentTo(&other_ring.base, *other_i, small_basis_part.unwrap_borrowed()),
                    (RNSFactorCongruence::CongruentTo(other_ring, other_i, _), ManagedDoubleRNSElRepresentation::Sum(parts)) => RNSFactorCongruence::CongruentTo(&other_ring.base, *other_i, &parts.0),
                    (RNSFactorCongruence::Zero, _) => unreachable!()
                });
                let congruences_doublerns = rns_factors.iter().zip(reprs.iter()).map(|(congruence, repr)| match (congruence, repr) {
                    (_, ManagedDoubleRNSElRepresentation::Zero) | 
                        (_, ManagedDoubleRNSElRepresentation::SmallBasis(_)) |
                        (_, ManagedDoubleRNSElRepresentation::Both(_, _)) => RNSFactorCongruence::Zero,
                    (RNSFactorCongruence::CongruentTo(other_ring, other_i, _), ManagedDoubleRNSElRepresentation::DoubleRNS(doublerns_part))  => RNSFactorCongruence::CongruentTo(&other_ring.base, *other_i, doublerns_part.unwrap_borrowed()),
                    (RNSFactorCongruence::CongruentTo(other_ring, other_i, _), ManagedDoubleRNSElRepresentation::Sum(parts)) => RNSFactorCongruence::CongruentTo(&other_ring.base, *other_i, &parts.1),
                    (RNSFactorCongruence::Zero, _) => unreachable!()
                });
                self.from_sum(
                    self.base.collect_rns_factors_non_fft(congruences_small_basis),
                    self.base.collect_rns_factors(congruences_doublerns)
                )
            }
        }
    }

    fn collect_rns_factors_prepared<'a, I>(&self, _rns_factors: I) -> Self::PreparedMultiplicant
        where I: Iterator<Item = super::RNSFactorCongruence<'a, Self, Self::PreparedMultiplicant>>,
            Self: 'a
    {
        ()
    }

    fn small_generating_set_len(&self) -> usize {
        self.rank()
    }

    #[instrument(skip_all)]
    fn as_representation_wrt_small_generating_set<V>(&self, x: &Self::Element, output: SubmatrixMut<V, zn_64::ZnEl>)
        where V: AsPointerToSlice<zn_64::ZnEl>
    {
        self.base.as_representation_wrt_small_generating_set_non_fft(self.to_small_basis(x).unwrap_or(&self.zero), output);
    }

    #[instrument(skip_all)]
    fn from_representation_wrt_small_generating_set<V>(&self, data: Submatrix<V, zn_64::ZnEl>) -> Self::Element
        where V: AsPointerToSlice<zn_64::ZnEl>
    {
        self.from_small_basis(self.base.from_representation_wrt_small_generating_set_non_fft(data))
    }
}

impl<NumberRing, A> NumberRingQuotient for ManagedDoubleRNSRingBase<NumberRing, A> 
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    type NumberRing = NumberRing;

    fn number_ring(&self) -> &Self::NumberRing {
        &self.base.number_ring()
    }
    
    fn acting_galois_group(&self) -> &Subgroup<CyclotomicGaloisGroup> {
        self.base.acting_galois_group()
    }

    fn apply_galois_action(&self, el: &Self::Element, g: &GaloisGroupEl) -> Self::Element {
        let result = if let Some(value) = self.to_doublerns(el) {
            self.base.apply_galois_action(&*value, g)
        } else {
            return self.zero();
        };
        return self.from_doublerns(result);
    }
}

impl<NumberRing, A> PartialEq for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    fn eq(&self, other: &Self) -> bool {
        self.base == other.base
    }
}

impl<NumberRing, A> RingBase for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    type Element = ManagedDoubleRNSEl<NumberRing, A>;

    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        ManagedDoubleRNSEl { internal: val.internal.clone() }
    }

    fn eq_el(&self, lhs: &Self::Element, rhs: &Self::Element) -> bool {
        let lhs_repr = lhs.internal.get_repr().get_kind();
        let rhs_repr = rhs.internal.get_repr().get_kind();
        match (lhs_repr, rhs_repr) {
            (ManagedDoubleRNSElRepresentationKind::Zero, _) | (_, ManagedDoubleRNSElRepresentationKind::Zero) => self.is_zero(lhs),
            (ManagedDoubleRNSElRepresentationKind::SmallBasis, _) | (_, ManagedDoubleRNSElRepresentationKind::SmallBasis) => self.base.eq_el_non_fft(&*self.to_small_basis(lhs).unwrap(), &*self.to_small_basis(rhs).unwrap()),
            _ => self.base.eq_el(&*self.to_doublerns(lhs).unwrap(), &*self.to_doublerns(rhs).unwrap())
        }
    }

    fn is_zero(&self, value: &Self::Element) -> bool {
        let val_repr = value.internal.get_repr().get_kind();
        match val_repr {
            ManagedDoubleRNSElRepresentationKind::Zero => true,
            ManagedDoubleRNSElRepresentationKind::Sum | ManagedDoubleRNSElRepresentationKind::SmallBasis | ManagedDoubleRNSElRepresentationKind::Both => self.base.eq_el_non_fft(&*self.to_small_basis(value).unwrap(), &self.zero),
            ManagedDoubleRNSElRepresentationKind::DoubleRNS => self.base.is_zero(self.to_doublerns(value).unwrap())
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
        *value = self.from_doublerns(result);
    }

    fn negate(&self, mut value: Self::Element) -> Self::Element {
        value.internal = self.negate_internal(value.internal);
        return value;
    }
    
    #[instrument(skip_all)]
    fn mul_int_ref(&self, lhs: &Self::Element, rhs: i32) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.mul_base_internal(lhs.internal.clone(), &self.base_ring().int_hom().map(rhs))
        }
    }

    fn add_ref(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.add_internal(lhs.internal.clone(), rhs.internal.clone())
        }
    }

    fn sub_ref(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.sub_internal(lhs.internal.clone(), rhs.internal.clone())
        }
    }

    fn mul_ref(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        if let (Some(lhs), Some(rhs)) = (self.to_doublerns(lhs), self.to_doublerns(rhs)) {
            self.from_doublerns(self.base.mul_ref(&*lhs, &*rhs))
        } else {
            self.zero()
        }
    }

    fn fma(&self, lhs: &Self::Element, rhs: &Self::Element, summand: Self::Element) -> Self::Element {
        if let (Some(lhs), Some(rhs)) = (self.to_doublerns(lhs), self.to_doublerns(rhs)) {
            match summand.internal.get_repr() {
                ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) => {
                    return self.from_doublerns(self.unmanaged_ring().fma(lhs, rhs, double_rns_repr.to_owned(|x| self.unmanaged_ring().clone_el(x))));
                },
                ManagedDoubleRNSElRepresentation::Sum(parts) => {
                    return self.from_sum(
                        self.unmanaged_ring().get_ring().clone_el_non_fft(&parts.0),
                        self.unmanaged_ring().fma(lhs, rhs, self.unmanaged_ring().clone_el(&parts.1))
                    )
                },
                ManagedDoubleRNSElRepresentation::Zero => {
                    return self.from_doublerns(self.unmanaged_ring().mul_ref(lhs, rhs))
                },
                _ => {}
            };
            return self.add(summand, self.from_doublerns(self.unmanaged_ring().mul_ref(lhs, rhs)));
        } else {
            return summand;
        }
    }

    fn pow_gen<R: IntegerRingStore>(&self, x: Self::Element, power: &El<R>, integers: R) -> Self::Element 
        where R::Type: IntegerRing
    {
        let result = if let Some(nonzero) = self.to_doublerns(&x) {
            self.base.pow_gen(self.base.clone_el(&*nonzero), power, integers)
        } else {
            return self.zero();
        };
        return self.from_doublerns(result);
    }

    fn characteristic<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        self.base_ring().characteristic(ZZ)
    }

    fn add_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        take_mut::take(&mut lhs.internal, |x| self.add_internal(x, rhs.internal.clone()));
    }

    fn add_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        take_mut::take(&mut lhs.internal, |x| self.add_internal(x, rhs.internal));
    }

    fn sub_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        take_mut::take(&mut lhs.internal, |x| self.sub_internal(x, rhs.internal.clone()));
    }

    fn negate_inplace(&self, lhs: &mut Self::Element) {
        take_mut::take(&mut lhs.internal, |x| self.negate_internal(x));
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
        take_mut::take(lhs, |x| self.sub(x, rhs));
    }

    fn mul_assign_int(&self, lhs: &mut Self::Element, rhs: i32) {
        take_mut::take(lhs, |x| self.mul_int(x, rhs));
    }

    fn mul_int(&self, lhs: Self::Element, rhs: i32) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.mul_base_internal(lhs.internal, &self.base_ring().int_hom().map(rhs))
        }
    }

    fn sub_self_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        take_mut::take(lhs, |x| self.sub(rhs, x));
    }

    fn sub_self_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        take_mut::take(lhs, |x| self.sub_ref_fst(rhs, x));
    }

    fn add_ref_fst(&self, lhs: &Self::Element, rhs: Self::Element) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.add_internal(lhs.internal.clone(), rhs.internal)
        }
    }

    fn add_ref_snd(&self, lhs: Self::Element, rhs: &Self::Element) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.add_internal(lhs.internal, rhs.internal.clone())
        }
    }

    fn add(&self, lhs: Self::Element, rhs: Self::Element) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.add_internal(lhs.internal, rhs.internal)
        }
    }

    fn sub_ref_fst(&self, lhs: &Self::Element, rhs: Self::Element) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.sub_internal(lhs.internal.clone(), rhs.internal)
        }
    }

    fn sub_ref_snd(&self, lhs: Self::Element, rhs: &Self::Element) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.sub_internal(lhs.internal, rhs.internal.clone())
        }
    }

    fn sub(&self, lhs: Self::Element, rhs: Self::Element) -> Self::Element {
        ManagedDoubleRNSEl {
            internal: self.sub_internal(lhs.internal, rhs.internal)
        }
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
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    default fn inner_product<I: Iterator<Item = (Self::Element, Self::Element)>>(&self, els: I) -> Self::Element {
        let data = els.collect::<Vec<_>>();
        return self.inner_product_ref(data.iter().map(|(l, r)| (l, r)));
    }

    default fn inner_product_ref<'a, I: Iterator<Item = (&'a Self::Element, &'a Self::Element)>>(&self, els: I) -> Self::Element
        where Self: 'a
    {
        self.from_doublerns(<_ as ComputeInnerProduct>::inner_product_ref(
            &self.base, 
            els.filter(|(l, r)| l.internal.get_repr().get_kind() != ManagedDoubleRNSElRepresentationKind::Zero && r.internal.get_repr().get_kind() != ManagedDoubleRNSElRepresentationKind::Zero)
                .map(|(l, r)| (self.to_doublerns(l).unwrap(), self.to_doublerns(r).unwrap()))
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
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    type BaseRing = <DoubleRNSRingBase<NumberRing, A> as RingExtension>::BaseRing;

    fn base_ring<'a>(&'a self) -> &'a Self::BaseRing {
        self.base.base_ring()
    }

    fn from(&self, x: El<Self::BaseRing>) -> Self::Element {
        let result_fft = self.base.from(self.base_ring().clone_el(&x));
        let result_coeff = self.base.from_non_fft(x);
        return self.from_both(result_coeff, result_fft);
    }

    fn mul_assign_base(&self, lhs: &mut Self::Element, rhs: &El<Self::BaseRing>) {
        take_mut::take(&mut lhs.internal, |x| self.mul_base_internal(x, rhs))
    }
}

impl<NumberRing, A> FreeAlgebra for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    type VectorRepresentation<'a> = DoubleRNSRingBaseElVectorRepresentation<'a, NumberRing, A> 
        where Self: 'a;

    fn canonical_gen(&self) -> Self::Element {
        let result = self.base.canonical_gen();
        return self.from_doublerns(result);
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
        return self.from_small_basis(result);
    }
}

impl<NumberRing, A> FiniteRingSpecializable for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    fn specialize<O: FiniteRingOperation<Self>>(op: O) -> O::Output {
        op.execute()
    }
}

impl<NumberRing, A> FiniteRing for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    type ElementsIter<'a> = std::iter::Map<<DoubleRNSRingBase<NumberRing, A> as FiniteRing>::ElementsIter<'a>, fn(DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A>>
        where Self: 'a;

    fn elements<'a>(&'a self) -> Self::ElementsIter<'a> {
        fn from_doublerns<NumberRing, A>(x: DoubleRNSEl<NumberRing, A>) -> ManagedDoubleRNSEl<NumberRing, A>
            where NumberRing: AbstractNumberRing,
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
        return self.from_doublerns(self.base.random_element(rng));
    }

    fn size<I: IntegerRingStore + Copy>(&self, ZZ: I) -> Option<El<I>>
        where I::Type: IntegerRing
    {
        self.base.size(ZZ)
    }
}

impl<NumberRing, A> SerializableElementRing for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    fn serialize<S>(&self, el: &Self::Element, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        if serializer.is_human_readable() {
            return SerializableNewtypeStruct::new("ManagedDoubleRNSEl", &SerializableSmallBasisElWithRing::new(&self.base, self.to_small_basis(el).unwrap_or(&self.zero))).serialize(serializer);
        }
        if let ManagedDoubleRNSElRepresentation::DoubleRNS(double_rns_repr) = el.internal.get_repr() {
            serializer.serialize_newtype_variant("ManagedDoubleRNSEl", 0, "DoubleRNS", &SerializeWithRing::new(&*double_rns_repr, RingRef::new(&self.base)))
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
            return DeserializeSeedNewtypeStruct::new("ManagedDoubleRNSEl", DeserializeSeedSmallBasisElWithRing::new(&self.base)).deserialize(deserializer).map(|small_basis_repr| self.from_small_basis(small_basis_repr));
        }

        struct ResultVisitor<'a, NumberRing, A>
            where NumberRing: AbstractNumberRing,
                A: Allocator + Clone
        {
            ring: &'a ManagedDoubleRNSRingBase<NumberRing, A>,
        }
        impl<'a, 'de, NumberRing, A> serde::de::Visitor<'de> for ResultVisitor<'a, NumberRing, A>
            where NumberRing: AbstractNumberRing,
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
                    Discriminant::DoubleRNS => variant.newtype_variant_seed(DeserializeWithRing::new(self.ring.unmanaged_ring())).map(|double_rns_repr| self.ring.from_doublerns(double_rns_repr)),
                    Discriminant::SmallBasis => variant.newtype_variant_seed(DeserializeSeedSmallBasisElWithRing::new(self.ring.unmanaged_ring().get_ring())).map(|small_basis_repr| self.ring.from_small_basis(small_basis_repr)),
                    Discriminant::Zero => variant.unit_variant().map(|()| self.ring.zero())
                }
            }
        }
        return deserializer.deserialize_enum("ManagedDoubleRNSEl", &["DoubleRNS", "SmallBasis", "Zero"], ResultVisitor { ring: self });
    }
}

impl<NumberRing, A> CanHomFrom<BigIntRingBase> for ManagedDoubleRNSRingBase<NumberRing, A>
    where NumberRing: AbstractNumberRing,
        A: Allocator + Clone
{
    type Homomorphism = <zn_rns::ZnBase<zn_64::Zn, BigIntRing> as CanHomFrom<BigIntRingBase>>::Homomorphism;

    fn has_canonical_hom(&self, from: &BigIntRingBase) -> Option<Self::Homomorphism> {
        self.base.base_ring().get_ring().has_canonical_hom(from)
    }

    fn map_in(&self, from: &BigIntRingBase, el: El<BigIntRing>, hom: &Self::Homomorphism) -> Self::Element {
        self.from(self.base.base_ring().get_ring().map_in(from, el, hom))
    }

    fn mul_assign_map_in(&self, from: &BigIntRingBase, lhs: &mut Self::Element, rhs: <BigIntRingBase as RingBase>::Element, hom: &Self::Homomorphism) {
        self.mul_assign_base(lhs, &self.base.base_ring().get_ring().map_in(from, rhs, hom));
    }

    fn mul_assign_map_in_ref(&self, from: &BigIntRingBase, lhs: &mut Self::Element, rhs: &<BigIntRingBase as RingBase>::Element, hom: &Self::Homomorphism) {
        self.mul_assign_base(lhs, &self.base.base_ring().get_ring().map_in_ref(from, rhs, hom));
    }
}

impl<NumberRing, A1, A2, C> CanHomFrom<SingleRNSRingBase<NumberRing, A1, C>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: AbstractNumberRing,
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
        return self.from_small_basis(self.base.map_in_from_singlerns(from, el, hom));
    }
}

impl<NumberRing, A1, A2> CanHomFrom<DoubleRNSRingBase<NumberRing, A1>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: AbstractNumberRing,
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
        return self.from_doublerns(self.base.map_in(from, el, hom));
    }
}

impl<NumberRing, A1, A2> CanHomFrom<ManagedDoubleRNSRingBase<NumberRing, A1>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: AbstractNumberRing,
        A1: Allocator + Clone,
        A2: Allocator + Clone
{
    type Homomorphism = <DoubleRNSRingBase<NumberRing, A2> as CanHomFrom<DoubleRNSRingBase<NumberRing, A2>>>::Homomorphism;

    fn has_canonical_hom(&self, from: &ManagedDoubleRNSRingBase<NumberRing, A1>) -> Option<Self::Homomorphism> {
        self.base.has_canonical_hom(&from.base)
    }

    fn map_in_ref(&self, from: &ManagedDoubleRNSRingBase<NumberRing, A1>, el: &<ManagedDoubleRNSRingBase<NumberRing, A1> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        if let Some(el) = from.to_doublerns(el) {
            return self.from_doublerns(self.base.map_in_ref(&from.base, &*el, hom));
        } else {
            self.zero()
        }
    }

    fn map_in(&self, from: &ManagedDoubleRNSRingBase<NumberRing, A1>, el: <ManagedDoubleRNSRingBase<NumberRing, A1> as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.map_in_ref(from, &el, hom)
    }
}

impl<NumberRing, A1, A2, C> CanIsoFromTo<SingleRNSRingBase<NumberRing, A1, C>> for ManagedDoubleRNSRingBase<NumberRing, A2>
    where NumberRing: AbstractNumberRing,
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
    where NumberRing: AbstractNumberRing,
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
    where NumberRing: AbstractNumberRing,
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
fn test_inner_product() {
    let (ring, elements) = ring_and_elements();
    assert_el_eq!(
        &ring,
        ring.sum(elements.iter().zip(elements.iter().skip(2)).map(|(l, r)| ring.mul_ref(l, r))),
        ring.get_ring().inner_product_ref(elements.iter().zip(elements.iter().skip(2)))
    );
}

#[test]
fn test_thread_safe() {
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(16);
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let ring = Arc::new(ManagedDoubleRNSRingBase::new(number_ring, rns_base));

    let test_element = Arc::new(ring.get_ring().from_sum(
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
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(16);
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let ring = ManagedDoubleRNSRingBase::new(number_ring, rns_base);

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
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(16);
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(97), zn_64::Zn::new(193)], BigIntRing::RING);
    let ring = ManagedDoubleRNSRingBase::new(number_ring.clone(), rns_base.clone());
    let singlerns_ring = SingleRNSRingBase::<_, _, DefaultConvolution>::new(number_ring, rns_base);
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
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(4);
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let ring = ManagedDoubleRNSRingBase::new(number_ring, rns_base);
    let base = &ring.get_ring().base;
    let reprs_of_11: [Box<dyn Fn() -> ManagedDoubleRNSEl<_, _>>; 4] = [
        Box::new(|| ring.get_ring().from_small_basis(base.from_non_fft(base.base_ring().int_hom().map(11)))),
        Box::new(|| ring.get_ring().from_doublerns(base.from(base.base_ring().int_hom().map(11)))),
        Box::new(|| ring.get_ring().from_sum(base.from_non_fft(base.base_ring().int_hom().map(10)), base.from(base.base_ring().int_hom().map(1)))),
        Box::new(|| ring.get_ring().from_both(base.from_non_fft(base.base_ring().int_hom().map(11)), base.from(base.base_ring().int_hom().map(11))))
    ];
    let reprs_of_102: [Box<dyn Fn() -> ManagedDoubleRNSEl<_, _>>; 4] = [
        Box::new(|| ring.get_ring().from_small_basis(base.from_non_fft(base.base_ring().int_hom().map(102)))),
        Box::new(|| ring.get_ring().from_doublerns(base.from(base.base_ring().int_hom().map(102)))),
        Box::new(|| ring.get_ring().from_sum(base.from_non_fft(base.base_ring().int_hom().map(100)), base.from(base.base_ring().int_hom().map(2)))),
        Box::new(|| ring.get_ring().from_both(base.from_non_fft(base.base_ring().int_hom().map(102)), base.from(base.base_ring().int_hom().map(102))))
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
        let a_small_basis = ring.get_ring().from_small_basis(ring.get_ring().unmanaged_ring().get_ring().clone_el_non_fft(ring.get_ring().to_small_basis(a).unwrap()));
        let serializer = serde_assert::Serializer::builder().is_human_readable(true).build();
        let tokens = ring.get_ring().serialize(&a_small_basis, &serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(true).build();
        let result = ring.get_ring().deserialize(&mut deserializer).unwrap();
        assert_el_eq!(ring, &a_small_basis, &result);
        match result.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::SmallBasis(_) => {},
            _ => panic!("wrong representation")
        };

        let a_small_basis = ring.get_ring().from_small_basis(ring.get_ring().unmanaged_ring().get_ring().clone_el_non_fft(ring.get_ring().to_small_basis(a).unwrap()));
        let serializer = serde_assert::Serializer::builder().is_human_readable(false).build();
        let tokens = ring.get_ring().serialize(&a_small_basis, &serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(false).build();
        let result = ring.get_ring().deserialize(&mut deserializer).unwrap();
        assert_el_eq!(ring, &a_small_basis, &result);
        match result.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::SmallBasis(_) => {},
            _ => panic!("wrong representation")
        };

        let a_doublerns = ring.get_ring().from_doublerns(ring.get_ring().unmanaged_ring().clone_el(ring.get_ring().to_doublerns(a).unwrap()));
        let serializer = serde_assert::Serializer::builder().is_human_readable(true).build();
        let tokens = ring.get_ring().serialize(&a_doublerns, &serializer).unwrap();
        let mut deserializer = serde_assert::Deserializer::builder(tokens).is_human_readable(true).build();
        let result = ring.get_ring().deserialize(&mut deserializer).unwrap();
        assert_el_eq!(ring, &a_doublerns, &result);
        match result.internal.get_repr() {
            ManagedDoubleRNSElRepresentation::SmallBasis(_) => {},
            _ => panic!("wrong representation")
        };

        let a_doublerns = ring.get_ring().from_doublerns(ring.get_ring().unmanaged_ring().clone_el(ring.get_ring().to_doublerns(a).unwrap()));
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

#[test]
fn test_deadlock() {
    let number_ring: Pow2CyclotomicNumberRing = Pow2CyclotomicNumberRing::new(4);
    let rns_base = zn_rns::Zn::new(vec![zn_64::Zn::new(17), zn_64::Zn::new(97)], BigIntRing::RING);
    let ring = ManagedDoubleRNSRingBase::new(number_ring, rns_base);
    let rns_base = ring.base_ring();

    let el = ring.get_ring().from_sum(
        ring.get_ring().base.from_non_fft(rns_base.int_hom().map(10)),
        ring.get_ring().base.from(rns_base.int_hom().map(-10)),
    );
    assert!(ring.is_zero(&el));
    assert!(ring.eq_el(&el, &el));
}
