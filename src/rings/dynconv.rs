
use std::marker::PhantomData;
use std::ops::Deref;

use feanor_math::algorithms::convolution::ConvolutionAlgorithm;
use feanor_math::ring::*;
use feanor_math::seq::VectorView;

pub trait DynConvolutionAlgorithm<R>
    where R: ?Sized + RingBase
{
    fn compute_convolution_dyn(&self, lhs: &[R::Element], rhs: &[R::Element], dst: &mut [R::Element], ring: &R);
    fn supports_ring_dyn(&self, ring: &R) -> bool;
}

impl<R, C> DynConvolutionAlgorithm<R> for C
    where R: ?Sized + RingBase,
        C: ConvolutionAlgorithm<R>
{
    fn compute_convolution_dyn(&self, lhs: &[R::Element], rhs: &[R::Element], dst: &mut [R::Element], ring: &R) {
        self.compute_convolution(lhs, rhs, dst, RingRef::new(ring));
    }

    fn supports_ring_dyn(&self, ring: &R) -> bool {
        self.supports_ring(RingRef::new(ring))
    }
}

pub struct DynConvolutionAlgorithmConvolution<R, C = Box<dyn DynConvolutionAlgorithm<R>>>
    where C: Deref,
        C::Target: DynConvolutionAlgorithm<R>,
        R: ?Sized + RingBase
{
    ring: PhantomData<R>,
    conv: C
}

impl<C, R> Clone for DynConvolutionAlgorithmConvolution<R, C>
    where C: Deref + Clone,
        C::Target: DynConvolutionAlgorithm<R>,
        R: ?Sized + RingBase
{
    fn clone(&self) -> Self {
        Self {
            ring: self.ring,
            conv: self.conv.clone()
        }
    }
}

impl<C, R> DynConvolutionAlgorithmConvolution<R, C>
    where C: Deref,
        C::Target: DynConvolutionAlgorithm<R>,
        R: ?Sized + RingBase
{
    pub fn new(conv: C) -> Self {
        Self {
            ring: PhantomData,
            conv: conv
        }
    }
}

impl<C, R> ConvolutionAlgorithm<R> for DynConvolutionAlgorithmConvolution<R, C>
    where C: Deref,
        C::Target: DynConvolutionAlgorithm<R>,
        R: ?Sized + RingBase
{
    fn compute_convolution<S: RingStore<Type = R> + Copy, V1: VectorView<El<S>>, V2: VectorView<El<S>>>(&self, lhs: V1, rhs: V2, dst: &mut [El<S>], ring: S) {
        let copy_lhs = lhs.as_iter().map(|x| ring.clone_el(x)).collect::<Vec<_>>();
        let copy_rhs = rhs.as_iter().map(|x| ring.clone_el(x)).collect::<Vec<_>>();
        self.conv.compute_convolution_dyn(&copy_lhs, &copy_rhs, dst, ring.get_ring());
    }

    fn supports_ring<S: RingStore<Type = R> + Copy>(&self, ring: S) -> bool {
        self.conv.supports_ring_dyn(ring.get_ring())
    }
}

#[cfg(test)]
use feanor_math::primitive_int::StaticRing;
#[cfg(test)]
use feanor_math::rings::zn::zn_64::{Zn, ZnBase};
#[cfg(test)]
use std::alloc::Global;
#[cfg(test)]
use feanor_math::algorithms::convolution::STANDARD_CONVOLUTION;
#[cfg(test)]
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
#[cfg(test)]
use feanor_math::rings::extension::FreeAlgebraStore;
#[cfg(test)]
use feanor_math::assert_el_eq;

#[test]
fn test_dyn_convolution_is_dyn_compatible() {
    #[allow(unused)]
    fn test(_: &dyn DynConvolutionAlgorithm<StaticRing<i64>>) {}
}

#[test]
fn test_dyn_convolution_convolution_use_build_ring() {
    fn do_test(conv: Box<dyn DynConvolutionAlgorithm<ZnBase>>) {
        let base_ring = Zn::new(2);
        let ring = FreeAlgebraImpl::new_with(base_ring, 3, [base_ring.one(), base_ring.one()], "a", Global, DynConvolutionAlgorithmConvolution::<ZnBase>::new(conv));
        assert_el_eq!(&ring, ring.one(), ring.pow(ring.canonical_gen(), 7));
    }
    do_test(Box::new(STANDARD_CONVOLUTION));
}