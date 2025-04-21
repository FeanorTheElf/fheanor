#![feature(never_type)]
#![feature(fn_traits)]
#![feature(unboxed_closures)]
#![feature(test)]
#![feature(const_type_name)]
#![feature(allocator_api)]
#![feature(ptr_alignment_type)]
#![feature(associated_type_defaults)]
#![feature(generic_arg_infer)]
#![feature(min_specialization)]
#![feature(array_chunks)]
#![feature(mapped_lock_guards)]
#![feature(associated_const_equality)]

#![allow(non_snake_case)]
#![allow(type_alias_bounds)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]
#![allow(rustdoc::private_intra_doc_links)]

#![doc = include_str!("../Readme.md")]

use std::alloc::Global;
use std::time::Instant;

use feanor_math::integer::BigIntRing;
use feanor_math::primitive_int::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::zn_64::Zn;

extern crate feanor_math;
#[cfg(feature = "use_hexl")]
extern crate feanor_math_hexl;
extern crate test;
extern crate thread_local;
extern crate serde;
extern crate rand;
extern crate rand_distr;

///
/// Simple way to create a ring element from a list of its coefficients as `i32`.
/// 
#[cfg(test)]
fn ring_literal<R>(ring: R, data: &[i32]) -> El<R>
    where R: RingStore,
        R::Type: feanor_math::rings::extension::FreeAlgebra
{
    use feanor_math::homomorphism::*;
    use feanor_math::rings::extension::*;

    ring.from_canonical_basis(data.iter().map(|x| ring.base_ring().int_hom().map(*x)))
}

///
/// The default convolution algorithm that will be used by all tests and benchmarks.
/// It is also a good choice when instantiating homomorphic encryption as a user.
/// 
/// By default, it will point to a pure-rust implementation of convolution (currently
/// [`crate::ntt::ntt_convolution::NTTConv`]), but can be changed by using the feature
/// `use_hexl`.
/// 
#[cfg(feature = "use_hexl")]
pub type DefaultConvolution = feanor_math_hexl::conv::HEXLConvolution;

///
/// The default convolution algorithm that will be used by all tests and benchmarks.
/// It is also a good choice when instantiating homomorphic encryption as a user.
/// 
/// By default, it will point to a pure-rust implementation of convolution (currently
/// [`crate::ntt::ntt_convolution::NTTConv`]), but can be changed by using the feature
/// `use_hexl`.
/// 
#[cfg(not(feature = "use_hexl"))]
pub type DefaultConvolution = crate::ntt::ntt_convolution::NTTConv<Zn>;

///
/// The default algorithm for computing negacyclic NTTs that will be used by 
/// all tests and benchmarks. It is also a good choice when instantiating homomorphic 
/// encryption as a user.
/// 
/// By default, it will point to a pure-rust implementation of the negacyclic NTT
/// (currently [`crate::number_ring::pow2_cyclotomic::RustNegacyclicNTT`]), but can be 
/// changed by using the feature `use_hexl`.
/// 
#[cfg(feature = "use_hexl")]
pub type DefaultNegacyclicNTT = feanor_math_hexl::hexl::HEXLNegacyclicNTT;

///
/// The default algorithm for computing negacyclic NTTs that will be used by 
/// all tests and benchmarks. It is also a good choice when instantiating homomorphic 
/// encryption as a user.
/// 
/// By default, it will point to a pure-rust implementation of the negacyclic NTT
/// (currently [`crate::number_ring::pow2_cyclotomic::RustNegacyclicNTT`]), but can be 
/// changed by using the feature `use_hexl`.
/// 
#[cfg(not(feature = "use_hexl"))]
pub type DefaultNegacyclicNTT = crate::number_ring::pow2_cyclotomic::RustNegacyclicNTT<Zn>;

///
/// The default allocator for ciphertext ring elements, which will be used by all tests and
/// benchmarks. It is also a good choice when instantiating homomorphic encryption as a user.
/// 
/// Currently, this is always [`std::alloc::Global`].
/// 
pub type DefaultCiphertextAllocator = Global;

///
/// Euler's totient function.
/// 
#[allow(unused)]
fn euler_phi(factorization: &[(i64, usize)]) -> i64 {
    StaticRing::<i64>::RING.prod(factorization.iter().map(|(p, e)| (p - 1) * StaticRing::<i64>::RING.pow(*p, e - 1)))
}

///
/// Euler's totient function.
/// 
/// It takes a list of all distinct prime factors of `n`, and returns `phi(n)`.
/// 
fn euler_phi_squarefree(factorization: &[i64]) -> i64 {
    StaticRing::<i64>::RING.prod(factorization.iter().map(|p| p - 1))
}

///
/// Runs the given function. If `LOG` is true, its running time is printed to stdout.
/// 
pub fn log_time<F, T, const LOG: bool, const COUNTER_VAR_COUNT: usize>(description: &str, step_fn: F) -> T
    where F: FnOnce(&mut [usize; COUNTER_VAR_COUNT]) -> T
{
    if LOG {
        println!("{}", description);
    }
    let mut counters = [0; COUNTER_VAR_COUNT];
    let start = Instant::now();
    let result = step_fn(&mut counters);
    let end = Instant::now();
    if LOG {
        println!("done in {} ms, {:?}", (end - start).as_millis(), counters);
    }
    return result;
}

///
/// The ring of integers, implemented using arbitrary precision
/// 
const ZZbig: BigIntRing = BigIntRing::RING;
///
/// The ring of integers, implemented using 64-bit integers
/// 
const ZZi64: StaticRing<i64> = StaticRing::<i64>::RING;
///
/// The ring of integers, implemented using 128-bit integers
/// 
const ZZi128: StaticRing<i128> = StaticRing::<i128>::RING;

///
/// Contains some macros that mimic `#[derive(Deserialize)]` but for [`serde::de::DeserializeSeed`].
/// 
mod serialization_helper;

///
/// Contains an abstraction for NTTs and convolutions, which can then be
/// used to configure the ring implementations in this crate.
/// 
pub mod ntt;

///
/// Defines the trait [`cyclotomic::CyclotomicRing`] for rings of the form `R[X]/(Phi_n)`, where `R` is any base ring.
/// 
pub mod cyclotomic;

///
/// Implementation of fast RNS conversion algorithms.
/// 
pub mod rnsconv;

///
/// Contains an HE-specific abstraction for number rings.
/// 
pub mod number_ring;

///
/// Implementation of rings using double-RNS representation.
/// 
pub mod ciphertext_ring;

///
/// Contains an implementation of "gadget products", which are a form of inner
/// products that are commonly used in HE to compute multiplications of noisy values
/// in a way that reduces the increase in noise.
/// 
pub mod gadget_product;

///
/// Contains an implementation of the BFV scheme.
/// 
pub mod bfv;

///
/// The implementation of arithmetic-galois circuits (i.e. circuits built
/// from linear combination, multiplication and galois gates).
/// 
pub mod circuit;

///
/// Contains algorithms to compute linear transformations and represent
/// them as linear combination of Galois automorphisms, as required for
/// (second-generation) HE schemes.
/// 
pub mod lintransform;

///
/// Contains algorithms to build arithmetic circuits, with a focus on
/// digit extraction polynomials.
/// 
pub mod digitextract;

///
/// Contains an implementation of the BGV scheme.
/// 
pub mod bgv;

///
/// Contains an implementation of the CLPX/GBFV scheme.
/// 
pub mod clpx;

///
/// This is a workaround for displaying examples on `docs.rs`.
/// 
/// Contains an empty submodule for each example, whose documentation gives
/// a guide to the corresponding concepts of Fheanor.
/// 
/// Note that this module is only included when building the documentation,
/// you cannot use it when importing `fheanor` as a crate.
/// 
#[cfg(any(doc, doctest))]
pub mod examples {
    #[doc = include_str!("../examples/bfv_basics/Readme.md")]
    pub mod bfv_basics {}
    #[doc = include_str!("../examples/bgv_basics/Readme.md")]
    pub mod bgv_basics {}
    #[doc = include_str!("../examples/bfv_impl_v1/Readme.md")]
    pub mod bfv_impl_v1 {}
    #[doc = include_str!("../examples/bfv_impl_v2/Readme.md")]
    pub mod bfv_impl_v2 {}
    #[doc = include_str!("../examples/clpx_basics/Readme.md")]
    pub mod clpx_basics {}
}