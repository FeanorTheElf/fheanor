use std::sync::{MappedRwLockReadGuard, RwLock, RwLockReadGuard};

use feanor_math::primitive_int::StaticRing;
use feanor_math::rings::zn::zn_64::*;
use feanor_math::ring::*;
use feanor_math::rings::zn::ZnRingStore;

///
/// Contains algorithms for computing linear transforms and representing them
/// as linear combination of Galois automorphisms.
/// 
pub mod matmul;

///
/// Contains an implementation of the homomorphic trace.
/// 
pub mod trace;

///
/// Contains an implementation of the Slots-to-Coefficients transform and its inverse
/// for odd, composite cyclotomic number rings.
/// 
pub mod composite;

///
/// Contains an implementation of the Slots-to-Coefficients transform and its inverse
/// for power-of-two cyclotomic number rings.
/// 
pub mod pow2;

///
/// Provides access to arbitrary powers of a single element of a finite ring,
/// caching intermediate powers for faster access.
/// 
/// The main use case are HE-style rings, in which multiplication can be quite
/// expensive.
/// 
pub struct PowerTable<R>
    where R: RingStore
{
    ring: R,
    exponent_ring: Zn,
    powers: RwLock<Vec<El<R>>>
}

impl<R> PowerTable<R>
    where R: RingStore
{
    pub fn new(ring: R, base: El<R>, order_of_base: usize) -> Self {
        debug_assert!(ring.is_one(&ring.pow(ring.clone_el(&base), order_of_base)));
        Self {
            powers: RwLock::new(vec![ring.one(), base]),
            ring: ring,
            exponent_ring: Zn::new(order_of_base as u64),
        }
    }

    pub fn get_power<'a>(&'a self, power: i64) -> MappedRwLockReadGuard<'a, El<R>> {
        let power = self.exponent_ring.smallest_positive_lift(self.exponent_ring.coerce(&StaticRing::<i64>::RING, power)) as usize;
        let powers = self.powers.read().unwrap();
        if powers.len() > power {
            return RwLockReadGuard::map(powers, |powers| &powers[power]);
        }
        drop(powers);
        let mut powers = self.powers.write().unwrap();
        while powers.len() <= power {
            let new = self.ring.mul_ref(powers.last().unwrap(), &powers[1]);
            powers.push(new);
        }
        drop(powers);
        return RwLockReadGuard::map(self.powers.read().unwrap(), |powers| &powers[power]);
    }
}