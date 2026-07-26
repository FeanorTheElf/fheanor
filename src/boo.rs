use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::MappedRwLockReadGuard;

pub trait GuardType<T> {
    type Guard<'a>: Deref<Target = T>
    where
        Self: 'a;
}

pub struct MappedRwLockReadGuardType<T> {
    element: PhantomData<T>,
}

impl<T> GuardType<T> for MappedRwLockReadGuardType<T> {
    type Guard<'a>
        = MappedRwLockReadGuard<'a, T>
    where
        Self: 'a;
}

pub struct NeverDeref<T> {
    element: PhantomData<T>,
    content: !,
}

impl<T> Deref for NeverDeref<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target { self.content }
}

impl<T> GuardType<T> for ! {
    type Guard<'a>
        = NeverDeref<T>
    where
        Self: 'a;
}

#[allow(dead_code)]
pub enum Boo<'a, T, G: 'a + GuardType<T> = !> {
    Borrowed(&'a T),
    MutablyBorrowed(&'a mut T),
    Owned(T),
    GuardedBorrowed(G::Guard<'a>),
}

impl<'a, T, G: 'a + GuardType<T>> Deref for Boo<'a, T, G> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Boo::Borrowed(x) => x,
            Boo::MutablyBorrowed(x) => x,
            Boo::Owned(x) => x,
            Boo::GuardedBorrowed(x) => x,
        }
    }
}

impl<'a, T, G: 'a + GuardType<T>> Boo<'a, T, G> {
    #[allow(dead_code)]
    pub fn to_mut<F>(&mut self, clone_fn: F) -> &mut T
    where
        F: FnOnce(&T) -> T,
    {
        match self {
            Boo::Borrowed(x) => {
                *self = Boo::Owned(clone_fn(x));
            }
            Boo::GuardedBorrowed(x) => {
                *self = Boo::Owned(clone_fn(x));
            }
            _ => {}
        }
        match self {
            Boo::Borrowed(_) => unreachable!(),
            Boo::GuardedBorrowed(_) => unreachable!(),
            Boo::MutablyBorrowed(x) => x,
            Boo::Owned(x) => x,
        }
    }

    pub fn to_owned<F>(self, clone_fn: F) -> T
    where
        F: FnOnce(&T) -> T,
    {
        match self {
            Boo::Borrowed(x) => clone_fn(x),
            Boo::GuardedBorrowed(x) => clone_fn(&x),
            Boo::MutablyBorrowed(x) => clone_fn(x),
            Boo::Owned(x) => x,
        }
    }

    pub fn unwrap_borrowed(&self) -> &'a T {
        match self {
            Boo::Borrowed(x) => x,
            _ => unreachable!(),
        }
    }
}
