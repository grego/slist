//! A trait for creating a list of references from a reference of a list.

use super::{Either, List, Slist, SlistSum};

/// A trait for creating a list of references from a reference of a list.
pub trait SlistAsRef<'a, T: 'a>: Slist<T> {
    /// Result of taking a reference of the list
    type Result: Slist<&'a T>;
    /// Result of taking a mutable reference of the list
    type ResultMut: Slist<&'a mut T>;
    /// Create a list of references from a reference of a list
    fn as_ref(&'a self) -> Self::Result;
    /// Create a list of mutable references from a mutable reference of a list
    fn as_mut(&'a mut self) -> Self::ResultMut;
}

impl<'a, T: 'a> SlistAsRef<'a, T> for () {
    type Result = ();
    type ResultMut = ();

    #[inline]
    fn as_ref(&'a self) -> Self::Result {}
    #[inline]
    fn as_mut(&'a mut self) -> Self::ResultMut {}
}

impl<'a, T: 'a, N, M, O> SlistAsRef<'a, T> for List<T, N>
where
    N: SlistAsRef<'a, T, Result = M, ResultMut = O> + Slist<T>,
    M: Slist<&'a T>,
    O: Slist<&'a mut T>,
    N::Filter: SlistSum<T, Next = N>,
    M::Filter: SlistSum<&'a T, Next = M>,
    O::Filter: SlistSum<&'a mut T, Next = O>,
{
    type Result = List<&'a T, N::Result>;
    type ResultMut = List<&'a mut T, N::ResultMut>;

    #[inline]
    fn as_ref(&'a self) -> Self::Result {
        List {
            head: &self.head,
            tail: self.tail.as_ref(),
        }
    }

    #[inline]
    fn as_mut(&'a mut self) -> Self::ResultMut {
        List {
            head: &mut self.head,
            tail: self.tail.as_mut(),
        }
    }
}

impl<'a, T: 'a, N: SlistAsRef<'a, T>, M: SlistAsRef<'a, T>> SlistAsRef<'a, T> for Either<N, M> {
    type Result = Either<N::Result, M::Result>;
    type ResultMut = Either<N::ResultMut, M::ResultMut>;

    #[inline]
    fn as_ref(&'a self) -> Self::Result {
        match self {
            Either::Left(n) => Either::Left(n.as_ref()),
            Either::Right(m) => Either::Right(m.as_ref()),
        }
    }

    #[inline]
    fn as_mut(&'a mut self) -> Self::ResultMut {
        match self {
            Either::Left(n) => Either::Left(n.as_mut()),
            Either::Right(m) => Either::Right(m.as_mut()),
        }
    }
}
