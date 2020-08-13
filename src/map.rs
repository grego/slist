//! Map a list of one type into a list of another type via a mapping function.

use super::{Either, List, Slist, SlistFlatten, SlistSum};

/// Map a list of type `T` into a list of type `U' via a mapping closure.
pub trait SlistMap<T, U>: Slist<T> {
    /// Result of applying the map.
    type Result: Slist<U>;
    /// Map a list of type `T` into a list of type `U' via a mapping closure `f`,
    /// which it applies onto each element of the list.
    fn map<F: FnMut(T) -> U>(self, f: F) -> Self::Result;
    /// Both map and filter. The closure `f` must return `Option<u>`.
    /// Only the elements for which the closure returns `Some(result)`
    /// are retained and unwrapped.
    /// ```
    /// # use slist::prelude::*;
    /// let list = slist![1, 2].flat_map(|i| slist![i; 2]);
    /// assert_eq!(list, slist![1, 1, 2, 2]);
    /// ```
    fn filter_map<F: FnMut(T) -> Option<U>>(
        self,
        f: F,
    ) -> Either<Self::Result, <Self::Result as Slist<U>>::Filter>;
    /// Map list into a list of lists and then flatten the nested structure.
    #[inline]
    fn flat_map<F: FnMut(T) -> U, V>(self, f: F) -> <Self::Result as SlistFlatten<U, V>>::Flattened
    where
        Self::Result: SlistFlatten<U, V>,
        U: Slist<V>
    {
        self.map(f).flatten()
    }
}

impl<T, U> SlistMap<T, U> for () {
    type Result = ();

    #[inline]
    fn map<F: FnMut(T) -> U>(self, _: F) -> Self::Result {}
    #[inline]
    fn filter_map<F: FnMut(T) -> Option<U>>(self, _f: F) -> Either<(), <() as Slist<U>>::Filter> {
        Either::Left(())
    }
}

impl<U, T, N, M> SlistMap<T, U> for List<T, N>
where
    N: SlistMap<T, U, Result = M> + Slist<T>,
    M: Slist<U>,
    N::Filter: SlistSum<T, Next = N>,
    M::Filter: SlistSum<U, Next = N::Result>,
{
    type Result = List<U, N::Result>;

    #[inline]
    fn map<F: FnMut(T) -> U>(self, mut f: F) -> Self::Result {
        List {
            head: f(self.head),
            tail: self.tail.map(f),
        }
    }

    #[inline]
    fn filter_map<F: FnMut(T) -> Option<U>>(
        self,
        mut f: F,
    ) -> Either<Self::Result, <Self::Result as Slist<U>>::Filter> {
        let (head, tail) = self.pop();
        if let Some(head) = f(head) {
            tail.filter_map(f).push(head)
        } else {
            Either::Right(tail.filter_map(f))
        }
    }
}

impl<U, T, N: SlistMap<T, U>, M: SlistMap<T, U>> SlistMap<T, U> for Either<N, M> {
    type Result = Either<N::Result, M::Result>;

    #[inline]
    fn map<F: FnMut(T) -> U>(self, f: F) -> Self::Result {
        match self {
            Either::Left(n) => Either::Left(n.map(f)),
            Either::Right(m) => Either::Right(m.map(f)),
        }
    }

    #[inline]
    fn filter_map<F: FnMut(T) -> Option<U>>(
        self,
        f: F,
    ) -> Either<Self::Result, <Self::Result as Slist<U>>::Filter> {
        match self {
            Either::Left(n) => match n.filter_map(f) {
                Either::Left(l) => Either::Left(Either::Left(l)),
                Either::Right(r) => Either::Right(Either::Left(r)),
            },
            Either::Right(m) => match m.filter_map(f) {
                Either::Left(l) => Either::Left(Either::Right(l)),
                Either::Right(r) => Either::Right(Either::Right(r)),
            },
        }
    }
}
