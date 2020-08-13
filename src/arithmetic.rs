use super::{Either, List, Slist, SlistMap, SlistSum};

use core::convert::Infallible;
use core::ops::{Add, Mul};

impl<T, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> Add<()> for List<T, N> {
    type Output = Self;

    #[inline]
    fn add(self, _: ()) -> Self::Output {
        self
    }
}

impl<T, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> Add<List<T, N>> for () {
    type Output = List<T, N>;

    #[inline]
    fn add(self, other: List<T, N>) -> Self::Output {
        other
    }
}

impl<T, N, M, O> Add<List<T, M>> for List<T, N>
where
    N: Slist<T>,
    M: Slist<T>,
    Self: Add<M, Output = O>,
    O: Slist<T>,
    N::Filter: SlistSum<T, Next = N>,
    M::Filter: SlistSum<T, Next = M>,
    O::Filter: SlistSum<T, Next = O>,
{
    type Output = List<T, O>;

    #[inline]
    fn add(self, other: List<T, M>) -> Self::Output {
        List {
            head: other.head,
            tail: self + other.tail,
        }
    }
}

impl<T, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> Mul<()> for List<T, N> {
    type Output = ();

    #[inline]
    fn mul(self, _: ()) -> Self::Output {}
}

impl<T, U, N, M, O, P> Mul<List<U, M>> for List<T, N>
where
    T: Clone,
    U: Clone,
    N: Slist<T> + SlistMap<T, (T, U), Result = P> + Clone,
    M: Slist<U> + Clone,
    Self: Mul<M, Output = O>,
    O: Slist<(T, U)> + Add<List<(T, U), P>>,
    P: Slist<(T, U)>,
    O::Output: Slist<(T, U)>,
    N::Filter: SlistSum<T, Next = N>,
    M::Filter: SlistSum<U, Next = M>,
    O::Filter: SlistSum<(T, U), Next = O>,
    P::Filter: SlistSum<(T, U), Next = P>,
{
    type Output = O::Output;

    #[inline]
    fn mul(self, other: List<U, M>) -> Self::Output {
        let (head, tail) = other.pop();
        self.clone() * tail + self.map(|i| (i, head.clone()))
    }
}

impl<T, N: Add<T>, M: Add<T>> Add<T> for Either<N, M> {
    type Output = Either<N::Output, M::Output>;

    #[inline]
    fn add(self, other: T) -> Self::Output {
        match self {
            Either::Left(n) => Either::Left(n + other),
            Either::Right(m) => Either::Right(m + other),
        }
    }
}

impl<N, M> Add<Either<N, M>> for () {
    type Output = Either<N, M>;

    #[inline]
    fn add(self, other: Either<N, M>) -> Self::Output {
        other
    }
}

impl<T, S: Slist<T>, N, M, O1, O2> Add<Either<N, M>> for List<T, S>
where
    List<T, S>: Add<N, Output = O1> + Add<M, Output = O2>,
{
    type Output = Either<O1, O2>;

    #[inline]
    fn add(self, other: Either<N, M>) -> Self::Output {
        match other {
            Either::Left(n) => Either::Left(self + n),
            Either::Right(m) => Either::Right(self + m),
        }
    }
}

impl<T, N: Mul<T>, M: Mul<T>> Mul<T> for Either<N, M> {
    type Output = Either<N::Output, M::Output>;

    #[inline]
    fn mul(self, other: T) -> Self::Output {
        match self {
            Either::Left(n) => Either::Left(n * other),
            Either::Right(m) => Either::Right(m * other),
        }
    }
}

impl<N, M> Mul<Either<N, M>> for () {
    type Output = ();

    #[inline]
    fn mul(self, _: Either<N, M>) -> Self::Output {}
}

impl<T, S: Slist<T>, N, M, O1, O2> Mul<Either<N, M>> for List<T, S>
where
    List<T, S>: Mul<N, Output = O1> + Mul<M, Output = O2>,
{
    type Output = Either<O1, O2>;

    #[inline]
    fn mul(self, other: Either<N, M>) -> Self::Output {
        match other {
            Either::Left(n) => Either::Left(self * n),
            Either::Right(m) => Either::Right(self * m),
        }
    }
}

impl<T, N: Slist<T>> Add<Infallible> for List<T, N> {
    type Output = Infallible;

    #[inline]
    fn add(self, other: Infallible) -> Self::Output {
        other
    }
}

impl<T, N: Slist<T>> Add<List<T, N>> for Infallible {
    type Output = Infallible;

    #[inline]
    fn add(self, _: List<T, N>) -> Self::Output {
        self
    }
}

impl<T, N: Slist<T>> Mul<Infallible> for List<T, N> {
    type Output = Infallible;

    #[inline]
    fn mul(self, other: Infallible) -> Self::Output {
        other
    }
}

impl<T, N: Slist<T>> Mul<List<T, N>> for Infallible {
    type Output = Infallible;

    #[inline]
    fn mul(self, _: List<T, N>) -> Self::Output {
        self
    }
}

impl<M, N> Add<Either<N, M>> for Infallible {
    type Output = Infallible;

    #[inline]
    fn add(self, _: Either<N, M>) -> Self::Output {
        self
    }
}

impl<M, N> Mul<Either<N, M>> for Infallible {
    type Output = Infallible;

    #[inline]
    fn mul(self, _: Either<N, M>) -> Self::Output {
        self
    }
}
