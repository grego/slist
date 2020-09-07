use super::{Either, List, Slist, SlistSum, Void};

impl<T, U, N, M> PartialEq<List<U, M>> for List<T, N>
where
    T: PartialEq<U>,
    U: PartialEq<T>,
    N: PartialEq<M> + Slist<T>,
    M: PartialEq<N> + Slist<U>,
    N::Filter: SlistSum<T, Next = N>,
    M::Filter: SlistSum<U, Next = M>,
{
    #[inline]
    fn eq(&self, other: &List<U, M>) -> bool {
        if <Self as Slist<T>>::MAXLEN != <List<U, M> as Slist<U>>::MAXLEN || self.head != other.head
        {
            return false;
        }
        self.tail.eq(&other.tail)
    }
}

impl<N1, M1, N2, M2> PartialEq<Either<N2, M2>> for Either<N1, M1>
where
    N1: PartialEq<N2> + PartialEq<M2>,
    M1: PartialEq<N2> + PartialEq<M2>,
{
    #[inline]
    fn eq(&self, other: &Either<N2, M2>) -> bool {
        match self {
            Either::Left(n) => match other {
                Either::Left(l) => n.eq(l),
                Either::Right(r) => n.eq(r),
            },
            Either::Right(m) => match other {
                Either::Left(l) => m.eq(l),
                Either::Right(r) => m.eq(r),
            },
        }
    }
}

impl<N: Eq + PartialEq<M>, M: Eq + PartialEq<N>> Eq for Either<N, M> {}

impl<T, S, N, M> PartialEq<List<T, S>> for Either<N, M>
where
    S: Slist<T>,
    N: PartialEq<List<T, S>>,
    M: PartialEq<List<T, S>>,
{
    #[inline]
    fn eq(&self, other: &List<T, S>) -> bool {
        match self {
            Either::Left(n) => n.eq(other),
            Either::Right(m) => m.eq(other),
        }
    }
}

impl<T, N: Slist<T>> PartialEq<Void> for List<T, N> {
    #[inline]
    fn eq(&self, _: &Void) -> bool {
        false
    }
}

impl<T, N: Slist<T>> PartialEq<List<T, N>> for Void {
    #[inline]
    fn eq(&self, _: &List<T, N>) -> bool {
        false
    }
}

impl<T, N: Slist<T>> PartialEq<List<T, N>> for () {
    #[inline]
    fn eq(&self, _: &List<T, N>) -> bool {
        false
    }
}

impl<T, N: Slist<T>> PartialEq<()> for List<T, N> {
    #[inline]
    fn eq(&self, _: &()) -> bool {
        false
    }
}

impl<N, M> PartialEq<Void> for Either<N, M> {
    #[inline]
    fn eq(&self, _: &Void) -> bool {
        false
    }
}

impl<N, M> PartialEq<()> for Either<N, M> {
    #[inline]
    fn eq(&self, _: &()) -> bool {
        false
    }
}

impl<N, M> PartialEq<Either<N, M>> for Void {
    #[inline]
    fn eq(&self, _: &Either<N, M>) -> bool {
        false
    }
}

impl<N, M> PartialEq<Either<N, M>> for () {
    #[inline]
    fn eq(&self, _: &Either<N, M>) -> bool {
        false
    }
}
