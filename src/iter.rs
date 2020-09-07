use crate::{Either, List, Slist, SlistSum, Void};

use core::iter::IntoIterator;

impl<T, N, S> IntoIterator for List<T, N>
where
    N: Slist<T, Filter = S>,
    S: SlistSum<T, Next = N>,
    Either<Self, Either<N, S>>: Iterator<Item = T>,
{
    type Item = T;
    type IntoIter = Either<Self, Either<N, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.filter(|_| true)
    }
}
    
impl<T, N, S> Iterator for Either<List<T, N>, Either<N, S>>
where
    N: Slist<T, Filter = S>,
    S: SlistSum<T, Next = N> + Default,
    Either<N, S>: Iterator<Item = T>,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Either::Left(_) => {
                let owned = core::mem::take(self);
                if let Either::Left(list) = owned {
                    *self = Either::Right(Either::Left(list.tail));
                    Some(list.head)
                } else {
                    unreachable!();
                }
            }
            Either::Right(ref mut r) => r.next(),
        }
    }
}

impl<T> Iterator for Either<List<T, ()>, Either<(), Void>>
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Either::Left(_) => {
                let owned = core::mem::take(self);
                if let Either::Left(list) = owned {
                    Some(list.head)
                } else {
                    unreachable!();
                }
            }
            Either::Right(_) => None,
        }
    }
}
