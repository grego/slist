//! Reverse the direction of a list

use super::{Either, List, Slist, SlistSum, Void};

use core::ops::Add;

/// Reverse the direction of a list.
pub trait SlistReverse<T>: Slist<T> {
    /// Reverse the direction of the list. The first item becomes the last, the second
    /// the second last and so on.
    fn reverse(self) -> Self;
}

impl<T> SlistReverse<T> for Void {
    #[inline]
    fn reverse(self) -> Self {
        self
    }
}

impl<T> SlistReverse<T> for () {
    #[inline]
    fn reverse(self) -> Self {
        self
    }
}

impl<T, N> SlistReverse<T> for List<T, N> where
    N: SlistReverse<T> + Slist<T>,
    N::Filter: SlistSum<T, Next = N>,
    List<T, ()>: Add<N, Output = Self>,
{
    #[inline]
    fn reverse(self) -> Self {
        List::new(self.head) + self.tail.reverse()
    }
}

impl<T, N: SlistReverse<T>, M: SlistReverse<T>> SlistReverse<T> for Either<N, M> {
    #[inline]
    fn reverse(self) -> Self {
        match self {
            Either::Left(n) => Either::Left(n.reverse()),
            Either::Right(m) => Either::Right(m.reverse()),
        }
    }
}
