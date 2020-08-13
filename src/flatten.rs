//! Flatten a list of lists of type `U' into a list of `U`

use super::{Either, List, Slist, SlistSum};

use core::convert::Infallible;
use core::ops::Add;

/// Flatten a list of lists of type `U' into a list of `U'
pub trait SlistFlatten<T, U>: Slist<T>
where
    T: Slist<U>,
{
    /// Type of the flattened list
    type Flattened: Slist<U>;
    /// Flatten a list of lists into a list.
    /// # Example
    /// ```
    /// # use slist::{slist, SlistFlatten};
    /// let list = slist![slist![1, 2], slist![3; 2]];
    /// assert_eq!(list.flatten(), slist![1, 2, 3, 3]);
    /// ```
    fn flatten(self) -> Self::Flattened;
}

impl<T: Slist<U>, U> SlistFlatten<T, U> for Infallible {
    type Flattened = Infallible;

    #[inline]
    fn flatten(self) -> Self::Flattened {
        self
    }
}

impl<T: Slist<U>, U> SlistFlatten<T, U> for () {
    type Flattened = ();

    #[inline]
    fn flatten(self) -> Self::Flattened {}
}

impl<T, U, N, O> SlistFlatten<T, U> for List<T, N>
where
    T: Slist<U>,
    N: SlistFlatten<T, U>,
    N::Flattened: Add<T, Output = O>,
    N::Filter: SlistSum<T, Next = N>,
    O: Slist<U>,
{
    type Flattened = O;

    #[inline]
    fn flatten(self) -> Self::Flattened {
        self.tail.flatten() + self.head
    }
}

impl<T, U, N, M> SlistFlatten<T, U> for Either<N, M>
where
    T: Slist<U>,
    N: SlistFlatten<T, U>,
    M: SlistFlatten<T, U>,
{
    type Flattened = Either<N::Flattened, M::Flattened>;

    #[inline]
    fn flatten(self) -> Self::Flattened {
        match self {
            Either::Left(n) => Either::Left(n.flatten()),
            Either::Right(m) => Either::Right(m.flatten()),
        }
    }
}
