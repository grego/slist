#![no_std]
#![warn(missing_docs)]
//! s(tatic|tack)lists
//! Experimental algebraic lists with with statically determined size that live on stack.
//! They can be mapped, folded, filtered and have continuous storage.
//! `#![no_std]`, no const generics, no macros, no unsafe, no heap allocation nor boxing,
//! no dynamic dispatch, no dependencies, no unstable code used for the implementation.
//! Just the Rust trait system.
//!
//! Lists are constructed kind of like natural numbers in [Peano arithmetic](https://en.wikipedia.org/wiki/Peano_axioms).
//! For example, the type of a with 8 elements is
//! ```
//! # use slist::List;
//! # type T = u8;
//! let l: List<T, List<T, List<T, List<T, List<T, List<T, List<T, List<T, ()>>>>>>>>;
//! ```
//!
//! When the list is filtered, the result can be an arbitrary sublist, so the returned
//! type is a disjuncion of all lists smaller than the original:
//! ```
//! # use slist::{Either, List};
//! # use core::convert::Infallible;
//! # type T = u8;
//! let s: Either<List<T, List<T, List<T, List<T, List<T, List<T, List<T, List<T, ()>>>>>>>>, Either<List<T, List<T, List<T, List<T, List<T, List<T, List<T, ()>>>>>>>, Either<List<T, List<T, List<T, List<T, List<T, List<T, ()>>>>>>, Either<List<T, List<T, List<T, List<T, List<T, ()>>>>>, Either<List<T, List<T, List<T, List<T, ()>>>>, Either<List<T, List<T, List<T, ()>>>, Either<List<T, List<T, ()>>, Either<List<T, ()>, Either<(), Infallible>>>>>>>>>;
//! ```
//! Although very cumbersome to write, in the actual implementation, it has linear memory efficienncy and
//! is only one tag longer than the original, which is as short as it can get, since the length is
//! determined only on runtime. This way, computations can be performed on lists with variable but bounded length.
//!
//! `slist` macro can be used for quick list creation (the actual implementation contains no macros):
//! ```
//! use slist::prelude::*;
//!
//! let list = slist![0_usize, 3, 10, 19, 12, 22, 28, 13, 6].map(|i| i + 1);
//! let filtered = list.filter(|u| (u % 2) == 0);
//! assert_eq!(filtered + slist![3, 4, 5], slist![4, 20, 14, 3, 4, 5]);
//! assert_eq!(slist![6, 7] * slist![false, true], slist![(6, false), (7, false), (6, true), (7, true)]);
//! ```
//!
//! Note that when provided with an expression and size, the `slist` macro evaluates the expression
//! for each element separately. This is different to the array constructor (or the `vec` macro)
//! and can be used to iteratively build bounded lists, like of numbers from the standard input:
//! ```
//! use slist::prelude::*;
//! # use std::io::BufRead;
//!
//! let stdin = std::io::stdin();
//! let mut inputs = stdin.lock().lines().filter_map(Result::ok).map(|s| s.parse::<u16>().ok());
//!
//! let list = slist![inputs.next().flatten(); 4];
//! let list = list.filter_map(|i| i);
//! ```
//!
//! The macros are only used for convenience and are not necessary for the library to function.
//! For example, the following code gets expanded to:
//! ```
//! # use slist::prelude::*;
//! # use std::io::BufRead;
//! # let stdin = std::io::stdin();
//! # let mut inputs = stdin.lock().lines().filter_map(Result::ok).map(|s| s.parse::<u16>().ok());
//! let list = {
//!     use slist::List;
//!     let list: List<(), List<(), List<(), List<(), List<(), ()>>>>> = Default::default();
//!     list.map(|_| inputs.next().flatten())
//! };
//! ```
//! If you prefer to write natural numbers in Peano form, there is no need for any macros at all.
//!
//! Unfortunately, until [generic associated types](https://github.com/rust-lang/rfcs/blob/master/text/1598-generic_associated_types.md)
//! are stabilised, mapping of lists, resp. creating a list of references from a reference of a list
//! need to be provided by separate traits, `SlistMap<T, U>`, resp. `SlistAsRef<'a, T>`.
//! This crate provides a `prelude` module, from which every such trait can be conveniently imported.
//!
//! This crate can take a heavy toll on the compiler and using in in production can be adventurous.

/// Implementation of addition and multiplication for lists.
pub mod arithmetic;
/// Implementation of equality traits for lists.
pub mod eq;
/// A helper module, exporting all traits for convenient working with lists.
pub mod prelude {
    pub use crate::{slist, Slist, SlistAsRef, SlistFlatten, SlistMap, SlistReverse, SlistSum};
}

pub mod as_ref;
pub mod flatten;
pub mod map;
pub mod reverse;

pub use as_ref::SlistAsRef;
pub use flatten::SlistFlatten;
pub use map::SlistMap;
pub use reverse::SlistReverse;
pub use slist_derive::slist_typegen;

use core::cmp::Ordering;
// TODO: replace with `!` (the never type) once stabilised
use core::convert::Infallible;
use core::fmt::{self, Display, Formatter};
use core::ops::{Add, Index, IndexMut};

/// A trait representing static stack lists.
pub trait Slist<T>: Sized {
    /// The largest number of element the type can contain.
    const MAXLEN: usize = 0;
    /// A type that is returned when at least one element is filtered out
    /// via the `filter` method.
    type Filter;
    /// Keep only the elements in the list that satisfy the given closure `f`.
    /// The closure must return `true` or `false`. Only the elemets for whic it returns
    /// `true` are retained.
    #[inline]
    fn filter<F: FnMut(&T) -> bool>(self, _f: F) -> Either<Self, Self::Filter> {
        Either::Left(self)
    }
    /// Apply the closure `f` on the list, producing a single, final value.
    /// `foldr` takes 2 argumetst: an initial value (an `accumulator`) and a closure
    /// that computes a new value of the accumulator from the old one and an element
    /// of the list. After going through each element this way, the final value of the
    /// accumulator is yielded.
    /// This is the "right" variant of fold, meaning (in the `slist` conventions) that
    /// the closure is applied on the elements "from left to right".
    #[inline]
    fn foldr<U, F: FnMut(U, T) -> U>(self, acc: U, _f: &mut F) -> U {
        acc
    }

    /// Apply the closure `f` on the list, producing a single, final value.
    /// `foldl` takes 2 arguments: an initial value (an `accumulator`) and a closure
    /// that computes a new value of the accumulator from the old one and an element
    /// of the list. After going through each element this way, the final value of the
    /// accumulator is yielded.
    /// This is the "left" variant of fold, meaning (in the `slist` conventions) that
    /// the closure is applied on the elements "from right to left".
    #[inline]
    fn foldl<U, F: FnMut(U, T) -> U>(self, acc: U, _f: F) -> U {
        acc
    }

    /// Run the closure `f` for each element of the list.
    #[inline]
    fn for_each<F: FnMut(T)>(self, _f: F) {}

    /// Sum the elements of the list, for types that implement addition.
    #[inline]
    fn sum<U>(self) -> U
    where
        U: Add<T, Output = U> + Default,
    {
        self.foldl(U::default(), U::add)
    }

    /// Get a reference of the element at `index`, or return `None`
    /// if `index` is out of the list.
    #[inline]
    fn get(&self, _index: usize) -> Option<&T> {
        None
    }

    /// Get a mutable reference of the element at `index`, or return `None`
    /// if `index` is out of the list.
    #[inline]
    fn get_mut(&mut self, _index: usize) -> Option<&mut T> {
        None
    }

    /// Display elements of the list to the formatter. A convenience method for
    /// implementing `Display` for list elements.
    #[inline]
    fn view(&self, _f: &mut Formatter<'_>) -> fmt::Result
    where
        T: Display,
    {
        Ok(())
    }

    /// Get the length of the list.
    #[inline]
    fn len(&self) -> usize {
        Self::MAXLEN
    }

    /// Returns `true` if the list contains no elements, otherwise returns `false`.
    #[inline]
    fn is_empty(&self) -> bool {
        true
    }
}

/// A disjunction of all the list types of type `T`, up to a certain length.
/// Used for implementing `filter` for lists.
pub trait SlistSum<T>: Slist<T> {
    /// The next list that is not in the disjunction.
    /// The smallest list of type T that is larger than any of the lists in the current type.
    type Next: Slist<T>;
    /// Add another element to this list, possibly making it larger.
    fn push(self, item: T) -> Either<Self::Next, Self>;
}

/// A list type that contains an element of type `T` and another element, which is either another
/// list type or unit (`()`).
/// By convention, the given element is considered the last item on the list, although the compiler
/// is free to rearrange the order as it feels.
#[derive(Debug, Default)]
pub struct List<T, N: Slist<T>> {
    tail: N,
    head: T,
}

/// A disjuncion of two possible values.
/// By nesting of `Either`s, a disjuncion of lists of all lengths up to a certain bound
/// is created.
#[derive(Debug)]
pub enum Either<N, M> {
    /// Left variant
    Left(N),
    /// Right variant
    Right(M),
}

impl<T> Slist<T> for Infallible {
    type Filter = Infallible;
}

impl<T> Slist<T> for () {
    type Filter = Infallible;
}

/// For soundness reasons, `Slist` should be implemented only for those lists that contain
/// another lists.
/// Although this cannot be ensured within the Rust trait system (another type may implement
/// a public trait) without resorting to private modules, it is at least made sure that `Slist`
/// is implemented only for those lists, whose `filter` function will return the `Either` variant
/// containing the list itself if none of its items is filtered out.
impl<T, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> Slist<T> for List<T, N> {
    const MAXLEN: usize = 1 + N::MAXLEN;

    type Filter = Either<N, N::Filter>;

    #[inline]
    fn foldr<U, F: FnMut(U, T) -> U>(self, acc: U, f: &mut F) -> U {
        let acc = self.tail.foldr(acc, f);
        f(acc, self.head)
    }

    #[inline]
    fn foldl<U, F: FnMut(U, T) -> U>(self, acc: U, mut f: F) -> U {
        self.tail.foldl(f(acc, self.head), f)
    }

    #[inline]
    fn filter<F: FnMut(&T) -> bool>(self, mut f: F) -> Either<Self, Self::Filter> {
        let (head, tail) = self.pop();
        if f(&head) {
            tail.filter(f).push(head)
        } else {
            Either::Right(tail.filter(f))
        }
    }

    #[inline]
    fn for_each<F: FnMut(T)>(self, mut f: F) {
        f(self.head);
        self.tail.for_each(f);
    }

    #[inline]
    fn get(&self, index: usize) -> Option<&T> {
        match index.cmp(&(Self::MAXLEN - 1)) {
            Ordering::Greater => None,
            Ordering::Equal => Some(&self.head),
            Ordering::Less => self.tail.get(index),
        }
    }

    #[inline]
    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        match index.cmp(&(Self::MAXLEN - 1)) {
            Ordering::Greater => None,
            Ordering::Equal => Some(&mut self.head),
            Ordering::Less => self.tail.get_mut(index),
        }
    }

    #[inline]
    fn view(&self, f: &mut Formatter<'_>) -> fmt::Result
    where
        T: Display,
    {
        self.tail.view(f)?;
        write!(f, "{}, ", &self.head)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        false
    }
}

impl<T, N: Slist<T>, M: Slist<T>> Slist<T> for Either<N, M> {
    const MAXLEN: usize = [N::MAXLEN, M::MAXLEN][(N::MAXLEN < M::MAXLEN) as usize];

    type Filter = Either<N::Filter, M::Filter>;

    #[inline]
    fn foldr<U, F: FnMut(U, T) -> U>(self, acc: U, f: &mut F) -> U {
        match self {
            Either::Left(n) => n.foldr(acc, f),
            Either::Right(m) => m.foldr(acc, f),
        }
    }

    #[inline]
    fn foldl<U, F: FnMut(U, T) -> U>(self, acc: U, f: F) -> U {
        match self {
            Either::Left(n) => n.foldl(acc, f),
            Either::Right(m) => m.foldl(acc, f),
        }
    }

    #[inline]
    fn filter<F: FnMut(&T) -> bool>(self, f: F) -> Either<Self, Self::Filter> {
        match self {
            Either::Left(n) => match n.filter(f) {
                Either::Left(l) => Either::Left(Either::Left(l)),
                Either::Right(r) => Either::Right(Either::Left(r)),
            },
            Either::Right(m) => match m.filter(f) {
                Either::Left(l) => Either::Left(Either::Right(l)),
                Either::Right(r) => Either::Right(Either::Right(r)),
            },
        }
    }

    #[inline]
    fn for_each<F: FnMut(T)>(self, f: F) {
        match self {
            Either::Left(n) => n.for_each(f),
            Either::Right(m) => m.for_each(f),
        }
    }

    #[inline]
    fn get(&self, index: usize) -> Option<&T> {
        match self {
            Either::Left(n) => n.get(index),
            Either::Right(m) => m.get(index),
        }
    }

    #[inline]
    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        match self {
            Either::Left(n) => n.get_mut(index),
            Either::Right(m) => m.get_mut(index),
        }
    }

    #[inline]
    fn len(&self) -> usize {
        match self {
            Either::Left(n) => n.len(),
            Either::Right(m) => m.len(),
        }
    }

    #[inline]
    fn is_empty(&self) -> bool {
        match self {
            Either::Left(n) => n.is_empty(),
            Either::Right(m) => m.is_empty(),
        }
    }
}

impl<T> SlistSum<T> for () {
    type Next = List<T, ()>;

    #[inline]
    fn push(self, item: T) -> Either<Self::Next, ()> {
        Either::Left(List::new(item))
    }
}

impl<T> SlistSum<T> for Infallible {
    type Next = ();

    #[inline]
    fn push(self, _: T) -> Either<Self::Next, Self> {
        Either::Left(())
    }
}

impl<T, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> SlistSum<T> for Either<N, S> {
    type Next = List<T, N>;

    #[inline]
    fn push(self, item: T) -> Either<Self::Next, Self> {
        match self {
            Either::Left(l) => Either::Left(List {
                head: item,
                tail: l,
            }),
            Either::Right(r) => Either::Right(r.push(item)),
        }
    }
}

impl<T> List<T, ()> {
    /// Create a new list, containing one item.
        #[inline]pub const
    fn new(first: T) -> Self {
        List {
            head: first,
            tail: (),
        }
    }
}

impl<T, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> List<T, N> {
    /// Push the `item` at the end of the list.
        #[inline]pub
    fn push(self, item: T) -> List<T, Self> {
        List {
            head: item,
            tail: self,
        }
    }

    /// "Tear" the list into a tuple, containing the last element and a list
    /// consting of the rest of the original list.
        #[inline]pub
    fn pop(self) -> (T, N) {
        (self.head, self.tail)
    }
}

impl<T, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> Index<usize> for List<T, N> {
    type Output = T;
    #[inline]
    fn index(&self, index: usize) -> &T {
        self.get(index).unwrap()
    }
}

impl<T, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> IndexMut<usize> for List<T, N> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index).unwrap()
    }
}

impl<T, N, M> Index<usize> for Either<N, M>
where
    N: Slist<T> + Index<usize, Output = T>,
    M: Slist<T> + Index<usize, Output = T>,
{
    type Output = T;
    #[inline]
    fn index(&self, index: usize) -> &T {
        match self {
            Either::Left(n) => n.index(index),
            Either::Right(m) => m.index(index),
        }
    }
}

impl<T, N, M> IndexMut<usize> for Either<N, M>
where
    N: Slist<T> + Index<usize, Output = T> + IndexMut<usize>,
    M: Slist<T> + Index<usize, Output = T> + IndexMut<usize>,
{
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        match self {
            Either::Left(n) => n.index_mut(index),
            Either::Right(m) => m.index_mut(index),
        }
    }
}

impl<T: Display, N: Slist<T, Filter = S>, S: SlistSum<T, Next = N>> Display for List<T, N> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        self.tail.view(f)?;
        write!(f, "{}]", &self.head)
    }
}

impl<N: Display, M: Display> Display for Either<N, M> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(n) => write!(f, "{}", &n),
            Either::Right(m) => write!(f, "_{}", &m),
        }
    }
}

impl<T: Clone, N: Clone + Slist<T>> Clone for List<T, N> {
    #[inline]
    fn clone(&self) -> Self {
        List {
            head: self.head.clone(),
            tail: self.tail.clone(),
        }
    }
}

impl<T: Copy, N: Copy + Slist<T>> Copy for List<T, N> {}

impl<N: Clone, M: Clone> Clone for Either<M, N> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Either::Left(n) => Either::Left(n.clone()),
            Either::Right(m) => Either::Right(m.clone()),
        }
    }
}

impl<N: Copy, M: Copy> Copy for Either<N, M> {}

impl<N: Default, M> Default for Either<N, M> {
    #[inline]
    fn default() -> Self {
        Either::Left(N::default())
    }
}

/// Creates a list containing the arguments.
///
/// `slist!` allows the lists to be defined with the same syntax as array expressions.
/// There are two forms of this macro:
///
/// - Create a list containing given elements:
///
/// ```
/// # use slist::slist;
/// let list = slist![1, 2, 3];
/// assert_eq!(list[0], 1);
/// assert_eq!(list[1], 2);
/// assert_eq!(list[2], 3);
/// ```
///
/// - Create a list from a given expression and size:
///
/// ```
/// # use slist::slist;
/// let list = slist![1; 3];
/// assert_eq!(list, slist![1, 1, 1]);
/// ```
///
/// Note that unlike array constructors and the `vec` macro, the given expression
/// is evaluated for each element separately. This allows building the lists iteratively:
/// ```
/// use slist::prelude::*;
///
/// let mut i = 0;
/// let mut f = || {
///     i += 1;
///     i
/// };
/// let list = slist![f(); 3];
/// assert_eq!(list.reverse(), slist![1, 2, 3]);
#[macro_export]
macro_rules! slist {
    ($s:expr $(, $x:expr)*) => (
        $crate::List::new($s)$(.push($x))*
    );
    ($elem:expr; $n:expr) => (
        {
            use $crate::{slist_typegen, List, SlistMap};
            let list: $crate::slist_typegen!($n) = Default::default();
            list.map(|_| $elem)
        }
    );
}
