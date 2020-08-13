# s(tatic|tack)lists
[![Build status](https://badgen.net/github/status/grego/slist)](https://github.com/grego/slist/actions?query=workflow%3Atests) 
[![Crates.io status](https://badgen.net/crates/v/slist)](https://crates.io/crates/slist)
[![Docs](https://docs.rs/slist/badge.svg)](https://docs.rs/slist)

Experimental algebraic lists with with statically determined size that live on stack.
They can be mapped, folded, filtered and have continuous storage.
`#![no_std]`, no const generics, no macros, no unsafe, no heap allocation nor boxing,
no dynamic dispatch, no dependencies, no unstable code used for the implementation.
Just the Rust trait system.

Lists are constructed kind of like natural numbers in [Peano arithmetic](https://en.wikipedia.org/wiki/Peano_axioms).
For example, the type of a list with 8 elements is
```rust
let l: List<T, List<T, List<T, List<T, List<T, List<T, List<T, List<T, ()>>>>>>>>;
```

When the list is filtered, the result can be an arbitrary sublist, so the returned
type is a disjuncion of all lists smaller than the original:
```rust
let s: Either<List<T, List<T, List<T, List<T, List<T, List<T, List<T, List<T, ()>>>>>>>>, Either<List<T, List<T, List<T, List<T, List<T, List<T, List<T, ()>>>>>>>, Either<List<T, List<T, List<T, List<T, List<T, List<T, ()>>>>>>, Either<List<T, List<T, List<T, List<T, List<T, ()>>>>>, Either<List<T, List<T, List<T, List<T, ()>>>>, Either<List<T, List<T, List<T, ()>>>, Either<List<T, List<T, ()>>, Either<List<T, ()>, Either<(), Infallible>>>>>>>>>;
```
Although very cumbersome to write, in the actual implementation, it has linear memory efficienncy and
is only one tag longer than the original, which is as short as it can get, since the length is
determined only on runtime. This way, computations can be performed on lists with variable but bounded length.

`slist` macro can be used for quick list creation (the actual implementation contains no macros):
```rust
use slist::prelude::*;

let list = slist![0_usize, 3, 10, 19, 12, 22, 28, 13, 6].map(|i| i + 1);
let filtered = list.filter(|u| (u % 2) == 0);
assert_eq!(filtered + slist![3, 4, 5], slist![4, 20, 14, 3, 4, 5]);
assert_eq!(slist![6, 7] * slist![false, true], slist![(6, false), (7, false), (6, true), (7, true)]);
```

Note that when provided with an expression and size, the `slist` macro evaluates the expression
for each element separately. This is different to the array constructor (or the `vec` macro)
and can be used to iteratively build bounded lists, like of numbers from the standard input:
```rust
use slist::prelude::*;

let stdin = std::io::stdin();
let mut inputs = stdin.lock().lines().filter_map(Result::ok).map(|s| s.parse::<u16>().ok());

let list = slist![inputs.next().flatten(); 4];
let list = list.filter_map(|i| i);
```

The macros are only used for convenience and are not necessary for the library to function.
For example, the preceding code gets expanded to:
```rust
let list = {
    use slist::List;
    let list: List<(), List<(), List<(), List<(), List<(), ()>>>>> = Default::default();
    list.map(|_| inputs.next().flatten())
};
```
If you prefer to write natural numbers in Peano form, there is no need for any macros at all.

Unfortunately, until [generic associated types](https://github.com/rust-lang/rfcs/blob/master/text/1598-generic_associated_types.md)
are stabilised, mapping of lists, resp. creating a list of references from a reference of a list
need to be provided by separate traits, `SlistMap<T, U>`, resp. `SlistAsRef<'a, T>`.
This crate provides a `prelude` module, from which every such trait can be conveniently imported.

This crate can take a heavy toll on the compiler and using in in production can be adventurous.

License: MIT
