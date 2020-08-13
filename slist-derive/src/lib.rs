#![warn(missing_docs)]
//! A procedural macros that allow conversion of a non-negative integer `n` to the type
//! `List` of the `slist` crate of length `n`.
extern crate proc_macro;
use proc_macro::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};

fn parse_argument(item: TokenStream) -> Option<usize> {
    let mut iter = item.into_iter();

    let size = match iter.next()? {
        TokenTree::Literal(lit) => lit.to_string().parse().ok(),
        // Literal passed from a macro
        TokenTree::Group(group) if group.delimiter() == Delimiter::None => {
            let mut iter = group.stream().into_iter();
            let size = match iter.next()? {
                TokenTree::Literal(lit) => lit.to_string().parse().ok(),
                _ => None,
            };
            iter.next().map(drop).xor(Some(()))?;
            size
        }
        _ => None,
    }?;

    iter.next().map(drop).xor(Some(()))?;
    Some(size)
}

/// Generate a type of a list of units (`()`) of the given length.
/// The only valid input is a non-negative integer literal.
/// The type `List` of the `slist` crate needs to be imported in order for the resulting type
/// to be parsed correctly.
///
/// # Example
/// ```ignore
/// use slist::{slist_typegen, List};
/// let list: slist_typegen!(4) = Default::default();
/// let mut i = 0;
/// let list = list.map(|_| {
///     i += 1;
///     i
/// });
/// ```
#[proc_macro]
pub fn slist_typegen(item: TokenStream) -> TokenStream {
    let size =
        parse_argument(item).expect("Wrong argument; expected a literal non-negative integer");

    let empty: TokenTree = Group::new(Delimiter::Parenthesis, TokenStream::new()).into();
    let mut output: TokenStream = empty.clone().into();
    let start = [
        Ident::new("List", Span::call_site()).into(),
        Punct::new('<', Spacing::Alone).into(),
        empty,
        Punct::new(',', Spacing::Alone).into(),
    ];
    let end = [Punct::new('>', Spacing::Alone).into()];
    for _ in 0..size {
        output = start
            .iter()
            .cloned()
            .chain(output.into_iter())
            .chain(end.iter().cloned())
            .collect()
    }

    output
}
