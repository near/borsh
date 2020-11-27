use syn::export::TokenStream2;
use syn::{Ident, ItemUnion};

pub fn union_ser(_input: &ItemUnion, _cratename: Ident) -> syn::Result<TokenStream2> {
    unimplemented!()
}
