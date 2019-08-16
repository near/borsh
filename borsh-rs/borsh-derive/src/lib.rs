#![recursion_limit = "128"]
extern crate proc_macro;

use borsh_derive_internal::*;
use proc_macro::TokenStream;
use syn::{ItemEnum, ItemStruct, ItemUnion};

#[proc_macro_derive(BorshSerialize, attributes(borsh_skip))]
pub fn borsh_serialize(input: TokenStream) -> TokenStream {
    let res = if let Ok(input) = syn::parse::<ItemStruct>(input.clone()) {
        struct_ser(&input)
    } else if let Ok(input) = syn::parse::<ItemEnum>(input.clone()) {
        enum_ser(&input)
    } else if let Ok(input) = syn::parse::<ItemUnion>(input.clone()) {
        union_ser(&input)
    } else {
        // Derive macros can only be defined on structs, enums, and unions.
        unreachable!()
    };
    TokenStream::from(match res {
        Ok(res) => res,
        Err(err) => err.to_compile_error(),
    })
}

#[proc_macro_derive(BorshDeserialize, attributes(borsh_skip, borsh_init))]
pub fn borsh_deserialize(input: TokenStream) -> TokenStream {
    let res = if let Ok(input) = syn::parse::<ItemStruct>(input.clone()) {
        struct_de(&input)
    } else if let Ok(input) = syn::parse::<ItemEnum>(input.clone()) {
        enum_de(&input)
    } else if let Ok(input) = syn::parse::<ItemUnion>(input.clone()) {
        union_de(&input)
    } else {
        // Derive macros can only be defined on structs, enums, and unions.
        unreachable!()
    };
    TokenStream::from(match res {
        Ok(res) => res,
        Err(err) => err.to_compile_error(),
    })
}
