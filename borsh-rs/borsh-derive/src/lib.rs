#![recursion_limit = "128"]
extern crate proc_macro;

use proc_macro::TokenStream;
use borsh_derive_internal::*;
use syn::{ItemStruct, ItemEnum, ItemUnion};

#[proc_macro_derive(BorshSerialize, attributes(borsh_skip))]
pub fn borsh_serialize(input: TokenStream) -> TokenStream {
    if let Ok(input) = syn::parse::<ItemStruct>(input.clone()) {
        TokenStream::from(borsh_struct_ser(&input))
    } else if let Ok(input) = syn::parse::<ItemEnum>(input.clone()) {
        TokenStream::from(borsh_enum_ser(&input))
    } else if let Ok(input) = syn::parse::<ItemUnion>(input.clone()) {
        TokenStream::from(borsh_union_ser(&input))
    } else {
        // Derive macros can only be defined on structs, enums, and unions.
        unreachable!()
    }
}


#[proc_macro_derive(BorshDeserialize, attributes(borsh_skip, borsh_init))]
pub fn borsh_deserialize(input: TokenStream) -> TokenStream {
    if let Ok(input) = syn::parse::<ItemStruct>(input.clone()) {
        TokenStream::from(borsh_struct_de(&input))
    } else if let Ok(input) = syn::parse::<ItemEnum>(input.clone()) {
        TokenStream::from(borsh_enum_de(&input))
    } else if let Ok(input) = syn::parse::<ItemUnion>(input.clone()) {
        TokenStream::from(borsh_union_de(&input))
    } else {
        // Derive macros can only be defined on structs, enums, and unions.
        unreachable!()
    }
}

