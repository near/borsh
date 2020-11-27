extern crate proc_macro;
use borsh_derive_internal::*;
use borsh_schema_derive_internal::*;
use proc_macro::TokenStream;
use proc_macro_crate::crate_name;
use syn::export::Span;
use syn::{Ident, ItemEnum, ItemStruct, ItemUnion};

#[proc_macro_derive(BorshSerialize, attributes(borsh_skip))]
pub fn borsh_serialize(input: TokenStream) -> TokenStream {
    let cratename = Ident::new(
        &crate_name("borsh").unwrap_or("borsh".to_string()),
        Span::call_site(),
    );

    let res = if let Ok(input) = syn::parse::<ItemStruct>(input.clone()) {
        struct_ser(&input, cratename)
    } else if let Ok(input) = syn::parse::<ItemEnum>(input.clone()) {
        enum_ser(&input, cratename)
    } else if let Ok(input) = syn::parse::<ItemUnion>(input.clone()) {
        union_ser(&input, cratename)
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
    let cratename = Ident::new(
        &crate_name("borsh").unwrap_or("borsh".to_string()),
        Span::call_site(),
    );

    let res = if let Ok(input) = syn::parse::<ItemStruct>(input.clone()) {
        struct_de(&input, cratename)
    } else if let Ok(input) = syn::parse::<ItemEnum>(input.clone()) {
        enum_de(&input, cratename)
    } else if let Ok(input) = syn::parse::<ItemUnion>(input.clone()) {
        union_de(&input, cratename)
    } else {
        // Derive macros can only be defined on structs, enums, and unions.
        unreachable!()
    };
    TokenStream::from(match res {
        Ok(res) => res,
        Err(err) => err.to_compile_error(),
    })
}

#[proc_macro_derive(BorshSchema, attributes(borsh_skip))]
pub fn borsh_schema(input: TokenStream) -> TokenStream {
    let cratename = Ident::new(
        &crate_name("borsh").unwrap_or("borsh".to_string()),
        Span::call_site(),
    );

    let res = if let Ok(input) = syn::parse::<ItemStruct>(input.clone()) {
        process_struct(&input, cratename)
    } else if let Ok(input) = syn::parse::<ItemEnum>(input.clone()) {
        process_enum(&input, cratename)
    } else if let Ok(_) = syn::parse::<ItemUnion>(input.clone()) {
        Err(syn::Error::new(
            Span::call_site(),
            "Borsh schema does not support unions yet.",
        ))
    } else {
        // Derive macros can only be defined on structs, enums, and unions.
        unreachable!()
    };
    TokenStream::from(match res {
        Ok(res) => res,
        Err(err) => err.to_compile_error(),
    })
}
