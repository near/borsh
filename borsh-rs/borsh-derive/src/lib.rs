extern crate proc_macro;

use borsh_derive_internal::*;
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{parse_macro_input, Ident, ItemEnum, ItemStruct, ItemUnion, LitInt, Token};

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

struct SeqMacroSpec {
    mac_ident: Ident,
    prefix: Option<Ident>,
    lengths: Vec<usize>,
}

impl syn::parse::Parse for SeqMacroSpec {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mac_ident = input.parse()?;
        input.parse::<Token![=>]>()?;

        let prefix = input.parse::<Option<Ident>>()?;
        if prefix.is_some() {
            input.parse::<Token![::]>()?;
        }

        let seq_lengths;
        syn::parenthesized!(seq_lengths in input);
        let punctuated_lengths: syn::punctuated::Punctuated<LitInt, syn::parse::Nothing> =
            seq_lengths.parse_terminated(LitInt::parse)?;
        let lengths = punctuated_lengths
            .iter()
            .map(|l| l.base10_parse::<usize>())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(SeqMacroSpec {
            mac_ident,
            prefix,
            lengths,
        })
    }
}

#[proc_macro]
#[doc(hidden)]
pub fn _gen_seq_macro(input: TokenStream) -> TokenStream {
    let SeqMacroSpec {
        mac_ident,
        prefix,
        lengths,
    } = parse_macro_input!(input as SeqMacroSpec);
    let seqs = lengths.iter().copied().map(|len| {
        (0..len)
            .map(|i| {
                if let Some(prefix) = &prefix {
                    let seq_ident = format_ident!("{}{}", prefix, i);
                    quote!(#seq_ident)
                } else {
                    let seq_lit = proc_macro2::Literal::usize_unsuffixed(i);
                    quote!(#seq_lit)
                }
            })
            .collect::<Vec<_>>()
    });
    let length_lits = lengths
        .iter()
        .map(|&i| proc_macro2::Literal::usize_unsuffixed(i));
    let ts = TokenStream::from(quote! {
        #mac_ident!(#(#length_lits => ( #(#seqs)* ))*);
    });
    ts
}
