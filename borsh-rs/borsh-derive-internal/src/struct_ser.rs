use std::convert::TryFrom;

use quote::quote;
use syn::export::{Span, TokenStream2};
use syn::{Fields, Index, ItemStruct};

use crate::attribute_helpers::contains_skip;

pub fn struct_ser(input: &ItemStruct) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let generics = &input.generics;
    let mut body = TokenStream2::new();
    let mut serializable_field_types = TokenStream2::new();
    match &input.fields {
        Fields::Named(fields) => {
            for field in &fields.named {
                if contains_skip(&field.attrs) {
                    continue;
                }
                let field_name = field.ident.as_ref().unwrap();
                let delta = quote! {
                    borsh::BorshSerialize::serialize(&self.#field_name, writer)?;
                };
                body.extend(delta);

                let field_type = &field.ty;
                serializable_field_types.extend(quote! {
                    #field_type: borsh::ser::BorshSerialize,
                });
            }
        }
        Fields::Unnamed(fields) => {
            for field_idx in 0..fields.unnamed.len() {
                let field_idx = Index {
                    index: u32::try_from(field_idx).expect("up to 2^32 fields are supported"),
                    span: Span::call_site(),
                };
                let delta = quote! {
                    borsh::BorshSerialize::serialize(&self.#field_idx, writer)?;
                };
                body.extend(delta);
            }
        }
        Fields::Unit => {}
    }
    Ok(quote! {
        impl #generics borsh::ser::BorshSerialize for #name #generics where #serializable_field_types {
            fn serialize<W: std::io::Write>(&self, writer: &mut W) -> std::result::Result<(), std::io::Error> {
                #body
                Ok(())
            }
        }
    })
}

// Rustfmt removes comas.
#[rustfmt::skip]
#[cfg(test)]
mod tests {
    use super::*;

    fn assert_eq(expected: TokenStream2, actual: TokenStream2) {
        assert_eq!(expected.to_string(), actual.to_string())
    }

    #[test]
    fn simple_struct() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A {
                x: u64,
                y: String,
            }
        }).unwrap();

        let actual = struct_ser(&item_struct).unwrap();
        let expected = quote!{
            impl borsh::ser::BorshSerialize for A
            where
                u64: borsh::ser::BorshSerialize,
                String: borsh::ser::BorshSerialize,
            {
                fn serialize<W: std::io::Write>(&self, writer: &mut W) -> std::result::Result<(), std::io::Error> {
                    borsh::BorshSerialize::serialize(&self.x, writer)?;
                    borsh::BorshSerialize::serialize(&self.y, writer)?;
                    Ok(())
                }
            }
        };
        assert_eq(expected, actual);
    }

    #[test]
    fn simple_generics() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A<K, V> {
                x: HashMap<K, V>,
                y: String,
            }
        }).unwrap();

        let actual = struct_ser(&item_struct).unwrap();
        let expected = quote!{
            impl<K, V> borsh::ser::BorshSerialize for A<K, V>
            where
                HashMap<K, V>: borsh::ser::BorshSerialize,
                String: borsh::ser::BorshSerialize,
            {
                fn serialize<W: std::io::Write>(&self, writer: &mut W) -> std::result::Result<(), std::io::Error> {
                    borsh::BorshSerialize::serialize(&self.x, writer)?;
                    borsh::BorshSerialize::serialize(&self.y, writer)?;
                    Ok(())
                }
            }
        };
        assert_eq(expected, actual);
    }
}
