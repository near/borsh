use crate::attribute_helpers::contains_skip;
use quote::quote;
use syn::export::{Span, TokenStream2};
use syn::{Fields, Index, ItemStruct};

pub fn struct_ser(input: &ItemStruct) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let mut body = TokenStream2::new();
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
            }
        }
        Fields::Unnamed(fields) => {
            for field_idx in 0..fields.unnamed.len() {
                let field_idx = Index {
                    index: field_idx as u32,
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

    let generics = crate::util::add_ser_constraints(input.generics.clone());
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        impl #impl_generics borsh::ser::BorshSerialize for #name #ty_generics #where_clause {
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
            impl borsh::ser::BorshSerialize for A {
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
            impl<K: borsh::ser::BorshSerialize, V: borsh::ser::BorshSerialize> borsh::ser::BorshSerialize for A<K, V> {
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
