use crate::attribute_helpers::{contains_initialize_with, contains_skip};
use quote::quote;
use syn::export::TokenStream2;
use syn::{Fields, ItemStruct};

pub fn struct_de(input: &ItemStruct) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let generics = &input.generics;
    let init_method = contains_initialize_with(&input.attrs)?;
    let mut deserializable_field_types = TokenStream2::new();
    let return_value = match &input.fields {
        Fields::Named(fields) => {
            let mut body = TokenStream2::new();
            for field in &fields.named {
                let field_name = field.ident.as_ref().unwrap();
                let delta = if contains_skip(&field.attrs) {
                    quote! {
                        #field_name: Default::default(),
                    }
                } else {
                    let field_type = &field.ty;
                    deserializable_field_types.extend(quote! {
                        #field_type: borsh::BorshDeserialize,
                    });

                    quote! {
                        #field_name: borsh::BorshDeserialize::deserialize(buf)?,
                    }
                };
                body.extend(delta);
            }
            quote! {
                Self { #body }
            }
        }
        Fields::Unnamed(fields) => {
            let mut body = TokenStream2::new();
            for _ in 0..fields.unnamed.len() {
                let delta = quote! {
                    borsh::BorshDeserialize::deserialize(buf)?,
                };
                body.extend(delta);
            }
            quote! {
                Self( #body )
            }
        }
        Fields::Unit => {
            quote! {
                Self {}
            }
        }
    };
    if let Some(method_ident) = init_method {
        Ok(quote! {
            impl #generics borsh::de::BorshDeserialize for #name #generics where #deserializable_field_types {
                fn deserialize(buf: &mut &[u8]) ->  std::result::Result<Self, std::io::Error> {
                    let mut return_value = #return_value;
                    return_value.#method_ident();
                    Ok(return_value)
                }
            }
        })
    } else {
        Ok(quote! {
            impl #generics borsh::de::BorshDeserialize for #name #generics where #deserializable_field_types {
                fn deserialize(buf: &mut &[u8]) -> std::result::Result<Self, std::io::Error> {
                    Ok(#return_value)
                }
            }
        })
    }
}
