use core::convert::TryFrom;

use quote::quote;
use syn::export::TokenStream2;
use syn::{Fields, Ident, ItemEnum, WhereClause};

use crate::attribute_helpers::{contains_initialize_with, contains_skip};

pub fn enum_de(input: &ItemEnum, cratename: Ident) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let mut where_clause = where_clause.map_or_else(
        || WhereClause {
            where_token: Default::default(),
            predicates: Default::default(),
        },
        Clone::clone,
    );
    let init_method = contains_initialize_with(&input.attrs)?;
    let mut variant_arms = TokenStream2::new();
    for (variant_idx, variant) in input.variants.iter().enumerate() {
        let variant_idx = u8::try_from(variant_idx).expect("up to 256 enum variants are supported");
        let variant_ident = &variant.ident;
        let mut variant_header = TokenStream2::new();
        match &variant.fields {
            Fields::Named(fields) => {
                for field in &fields.named {
                    let field_name = field.ident.as_ref().unwrap();
                    if contains_skip(&field.attrs) {
                        variant_header.extend(quote! {
                            #field_name: Default::default(),
                        });
                    } else {
                        let field_type = &field.ty;
                        where_clause.predicates.push(syn::parse2(quote! {
                            #field_type: #cratename::BorshDeserialize
                        }).unwrap());

                        variant_header.extend(quote! {
                            #field_name: #cratename::BorshDeserialize::deserialize(buf)?,
                        });
                    }
                }
                variant_header = quote! { { #variant_header }};
            }
            Fields::Unnamed(fields) => {
                for field in fields.unnamed.iter() {
                    if contains_skip(&field.attrs) {
                        variant_header.extend(quote! { Default::default(), });
                    } else {
                        let field_type = &field.ty;
                        where_clause.predicates.push(syn::parse2(quote! {
                            #field_type: #cratename::BorshDeserialize
                        }).unwrap());

                        variant_header
                            .extend(quote! { #cratename::BorshDeserialize::deserialize(buf)?, });
                    }
                }
                variant_header = quote! { ( #variant_header )};
            }
            Fields::Unit => {}
        }
        variant_arms.extend(quote! {
            #variant_idx => #name::#variant_ident #variant_header ,
        });
    }
    let variant_idx = quote! {
        let variant_idx: u8 = #cratename::BorshDeserialize::deserialize(buf)?;
    };
    if let Some(method_ident) = init_method {
        Ok(quote! {
            impl #impl_generics #cratename::de::BorshDeserialize for #name #ty_generics #where_clause {
                fn deserialize(buf: &mut &[u8]) -> core::result::Result<Self, #cratename::maybestd::io::Error> {
                    #variant_idx
                    let mut return_value = match variant_idx {
                        #variant_arms
                        _ => {
                            let msg = #cratename::maybestd::format!("Unexpected variant index: {:?}", variant_idx);

                            return Err(#cratename::maybestd::io::Error::new(
                                #cratename::maybestd::io::ErrorKind::InvalidInput,
                                msg,
                            ));
                        }
                    };
                    return_value.#method_ident();
                    Ok(return_value)
                }
            }
        })
    } else {
        Ok(quote! {
            impl #impl_generics #cratename::de::BorshDeserialize for #name #ty_generics #where_clause {
                fn deserialize(buf: &mut &[u8]) -> core::result::Result<Self, #cratename::maybestd::io::Error> {
                    #variant_idx
                    let return_value = match variant_idx {
                        #variant_arms
                        _ => {
                            let msg = #cratename::maybestd::format!("Unexpected variant index: {:?}", variant_idx);

                            return Err(#cratename::maybestd::io::Error::new(
                                #cratename::maybestd::io::ErrorKind::InvalidInput,
                                msg,
                            ));
                        }
                    };
                    Ok(return_value)
                }
            }
        })
    }
}
