use std::convert::TryFrom;

use quote::quote;
use syn::export::{Span, TokenStream2};
use syn::{Fields, Ident, ItemEnum, WhereClause};

use crate::attribute_helpers::contains_skip;

pub fn enum_ser(input: &ItemEnum) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let mut where_clause = where_clause.map_or_else(
        || WhereClause {
            where_token: Default::default(),
            predicates: Default::default(),
        },
        Clone::clone,
    );
    let mut body = TokenStream2::new();
    for (variant_idx, variant) in input.variants.iter().enumerate() {
        let variant_idx = u8::try_from(variant_idx).expect("up to 256 enum variants are supported");
        let variant_ident = &variant.ident;
        let mut variant_header = TokenStream2::new();
        let mut variant_body = TokenStream2::new();
        match &variant.fields {
            Fields::Named(fields) => {
                for field in &fields.named {
                    let field_name = field.ident.as_ref().unwrap();
                    if contains_skip(&field.attrs) {
                        variant_header.extend(quote! { _#field_name, });
                        continue;
                    } else {
                        let field_type = &field.ty;
                        where_clause.predicates.push(syn::parse2(quote! {
                            #field_type: borsh::ser::BorshSerialize
                        }).unwrap());
                        variant_header.extend(quote! { #field_name, });
                    }
                    variant_body.extend(quote! {
                         borsh::BorshSerialize::serialize(#field_name, writer)?;
                    })
                }
                variant_header = quote! { { #variant_header }};
            }
            Fields::Unnamed(fields) => {
                for (field_idx, field) in fields.unnamed.iter().enumerate() {
                    let field_idx =
                        u32::try_from(field_idx).expect("up to 2^32 fields are supported");
                    if contains_skip(&field.attrs) {
                        let field_ident =
                            Ident::new(format!("_id{}", field_idx).as_str(), Span::call_site());
                        variant_header.extend(quote! { #field_ident, });
                        continue;
                    } else {
                        let field_type = &field.ty;
                        where_clause.predicates.push(syn::parse2(quote! {
                            #field_type: borsh::ser::BorshSerialize
                        }).unwrap());

                        let field_ident =
                            Ident::new(format!("id{}", field_idx).as_str(), Span::call_site());
                        variant_header.extend(quote! { #field_ident, });
                        variant_body.extend(quote! {
                            borsh::BorshSerialize::serialize(#field_ident, writer)?;
                        })
                    }
                }
                variant_header = quote! { ( #variant_header )};
            }
            Fields::Unit => {}
        }
        body.extend(quote!(
            #name::#variant_ident #variant_header => {
                let variant_idx: u8 = #variant_idx;
                writer.write_all(&variant_idx.to_le_bytes())?;
                #variant_body
            }
        ))
    }
    Ok(quote! {
        impl #impl_generics borsh::ser::BorshSerialize for #name #ty_generics #where_clause {
            fn serialize<W: std::io::Write>(&self, writer: &mut W) -> std::result::Result<(), std::io::Error> {
                match self {
                    #body
                }
                Ok(())
            }
        }
    })
}
