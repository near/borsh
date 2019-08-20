use crate::attribute_helpers::contains_skip;
use quote::quote;
use syn::export::{Span, TokenStream2};
use syn::{Fields, Ident, ItemEnum};

pub fn enum_ser(input: &ItemEnum) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let mut body = TokenStream2::new();
    for (variant_idx, variant) in input.variants.iter().enumerate() {
        let variant_idx = variant_idx as u8;
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
                    let field_idx = field_idx as u32;
                    if contains_skip(&field.attrs) {
                        let field_ident =
                            Ident::new(format!("_id{}", field_idx).as_str(), Span::call_site());
                        variant_header.extend(quote! { #field_ident, });
                        continue;
                    } else {
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
                writer.write(&variant_idx.to_le_bytes())?;
                #variant_body
            }
        ))
    }
    Ok(quote! {
        impl borsh::ser::BorshSerialize for #name {
            fn serialize<W: std::io::Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
                match self {
                    #body
                }
                Ok(())
            }
        }
    })
}
