mod attribute_helpers;

use crate::attribute_helpers::{contains_initialize_with, contains_skip};
use proc_macro2::Span;
use quote::quote;
use syn::export::TokenStream2;
use syn::{Fields, Ident, Index, ItemEnum, ItemStruct, ItemUnion};

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
                    borsh::Serializable::write(&self.#field_name, writer)?;
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
                    borsh::Serializable::write(&self.#field_idx, writer)?;
                };
                body.extend(delta);
            }
        }
        Fields::Unit => {}
    }
    Ok(quote! {
        impl borsh::ser::Serializable for #name {
            fn write<W: std::io::Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
                #body
                Ok(())
            }
        }
    })
}

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
                         borsh::Serializable::write(#field_name, writer)?;
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
                            borsh::Serializable::write(#field_ident, writer)?;
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
        impl borsh::ser::Serializable for #name {
            fn write<W: std::io::Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
                match self {
                    #body
                }
                Ok(())
            }
        }
    })
}

pub fn union_ser(_input: &ItemUnion) -> syn::Result<TokenStream2> {
    unimplemented!()
}

pub fn struct_de(input: &ItemStruct) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let init_method = contains_initialize_with(&input.attrs)?;
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
                    quote! {
                        #field_name: borsh::Deserializable::read(reader)?,
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
                    borsh::Deserializable::read(reader)?,
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
            impl borsh::de::Deserializable for #name {
                fn read<R: std::io::Read>(reader: &mut R) -> Result<Self, std::io::Error> {
                    let mut return_value = #return_value;
                    return_value.#method_ident();
                    Ok(return_value)
                }
            }
        })
    } else {
        Ok(quote! {
            impl borsh::de::Deserializable for #name {
                fn read<R: std::io::Read>(reader: &mut R) -> Result<Self, std::io::Error> {
                    Ok(#return_value)
                }
            }
        })
    }
}

pub fn enum_de(input: &ItemEnum) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let init_method = contains_initialize_with(&input.attrs)?;
    let mut variant_arms = TokenStream2::new();
    for (variant_idx, variant) in input.variants.iter().enumerate() {
        let variant_idx = variant_idx as u8;
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
                        variant_header.extend(quote! {
                            #field_name: borsh::Deserializable::read(reader)?,
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
                        variant_header.extend(quote! { borsh::Deserializable::read(reader)?, });
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
        let mut variant_idx = [0u8; std::mem::size_of::<u8>()];
        reader.read(&mut variant_idx)?;
        let variant_idx = u8::from_le_bytes(variant_idx);
    };
    if let Some(method_ident) = init_method {
        Ok(quote! {
            impl borsh::de::Deserializable for #name {
                fn read<R: std::io::Read>(reader: &mut R) -> Result<Self, std::io::Error> {
                    #variant_idx
                    let mut return_value = match variant_idx {
                        #variant_arms
                        _ => panic!(format!("Unexpeted variant index: {:?}", variant_idx)),
                    };
                    return_value.#method_ident();
                    Ok(return_value)
                }
            }
        })
    } else {
        Ok(quote! {
            impl borsh::de::Deserializable for #name {
                fn read<R: std::io::Read>(reader: &mut R) -> Result<Self, std::io::Error> {
                    #variant_idx
                    let return_value = match variant_idx {
                        #variant_arms
                        _ => panic!(format!("Unexpeted variant index: {:?}", variant_idx)),
                    };
                    Ok(return_value)
                }
            }
        })
    }
}

pub fn union_de(_input: &ItemUnion) -> syn::Result<TokenStream2> {
    unimplemented!()
}
