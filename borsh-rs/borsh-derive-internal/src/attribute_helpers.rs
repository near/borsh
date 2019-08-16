use syn::spanned::Spanned;
use syn::{Attribute, Error, Ident, Meta, NestedMeta};

pub fn contains_skip(attrs: &[Attribute]) -> bool {
    for attr in attrs.iter() {
        if let Ok(Meta::Word(ident)) = attr.parse_meta() {
            if ident.to_string().as_str() == "borsh_skip" {
                return true;
            }
        }
    }
    false
}

pub fn contains_initialize_with(attrs: &[Attribute]) -> syn::Result<Option<Ident>> {
    for attr in attrs.iter() {
        if let Ok(Meta::List(meta_list)) = attr.parse_meta() {
            if meta_list.ident.to_string().as_str() == "borsh_init" {
                if meta_list.nested.len() != 1 {
                    return Err(Error::new(
                        meta_list.span(),
                        "borsh_init requires exactly one initialization method.",
                    ));
                }
                let nested_meta = meta_list.nested.iter().next().unwrap();
                if let NestedMeta::Meta(Meta::Word(ident)) = nested_meta {
                    return Ok(Some(ident.clone()));
                }
            }
        }
    }
    Ok(None)
}
