use quote::{quote, ToTokens};
use syn::export::TokenStream2;
use syn::{Attribute, Generics, Meta};

pub fn contains_skip(attrs: &[Attribute]) -> bool {
    for attr in attrs.iter() {
        if let Ok(Meta::Path(path)) = attr.parse_meta() {
            if path.to_token_stream().to_string().as_str() == "borsh_skip" {
                return true;
            }
        }
    }
    false
}

pub fn schema_type_name(ident_str: &String, generics: &Generics) -> (TokenStream2, TokenStream2) {
    let (_, _, where_clause_generics) = generics.split_for_impl();
    // Generate function that returns the name of the type.
    let mut schema_type_name_params = TokenStream2::new();
    let mut where_clause = TokenStream2::new();
    if let Some(where_clause_generics) = where_clause_generics {
        let where_clause_generics = &where_clause_generics.predicates;
        where_clause = quote! {#where_clause_generics};
    }
    for type_param in generics.type_params() {
        let type_param_name = &type_param.ident;
        if schema_type_name_params.is_empty() {
            schema_type_name_params = quote! {
                let params = format!("{}", <#type_param_name>::schema_type_name());
            };
        } else {
            schema_type_name_params.extend(quote! {
                let params = format!("{}, {}", params, <#type_param_name>::schema_type_name());
            });
        }
        where_clause.extend(quote! {
            #type_param_name: borsh::BorshSchema,
        });
    }
    let result = if schema_type_name_params.is_empty() {
        quote! {
                #ident_str.to_string()
        }
    } else {
        quote! {
                #schema_type_name_params
                format!(r#"{}<{}>"#, #ident_str, params)
        }
    };
    (result, where_clause)
}
