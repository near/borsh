use crate::attribute_helpers::contains_skip;
use quote::quote;
use syn::export::{ToTokens, TokenStream2};
use syn::{Fields, ItemStruct};

pub fn process_struct(input: &ItemStruct) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let name_str = name.to_token_stream().to_string();
    let generics = &input.generics;
    let (impl_generics, ty_generics, where_clause_generics) = generics.split_for_impl();
    // Generate function that returns the name of the type.
    let mut schema_type_name_params = TokenStream2::new();
    let mut where_clause = TokenStream2::new();
    if let Some(where_clause_generics) = where_clause_generics {
        let where_clause_generics = &where_clause_generics.predicates;
        where_clause = quote! {#where_clause_generics};
    }
    for type_param in input.generics.type_params() {
        let type_param_name = &type_param.ident;
        if schema_type_name_params.is_empty() {
            schema_type_name_params = quote! {
                let params = format!("{}", #type_param_name::schema_type_name());
            };
        } else {
            schema_type_name_params.extend(quote! {
                let params = format!("{}, {}", params, #type_param_name::schema_type_name());
            });
        }
        where_clause.extend(quote! {
            #type_param_name: borsh_schema::BorshSchema,
        });
    }
    let schema_type_name = if schema_type_name_params.is_empty() {
        quote! {
            fn schema_type_name() -> String {
                #name_str.to_string()
            }
        }
    } else {
        quote! {
            fn schema_type_name() -> String {
                #schema_type_name_params
                format!(r#"{}<{}>"#, #name_str, params)
            }
        }
    };

    // Generate function that returns the schema of required types.
    let mut add_rec_type_definitions_fields = TokenStream2::new();
    let mut add_rec_type_definitions_rec = TokenStream2::new();
    match &input.fields {
        Fields::Named(fields) => {
            for field in &fields.named {
                if contains_skip(&field.attrs) {
                    continue;
                }
                let field_name = field.ident.as_ref().unwrap().to_token_stream().to_string();
                let field_type = &field.ty;
                if add_rec_type_definitions_fields.is_empty() {
                    add_rec_type_definitions_fields = quote! {
                        let fields = format!(r#"["{}", "{}"]"#, #field_name, #field_type::schema_type_name());
                    };
                } else {
                    add_rec_type_definitions_fields.extend(quote! {
                        let fields = format!(r#"{}, ["{}", "{}"]"#, fields, #field_name, #field_type::schema_type_name());
                    });
                }
                add_rec_type_definitions_rec.extend(quote! {
                    <#field_type>::add_rec_type_definitions(definitions);
                });
                where_clause.extend(quote! {
                    #field_type: borsh_schema::BorshSchema,
                });
            }
        }
        Fields::Unnamed(fields) => {
            for field in &fields.unnamed {
                if contains_skip(&field.attrs) {
                    continue;
                }
                let field_type = &field.ty;
                if add_rec_type_definitions_fields.is_empty() {
                    add_rec_type_definitions_fields = quote! {
                        let fields = format!(r#""{}""#, #field_type::schema_type_name());
                    };
                } else {
                    add_rec_type_definitions_fields.extend(quote! {
                        let fields = format!(r#"{}, "{}""#, fields, #field_type::schema_type_name());
                    });
                }
                add_rec_type_definitions_rec.extend(quote! {
                    <#field_type>::add_rec_type_definitions(definitions);
                });
                where_clause.extend(quote! {
                    #field_type: borsh_schema::BorshSchema,
                });
            }
        }
        Fields::Unit => {
            add_rec_type_definitions_fields = quote! {
                let fields = "";
            };
        }
    }

    let add_rec_type_definitions = quote! {
        fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
            #add_rec_type_definitions_fields
            let definition = format!(r#"{{ "kind": "struct", "fields": [ {} ] }}"#, fields);
            Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
            #add_rec_type_definitions_rec
        }
    };
    if !where_clause.is_empty() {
        where_clause = quote! { where #where_clause};
    }
    Ok(quote! {
        impl #impl_generics borsh_schema::BorshSchema for #name #ty_generics #where_clause {
            #schema_type_name
            #add_rec_type_definitions
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
    fn unit_struct() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A;
        }).unwrap();

        let actual = process_struct(&item_struct).unwrap();
        let expected = quote!{
            impl borsh_schema::BorshSchema for A
            {
                fn schema_type_name() -> String {
                    "A".to_string()
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = "";
                    let definition = format!(r#"{{ "kind": "struct", "fields": [ {} ] }}"#, fields);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                }
            }
        };
        assert_eq(expected, actual);
    }

    #[test]
    fn simple_struct() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A {
                x: u64,
                y: String,
            }
        }).unwrap();

        let actual = process_struct(&item_struct).unwrap();
        let expected = quote!{
            impl borsh_schema::BorshSchema for A
            where
                u64: borsh_schema::BorshSchema,
                String: borsh_schema::BorshSchema,
            {
                fn schema_type_name() -> String {
                    "A".to_string()
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = format!(r#"["{}", "{}"]"#, "x", u64::schema_type_name());
                    let fields = format!(
                        r#"{}, ["{}", "{}"]"#,
                        fields,
                        "y",
                        String::schema_type_name()
                    );
                    let definition = format!(r#"{{ "kind": "struct", "fields": [ {} ] }}"#, fields);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                    <u64>::add_rec_type_definitions(definitions);
                    <String>::add_rec_type_definitions(definitions);
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

        let actual = process_struct(&item_struct).unwrap();
        let expected = quote!{
            impl<K, V> borsh_schema::BorshSchema for A<K, V>
            where
                K: borsh_schema::BorshSchema,
                V: borsh_schema::BorshSchema,
                HashMap<K, V>: borsh_schema::BorshSchema,
                String: borsh_schema::BorshSchema,
            {
                fn schema_type_name() -> String {
                    let params = format!("{}", K::schema_type_name());
                    let params = format!("{}, {}", params, V::schema_type_name());
                    format!(r#"{}<{}>"#, "A", params)
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = format!(
                        r#"["{}", "{}"]"#,
                        "x",
                        HashMap < K,
                        V > ::schema_type_name()
                    );
                    let fields = format!(
                        r#"{}, ["{}", "{}"]"#,
                        fields,
                        "y",
                        String::schema_type_name()
                    );
                    let definition = format!(r#"{{ "kind": "struct", "fields": [ {} ] }}"#, fields);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                    <HashMap<K, V> >::add_rec_type_definitions(definitions);
                    <String>::add_rec_type_definitions(definitions);
                }
            }
        };
        assert_eq(expected, actual);
    }
}
