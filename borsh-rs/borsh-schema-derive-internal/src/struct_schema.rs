use crate::helpers::{contains_skip, schema_type_name};
use quote::quote;
use syn::export::{ToTokens, TokenStream2};
use syn::{Fields, ItemStruct};

pub fn process_struct(input: &ItemStruct) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let name_str = name.to_token_stream().to_string();
    let generics = &input.generics;
    let (impl_generics, ty_generics, _) = generics.split_for_impl();
    // Generate function that returns the name of the type.
    let (schema_type_name, mut where_clause) = schema_type_name(&name_str, &input.generics);

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
                        let fields = format!(r#"["{}", "{}"]"#, #field_name, <#field_type>::schema_type_name());
                    };
                } else {
                    add_rec_type_definitions_fields.extend(quote! {
                        let fields = format!(r#"{}, ["{}", "{}"]"#, fields, #field_name, <#field_type>::schema_type_name());
                    });
                }
                add_rec_type_definitions_rec.extend(quote! {
                    <#field_type>::add_rec_type_definitions(definitions);
                });
                where_clause.extend(quote! {
                    #field_type: borsh::BorshSchema,
                });
            }
            if add_rec_type_definitions_fields.is_empty() {
                add_rec_type_definitions_fields = quote! {
                    let fields = "";
                };
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
                        let fields = format!(r#""{}""#, <#field_type>::schema_type_name());
                    };
                } else {
                    add_rec_type_definitions_fields.extend(quote! {
                        let fields = format!(r#"{}, "{}""#, fields, <#field_type>::schema_type_name());
                    });
                }
                add_rec_type_definitions_rec.extend(quote! {
                    <#field_type>::add_rec_type_definitions(definitions);
                });
                where_clause.extend(quote! {
                    #field_type: borsh::BorshSchema,
                });
            }
            if add_rec_type_definitions_fields.is_empty() {
                add_rec_type_definitions_fields = quote! {
                    let fields = "";
                };
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
        impl #impl_generics borsh::BorshSchema for #name #ty_generics #where_clause {
            fn schema_type_name() -> String {
                #schema_type_name
            }
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
            impl borsh::BorshSchema for A
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
    fn wrapper_struct() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A<T>(T);
        }).unwrap();

        let actual = process_struct(&item_struct).unwrap();
        let expected = quote!{
            impl<T> borsh::BorshSchema for A<T>
            where
                T: borsh::BorshSchema,
                T: borsh::BorshSchema,
            {
                fn schema_type_name() -> String {
                    let params = format!("{}", <T>::schema_type_name());
                    format!(r#"{}<{}>"#, "A", params)
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = format!(r#""{}""#, <T>::schema_type_name());
                    let definition = format!(r#"{{ "kind": "struct", "fields": [ {} ] }}"#, fields);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                    <T>::add_rec_type_definitions(definitions);
                }
            }
        };
        assert_eq(expected, actual);
    }

    #[test]
    fn tuple_struct() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A(u64, String);
        }).unwrap();

        let actual = process_struct(&item_struct).unwrap();
        let expected = quote!{
            impl borsh::BorshSchema for A
            where
                u64: borsh::BorshSchema,
                String: borsh::BorshSchema,
            {
                fn schema_type_name() -> String {
                    "A".to_string()
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = format!(r#""{}""#, <u64>::schema_type_name());
                    let fields = format!(
                        r#"{}, "{}""#,
                        fields,
                        <String>::schema_type_name()
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
    fn tuple_struct_params() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A<K, V>(K, V);
        }).unwrap();

        let actual = process_struct(&item_struct).unwrap();
        let expected = quote!{
            impl<K, V> borsh::BorshSchema for A<K, V>
            where
                K: borsh::BorshSchema,
                V: borsh::BorshSchema,
                K: borsh::BorshSchema,
                V: borsh::BorshSchema,
            {
                fn schema_type_name() -> String {
                    let params = format!("{}", <K>::schema_type_name());
                    let params = format!("{}, {}", params, <V>::schema_type_name());
                    format!(r#"{}<{}>"#, "A", params)
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = format!(r#""{}""#, <K>::schema_type_name());
                    let fields = format!(r#"{}, "{}""#, fields, <V>::schema_type_name());
                    let definition = format!(r#"{{ "kind": "struct", "fields": [ {} ] }}"#, fields);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                    <K>::add_rec_type_definitions(definitions);
                    <V>::add_rec_type_definitions(definitions);
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
            impl borsh::BorshSchema for A
            where
                u64: borsh::BorshSchema,
                String: borsh::BorshSchema,
            {
                fn schema_type_name() -> String {
                    "A".to_string()
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = format!(r#"["{}", "{}"]"#, "x", <u64>::schema_type_name());
                    let fields = format!(
                        r#"{}, ["{}", "{}"]"#,
                        fields,
                        "y",
                        <String>::schema_type_name()
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
            impl<K, V> borsh::BorshSchema for A<K, V>
            where
                K: borsh::BorshSchema,
                V: borsh::BorshSchema,
                HashMap<K, V>: borsh::BorshSchema,
                String: borsh::BorshSchema,
            {
                fn schema_type_name() -> String {
                    let params = format!("{}", <K>::schema_type_name());
                    let params = format!("{}, {}", params, <V>::schema_type_name());
                    format!(r#"{}<{}>"#, "A", params)
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = format!(
                        r#"["{}", "{}"]"#,
                        "x",
                        <HashMap < K, V > > ::schema_type_name()
                    );
                    let fields = format!(
                        r#"{}, ["{}", "{}"]"#,
                        fields,
                        "y",
                        <String>::schema_type_name()
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

    #[test]
    fn tuple_struct_whole_skip() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A(#[borsh_skip] String);
        }).unwrap();

        let actual = process_struct(&item_struct).unwrap();
        let expected = quote!{
            impl borsh::BorshSchema for A
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
    fn tuple_struct_partial_skip() {
        let item_struct: ItemStruct = syn::parse2(quote!{
            struct A(#[borsh_skip] u64, String);
        }).unwrap();

        let actual = process_struct(&item_struct).unwrap();
        let expected = quote!{
            impl borsh::BorshSchema for A
            where
                String: borsh::BorshSchema,
            {
                fn schema_type_name() -> String {
                    "A".to_string()
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    let fields = format!(r#""{}""#, <String>::schema_type_name());
                    let definition = format!(r#"{{ "kind": "struct", "fields": [ {} ] }}"#, fields);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                    <String>::add_rec_type_definitions(definitions);
                }
            }
        };
        assert_eq(expected, actual);
    }
}
