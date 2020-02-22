use crate::helpers::schema_type_name;
use quote::quote;
use syn::export::{Span, ToTokens, TokenStream2};
use syn::{
    parse_quote, AttrStyle, Attribute, Field, Fields, FieldsUnnamed, Ident, ItemEnum, ItemStruct,
    Visibility,
};

pub fn process_enum(input: &ItemEnum) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let name_str = name.to_token_stream().to_string();
    let generics = &input.generics;
    let (impl_generics, ty_generics, _) = generics.split_for_impl();
    // Generate function that returns the name of the type.
    let (schema_type_name, mut where_clause) = schema_type_name(&name_str, &input.generics);

    // Generate function that returns the schema for variants.
    // Definitions of the variants.
    let mut variants_defs = TokenStream2::new();
    // Definitions of the anonymous structs used in variants.
    let mut anonymous_defs = TokenStream2::new();
    // Recursive calls to `add_rec_type_definitions`.
    let mut add_recursive_defs = TokenStream2::new();
    for variant in &input.variants {
        let variant_name_str = variant.ident.to_token_stream().to_string();
        let full_variant_name_str = format!("{}{}", name_str, variant_name_str);
        let full_variant_ident = Ident::new(full_variant_name_str.as_str(), Span::call_site());
        let mut anonymous_struct = ItemStruct {
            attrs: vec![],
            vis: Visibility::Inherited,
            struct_token: Default::default(),
            ident: full_variant_ident.clone(),
            generics: (*generics).clone(),
            fields: variant.fields.clone(),
            semi_token: Some(Default::default()),
        };
        let generic_params = generics
            .type_params()
            .fold(TokenStream2::new(), |acc, generic| {
                let ident = &generic.ident;
                quote! {
                    #acc
                    #ident ,
                }
            });
        if !generic_params.is_empty() {
            let attr = Attribute {
                pound_token: Default::default(),
                style: AttrStyle::Outer,
                bracket_token: Default::default(),
                path: parse_quote! {borsh_skip},
                tokens: Default::default(),
            };
            // Whether we should convert the struct from unit struct to regular struct.
            let mut unit_to_regular = false;
            match &mut anonymous_struct.fields {
                Fields::Named(named) => {
                    named.named.push(Field {
                        attrs: vec![attr.clone()],
                        vis: Visibility::Inherited,
                        ident: Some(Ident::new("borsh_schema_phantom_data", Span::call_site())),
                        colon_token: None,
                        ty: parse_quote! {::std::marker::PhantomData<(#generic_params)>},
                    });
                }
                Fields::Unnamed(unnamed) => {
                    unnamed.unnamed.push(Field {
                        attrs: vec![attr.clone()],
                        vis: Visibility::Inherited,
                        ident: None,
                        colon_token: None,
                        ty: parse_quote! {::std::marker::PhantomData<(#generic_params)>},
                    });
                }
                Fields::Unit => {
                    unit_to_regular = true;
                }
            }
            if unit_to_regular {
                let mut fields = FieldsUnnamed {
                    paren_token: Default::default(),
                    unnamed: Default::default(),
                };
                fields.unnamed.push(Field {
                    attrs: vec![attr],
                    vis: Visibility::Inherited,
                    ident: None,
                    colon_token: None,
                    ty: parse_quote! {::std::marker::PhantomData<(#generic_params)>},
                });
                anonymous_struct.fields = Fields::Unnamed(fields);
            }
        }
        anonymous_defs.extend(quote! {
            #[derive(borsh::BorshSchema)]
            #anonymous_struct
        });
        add_recursive_defs.extend(quote! {
            <#full_variant_ident #ty_generics>::add_rec_type_definitions(definitions);
        });
        if variants_defs.is_empty() {
            variants_defs = quote! {
                let variants = format!(r#"["{}", "{}"]"#, #variant_name_str , <#full_variant_ident #ty_generics>::schema_type_name());
            };
        } else {
            variants_defs.extend(quote! {
                let variants = format!(r#"{}, ["{}", "{}"]"#, variants, #variant_name_str, <#full_variant_ident #ty_generics>::schema_type_name());
            });
        }
    }

    let type_definitions = quote! {
        fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
            #anonymous_defs
            #add_recursive_defs
            #variants_defs
            let definition = format!(r#"{{ "kind": "enum", "variants": [ {} ] }}"#, variants);
            Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
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
            #type_definitions
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
    fn simple_enum() {
        let item_enum: ItemEnum = syn::parse2(quote!{
            enum A {
                Bacon,
                Eggs
            }
        }).unwrap();

        let actual = process_enum(&item_enum).unwrap();
        let expected = quote!{
            impl borsh::BorshSchema for A {
                fn schema_type_name() -> String {
                    "A".to_string()
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    #[derive(borsh :: BorshSchema)]
                    struct ABacon;
                    #[derive(borsh :: BorshSchema)]
                    struct AEggs;
                    <ABacon>::add_rec_type_definitions(definitions);
                    <AEggs>::add_rec_type_definitions(definitions);
                    let variants = format!(r#"["{}", "{}"]"#, "Bacon", <ABacon>::schema_type_name());
                    let variants = format!(
                        r#"{}, ["{}", "{}"]"#,
                        variants,
                        "Eggs",
                        <AEggs>::schema_type_name()
                    );
                    let definition = format!(r#"{{ "kind": "enum", "variants": [ {} ] }}"#, variants);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                }
            }
        };
        assert_eq(expected, actual);
    }

    #[test]
    fn single_field_enum() {
        let item_enum: ItemEnum = syn::parse2(quote! {
            enum A {
                Bacon,
            }
        }).unwrap();

        let actual = process_enum(&item_enum).unwrap();
        let expected = quote!{
            impl borsh::BorshSchema for A {
                fn schema_type_name() -> String {
                    "A".to_string()
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    #[derive(borsh :: BorshSchema)]
                    struct ABacon;
                    <ABacon>::add_rec_type_definitions(definitions);
                    let variants = format!(r#"["{}", "{}"]"#, "Bacon", <ABacon>::schema_type_name());
                    let definition = format!(r#"{{ "kind": "enum", "variants": [ {} ] }}"#, variants);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                }
            }
        };
        assert_eq(expected, actual);
    }

    #[test]
    fn complex_enum() {
        let item_enum: ItemEnum = syn::parse2(quote! {
            enum A {
                Bacon,
                Eggs,
                Salad(Tomatoes, Cucumber, Oil),
                Sausage{wrapper: Wrapper, filling: Filling},
            }
        }).unwrap();

        let actual = process_enum(&item_enum).unwrap();
        let expected = quote!{
            impl borsh::BorshSchema for A {
                fn schema_type_name() -> String {
                    "A".to_string()
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    #[derive(borsh :: BorshSchema)]
                    struct ABacon;
                    #[derive(borsh :: BorshSchema)]
                    struct AEggs;
                    #[derive(borsh :: BorshSchema)]
                    struct ASalad(Tomatoes, Cucumber, Oil);
                    #[derive(borsh :: BorshSchema)]
                    struct ASausage {
                        wrapper: Wrapper,
                        filling: Filling
                    }
                    <ABacon>::add_rec_type_definitions(definitions);
                    <AEggs>::add_rec_type_definitions(definitions);
                    <ASalad>::add_rec_type_definitions(definitions);
                    <ASausage>::add_rec_type_definitions(definitions);
                    let variants = format!(r#"["{}", "{}"]"#, "Bacon", <ABacon>::schema_type_name());
                    let variants = format!(
                        r#"{}, ["{}", "{}"]"#,
                        variants,
                        "Eggs",
                        <AEggs>::schema_type_name()
                    );
                    let variants = format!(
                        r#"{}, ["{}", "{}"]"#,
                        variants,
                        "Salad",
                        <ASalad>::schema_type_name()
                    );
                    let variants = format!(
                        r#"{}, ["{}", "{}"]"#,
                        variants,
                        "Sausage",
                        <ASausage>::schema_type_name()
                    );
                    let definition = format!(r#"{{ "kind": "enum", "variants": [ {} ] }}"#, variants);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                }
            }
        };
        assert_eq(expected, actual);
    }

    #[test]
    fn complex_enum_generics() {
        let item_enum: ItemEnum = syn::parse2(quote! {
            enum A<C, W> {
                Bacon,
                Eggs,
                Salad(Tomatoes, C, Oil),
                Sausage{wrapper: W, filling: Filling},
            }
        }).unwrap();

        let actual = process_enum(&item_enum).unwrap();
        let expected = quote!{
            impl<C, W> borsh::BorshSchema for A<C, W>
            where
                C: borsh::BorshSchema,
                W: borsh::BorshSchema,
            {
                fn schema_type_name() -> String {
                    let params = format!("{}", <C>::schema_type_name());
                    let params = format!("{}, {}", params, <W>::schema_type_name());
                    format!(r#"{}<{}>"#, "A", params)
                }
                fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
                    #[derive(borsh :: BorshSchema)]
                    struct ABacon<C, W>( #[borsh_skip] ::std::marker::PhantomData<(C, W)>);
                    #[derive(borsh :: BorshSchema)]
                    struct AEggs<C, W>( #[borsh_skip] ::std::marker::PhantomData<(C, W)>);
                    #[derive(borsh :: BorshSchema)]
                    struct ASalad<C, W>(Tomatoes, C, Oil, #[borsh_skip] ::std::marker::PhantomData<(C, W)>);
                    #[derive(borsh :: BorshSchema)]
                    struct ASausage<C, W> {
                        wrapper: W,
                        filling: Filling,
                        #[borsh_skip]
                        borsh_schema_phantom_data: ::std::marker::PhantomData<(C, W)>
                    }
                    <ABacon<C, W> >::add_rec_type_definitions(definitions);
                    <AEggs<C, W> >::add_rec_type_definitions(definitions);
                    <ASalad<C, W> >::add_rec_type_definitions(definitions);
                    <ASausage<C, W> >::add_rec_type_definitions(definitions);
                    let variants = format!(
                        r#"["{}", "{}"]"#,
                        "Bacon",
                        <ABacon<C, W> >::schema_type_name()
                    );
                    let variants = format!(
                        r#"{}, ["{}", "{}"]"#,
                        variants,
                        "Eggs",
                        <AEggs<C, W> >::schema_type_name()
                    );
                    let variants = format!(
                        r#"{}, ["{}", "{}"]"#,
                        variants,
                        "Salad",
                        <ASalad<C, W> >::schema_type_name()
                    );
                    let variants = format!(
                        r#"{}, ["{}", "{}"]"#,
                        variants,
                        "Sausage",
                        <ASausage<C, W> >::schema_type_name()
                    );
                    let definition = format!(r#"{{ "kind": "enum", "variants": [ {} ] }}"#, variants);
                    Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
                }
            }
        };
        assert_eq(expected, actual);
    }
}
