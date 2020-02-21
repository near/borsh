//use borsh_schema_derive as borsh_schema;
//mod schema;
//use crate::schema::BorshSchema;
//use std::collections::hash_map::RandomState;
//use std::collections::HashMap;
//
//struct Tomatoes;
//impl BorshSchema for Tomatoes {
//    fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//        unimplemented!()
//    }
//
//    fn schema_type_name() -> String {
//        unimplemented!()
//    }
//}
//struct Cucumber;
//impl BorshSchema for Cucumber {
//    fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//        unimplemented!()
//    }
//
//    fn schema_type_name() -> String {
//        unimplemented!()
//    }
//}
//struct Oil;
//impl BorshSchema for Oil {
//    fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//        unimplemented!()
//    }
//
//    fn schema_type_name() -> String {
//        unimplemented!()
//    }
//}
//struct Wrapper;
//impl BorshSchema for Wrapper {
//    fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//        unimplemented!()
//    }
//
//    fn schema_type_name() -> String {
//        unimplemented!()
//    }
//}
//struct Filling;
//impl BorshSchema for Filling {
//    fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//        unimplemented!()
//    }
//
//    fn schema_type_name() -> String {
//        unimplemented!()
//    }
//}
//
//enum A<C, W> {
//    Bacon,
//    Eggs,
//    Salad(Tomatoes, C, Oil),
//    Sausage { wrapper: W, filling: Filling },
//}
//
//impl<C, W> BorshSchema for A<C, W>
//where
//    C: BorshSchema,
//    W: BorshSchema,
//{
//    fn schema_type_name() -> String {
//        let params = format!("{}", <C>::schema_type_name());
//        let params = format!("{}, {}", params, <W>::schema_type_name());
//        format!(r#"{}<{}>"#, "A", params)
//    }
//    fn add_rec_type_definitions(definitions: &mut ::std::collections::HashMap<String, String>) {
//        struct ABacon<C, W>(::std::marker::PhantomData<(C, W)>);
//        impl<C, W> BorshSchema for ABacon<C, W> {
//            fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//                unimplemented!()
//            }
//
//            fn schema_type_name() -> String {
//                unimplemented!()
//            }
//        }
//        struct AEggs<C, W>(::std::marker::PhantomData<(C, W)>);
//        impl<C, W> BorshSchema for AEggs<C, W> {
//            fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//                unimplemented!()
//            }
//
//            fn schema_type_name() -> String {
//                unimplemented!()
//            }
//        }
//        struct ASalad<C, W>(Tomatoes, C, Oil, ::std::marker::PhantomData<(C, W)>);
//        impl<C, W> BorshSchema for ASalad<C, W> {
//            fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//                unimplemented!()
//            }
//
//            fn schema_type_name() -> String {
//                unimplemented!()
//            }
//        }
//        struct ASausage<C, W> {
//            wrapper: W,
//            filling: Filling,
//            borsh_schema_phantom_data: ::std::marker::PhantomData<(C, W)>,
//        }
//        impl<C, W> BorshSchema for ASausage<C, W> {
//            fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
//                unimplemented!()
//            }
//
//            fn schema_type_name() -> String {
//                unimplemented!()
//            }
//        }
//        <ABacon<C, W>>::add_rec_type_definitions(definitions);
//        <AEggs<C, W>>::add_rec_type_definitions(definitions);
//        <ASalad<C, W>>::add_rec_type_definitions(definitions);
//        <ASausage<C, W>>::add_rec_type_definitions(definitions);
//        let variants = format!(
//            r#"["{}", "{}"]"#,
//            "Bacon",
//            <ABacon<C, W>>::schema_type_name()
//        );
//        let variants = format!(
//            r#"{}, ["{}", "{}"]"#,
//            variants,
//            "Eggs",
//            <AEggs<C, W>>::schema_type_name()
//        );
//        let variants = format!(
//            r#"{}, ["{}", "{}"]"#,
//            variants,
//            "Salad",
//            <ASalad<C, W>>::schema_type_name()
//        );
//        let variants = format!(
//            r#"{}, ["{}", "{}"]"#,
//            variants,
//            "Sausage",
//            <ASausage<C, W>>::schema_type_name()
//        );
//        let definition = format!(r#"{{ "kind": "enum", "variants": [ {} ] }}"#, variants);
//        Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
//    }
//}

pub mod schema;
pub use borsh_schema_derive::BorshSchema;
pub use schema::BorshSchema;
