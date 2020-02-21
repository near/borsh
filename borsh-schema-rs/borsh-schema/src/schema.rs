use std::collections::hash_map::{Entry, RandomState};
use std::collections::*;

/// A string description of the type.
pub trait BorshSchema {
    /// Recursively, using DFS, add type definitions required for this type. For primitive types
    /// this is an empty map. Type definition explains how to serialize/deserialize a type.
    fn add_rec_type_definitions(definitions: &mut HashMap<String, String>);

    /// Helper method to add a single type definition to the map.
    fn add_single_type_definition(
        name: String,
        definition: String,
        definitions: &mut HashMap<String, String>,
    ) {
        match definitions.entry(name) {
            Entry::Occupied(occ) => {
                let existing_def = occ.get();
                assert_eq!(existing_def, &definition, "Redefining type schema for the same type name. Types with the same names are not supported.");
            }
            Entry::Vacant(vac) => {
                vac.insert(definition);
            }
        }
    }
    /// Get the name of the type without brackets.
    fn schema_type_name() -> String;
}

impl<T> BorshSchema for Box<T>
where
    T: BorshSchema,
{
    fn add_rec_type_definitions(definitions: &mut HashMap<String, String, RandomState>) {
        T::add_rec_type_definitions(definitions);
    }

    fn schema_type_name() -> String {
        T::schema_type_name()
    }
}

impl BorshSchema for () {
    fn add_rec_type_definitions(_definitions: &mut HashMap<String, String>) {}

    fn schema_type_name() -> String {
        "nil".to_string()
    }
}

macro_rules! impl_for_renamed_primitives {
    ($($type: ident : $name: ident)+) => {
    $(
        impl BorshSchema for $type {
            fn add_rec_type_definitions(_definitions: &mut HashMap<String, String>) {}
            fn schema_type_name() -> String {
                stringify!($name).to_string()
            }
        }
    )+
    };
}

macro_rules! impl_for_primitives {
    ($($type: ident)+) => {
    impl_for_renamed_primitives!{$($type : $type)+}
    };
}

impl_for_primitives!(bool char f32 f64 i8 i16 i32 i64 i128 u8 u16 u32 u64 u128);
impl_for_renamed_primitives!(String: string);

macro_rules! impl_arrays {
    ($($len:expr)+) => {
    $(
    impl<T> BorshSchema for [T; $len]
    where
        T: BorshSchema,
    {
        fn add_rec_type_definitions(definitions: &mut HashMap<String, String>) {
            let definition = format!(
                r#"{{ "kind": "array", "params": [ "{}", {} ] }}"#,
                T::schema_type_name(),
                $len
            );
            Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
            T::add_rec_type_definitions(definitions);
        }
        fn schema_type_name() -> String {
            format!(r#"Array<{}, {}>"#, T::schema_type_name(), $len)
        }
    }
    )+
    };
}

impl_arrays!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 32 64 65);

impl<T> BorshSchema for Option<T>
where
    T: BorshSchema,
{
    fn add_rec_type_definitions(definitions: &mut HashMap<String, String>) {
        let definition = format!(
            r#"{{ "kind": "enum", "variants": [ ["None", "{}"], ["Some", "{}"] ] }}"#,
            <()>::schema_type_name(),
            T::schema_type_name()
        );
        Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
        T::add_rec_type_definitions(definitions);
    }

    fn schema_type_name() -> String {
        format!(r#"Option<{}>"#, T::schema_type_name())
    }
}

impl<T, E> BorshSchema for Result<T, E>
where
    T: BorshSchema,
    E: BorshSchema,
{
    fn add_rec_type_definitions(definitions: &mut HashMap<String, String>) {
        let definition = format!(
            r#"{{ "kind": "enum", "variants": [ ["Ok", "{}"], ["Err", "{}"] ] }}"#,
            T::schema_type_name(),
            E::schema_type_name()
        );
        Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
        T::add_rec_type_definitions(definitions);
    }

    fn schema_type_name() -> String {
        format!(
            r#"Result<{}, {}>"#,
            T::schema_type_name(),
            E::schema_type_name()
        )
    }
}

impl<T> BorshSchema for Vec<T>
where
    T: BorshSchema,
{
    fn add_rec_type_definitions(definitions: &mut HashMap<String, String>) {
        let definition = format!(
            r#"{{ "kind": "sequence", "params": [ "{}" ] }}"#,
            T::schema_type_name()
        );
        Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
        T::add_rec_type_definitions(definitions);
    }

    fn schema_type_name() -> String {
        format!(r#"Vec<{}>"#, T::schema_type_name())
    }
}

impl<K, V> BorshSchema for HashMap<K, V>
where
    K: BorshSchema,
    V: BorshSchema,
{
    fn add_rec_type_definitions(definitions: &mut HashMap<String, String>) {
        let definition = format!(
            r#"{{ "kind": "sequence", "params": [ "{}" ] }}"#,
            <(K, V)>::schema_type_name()
        );
        Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
        <(K, V)>::add_rec_type_definitions(definitions);
    }

    fn schema_type_name() -> String {
        format!(
            r#"HashMap<{}, {}>"#,
            K::schema_type_name(),
            V::schema_type_name()
        )
    }
}

macro_rules! impl_tuple {
    ($($name:ident),+) => {
    impl<$($name),+> BorshSchema for ($($name),+)
    where
        $($name: BorshSchema),+
    {
        fn add_rec_type_definitions(definitions: &mut HashMap<String, String>) {

            let params = "".to_string();
            $(
                let params = if params.is_empty() {
                    format!(r#""{}""#, $name::schema_type_name())
                } else {
                    format!(r#"{}, "{}""#, params, $name::schema_type_name())
                };
            )+

            let definition = format!(r#"{{ "kind": "tuple", "params": [ {} ] }}"#, params);
            Self::add_single_type_definition(Self::schema_type_name(), definition, definitions);
            $(
                $name::add_rec_type_definitions(definitions);
            )+
        }

        fn schema_type_name() -> String {
            let params = "".to_string();
            $(
                let params = if params.is_empty() {
                    $name::schema_type_name()
                } else {
                    format!(r#"{}, {}"#, params, $name::schema_type_name())
                };
            )+
            format!(r#"Tuple<{}>"#, params)
        }
    }
    };
}

impl_tuple!(T0, T1);
impl_tuple!(T0, T1, T2);
impl_tuple!(T0, T1, T2, T3);
impl_tuple!(T0, T1, T2, T3, T4);
impl_tuple!(T0, T1, T2, T3, T4, T5);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18);
impl_tuple!(
    T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19
);
impl_tuple!(
    T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20
);

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! map(
    () => { ::std::collections::HashMap::new() };
    { $($key:expr => $value:expr),+ } => {
        {
            let mut m = ::std::collections::HashMap::new();
            $(
                m.insert($key.to_string(), $value.to_string());
            )+
            m
        }
     };
    );

    #[test]
    fn simple_option() {
        let actual_name = Option::<u64>::schema_type_name();
        let mut actual_defs = map!();
        Option::<u64>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("Option<u64>", actual_name);
        assert_eq!(
            map! {"Option<u64>" => r#"{ "kind": "enum", "variants": [ ["None", "nil"], ["Some", "u64"] ] }"#},
            actual_defs
        );
    }

    #[test]
    fn nested_option() {
        let actual_name = Option::<Option<u64>>::schema_type_name();
        let mut actual_defs = map!();
        Option::<Option<u64>>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("Option<Option<u64>>", actual_name);
        assert_eq!(
            map! {
            "Option<u64>" => r#"{ "kind": "enum", "variants": [ ["None", "nil"], ["Some", "u64"] ] }"#,
            "Option<Option<u64>>" => r#"{ "kind": "enum", "variants": [ ["None", "nil"], ["Some", "Option<u64>"] ] }"#
            },
            actual_defs
        );
    }

    #[test]
    fn simple_vec() {
        let actual_name = Vec::<u64>::schema_type_name();
        let mut actual_defs = map!();
        Vec::<u64>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("Vec<u64>", actual_name);
        assert_eq!(
            map! {"Vec<u64>" => r#"{ "kind": "sequence", "params": [ "u64" ] }"#},
            actual_defs
        );
    }

    #[test]
    fn nested_vec() {
        let actual_name = Vec::<Vec<u64>>::schema_type_name();
        let mut actual_defs = map!();
        Vec::<Vec<u64>>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("Vec<Vec<u64>>", actual_name);
        assert_eq!(
            map! {
            "Vec<u64>" => r#"{ "kind": "sequence", "params": [ "u64" ] }"#,
            "Vec<Vec<u64>>" => r#"{ "kind": "sequence", "params": [ "Vec<u64>" ] }"#
            },
            actual_defs
        );
    }

    #[test]
    fn simple_tuple() {
        let actual_name = <(u64, String)>::schema_type_name();
        let mut actual_defs = map!();
        <(u64, String)>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("Tuple<u64, string>", actual_name);
        assert_eq!(
            map! {"Tuple<u64, string>" => r#"{ "kind": "tuple", "params": [ "u64", "string" ] }"#},
            actual_defs
        );
    }

    #[test]
    fn nested_tuple() {
        let actual_name = <(u64, (u8, bool), String)>::schema_type_name();
        let mut actual_defs = map!();
        <(u64, (u8, bool), String)>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("Tuple<u64, Tuple<u8, bool>, string>", actual_name);
        assert_eq!(
            map! {
            "Tuple<u64, Tuple<u8, bool>, string>" => r#"{ "kind": "tuple", "params": [ "u64", "Tuple<u8, bool>", "string" ] }"#,
            "Tuple<u8, bool>" => r#"{ "kind": "tuple", "params": [ "u8", "bool" ] }"#
            },
            actual_defs
        );
    }

    #[test]
    fn simple_map() {
        let actual_name = HashMap::<u64, String>::schema_type_name();
        let mut actual_defs = map!();
        HashMap::<u64, String>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("HashMap<u64, string>", actual_name);
        assert_eq!(
            map! {
            "HashMap<u64, string>" => r#"{ "kind": "sequence", "params": [ "Tuple<u64, string>" ] }"#,
            "Tuple<u64, string>" => r#"{ "kind": "tuple", "params": [ "u64", "string" ] }"#
            },
            actual_defs
        );
    }

    #[test]
    fn simple_array() {
        let actual_name = <[u64; 32]>::schema_type_name();
        let mut actual_defs = map!();
        <[u64; 32]>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("Array<u64, 32>", actual_name);
        assert_eq!(
            map! {"Array<u64, 32>" => r#"{ "kind": "array", "params": [ "u64", 32 ] }"#},
            actual_defs
        );
    }

    #[test]
    fn nested_array() {
        let actual_name = <[[[u64; 9]; 10]; 32]>::schema_type_name();
        let mut actual_defs = map!();
        <[[[u64; 9]; 10]; 32]>::add_rec_type_definitions(&mut actual_defs);
        assert_eq!("Array<Array<Array<u64, 9>, 10>, 32>", actual_name);
        assert_eq!(
            map! {
            "Array<u64, 9>" => r#"{ "kind": "array", "params": [ "u64", 9 ] }"#,
            "Array<Array<u64, 9>, 10>" => r#"{ "kind": "array", "params": [ "Array<u64, 9>", 10 ] }"#,
            "Array<Array<Array<u64, 9>, 10>, 32>" => r#"{ "kind": "array", "params": [ "Array<Array<u64, 9>, 10>", 32 ] }"#
            },
            actual_defs
        );
    }
}
