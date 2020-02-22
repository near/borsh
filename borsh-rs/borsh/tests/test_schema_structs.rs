use borsh::schema::BorshSchema;

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
pub fn unit_struct() {
    #[derive(borsh::BorshSchema)]
    struct A;
    assert_eq!("A".to_string(), A::schema_type_name());
    let mut defs = Default::default();
    A::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "A" => r#"{ "kind": "struct", "fields": [  ] }"#
        },
        defs
    );
}

#[test]
pub fn simple_struct() {
    #[derive(borsh::BorshSchema)]
    struct A {
        _f1: u64,
        _f2: String,
    };
    assert_eq!("A".to_string(), A::schema_type_name());
    let mut defs = Default::default();
    A::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "A" => r#"{ "kind": "struct", "fields": [ ["_f1", "u64"], ["_f2", "string"] ] }"#
        },
        defs
    );
}

#[test]
pub fn wrapper_struct() {
    #[derive(borsh::BorshSchema)]
    struct A<T>(T);
    assert_eq!("A<u64>".to_string(), <A<u64>>::schema_type_name());
    let mut defs = Default::default();
    <A<u64>>::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "A<u64>" => r#"{ "kind": "struct", "fields": [ "u64" ] }"#
        },
        defs
    );
}

#[test]
pub fn tuple_struct() {
    #[derive(borsh::BorshSchema)]
    struct A(u64, String);
    assert_eq!("A".to_string(), A::schema_type_name());
    let mut defs = Default::default();
    A::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "A" => r#"{ "kind": "struct", "fields": [ "u64", "string" ] }"#
        },
        defs
    );
}

#[test]
pub fn tuple_struct_params() {
    #[derive(borsh::BorshSchema)]
    struct A<K, V>(K, V);
    assert_eq!(
        "A<u64, string>".to_string(),
        <A<u64, String>>::schema_type_name()
    );
    let mut defs = Default::default();
    <A<u64, String>>::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "A<u64, string>" => r#"{ "kind": "struct", "fields": [ "u64", "string" ] }"#
        },
        defs
    );
}

#[test]
pub fn simple_generics() {
    #[derive(borsh::BorshSchema)]
    struct A<K, V> {
        _f1: std::collections::HashMap<K, V>,
        _f2: String,
    };
    assert_eq!(
        "A<u64, string>".to_string(),
        <A<u64, String>>::schema_type_name()
    );
    let mut defs = Default::default();
    <A<u64, String>>::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "A<u64, string>" => r#"{ "kind": "struct", "fields": [ ["_f1", "HashMap<u64, string>"], ["_f2", "string"] ] }"#,
        "HashMap<u64, string>" => r#"{ "kind": "sequence", "params": [ "Tuple<u64, string>" ] }"#,
        "Tuple<u64, string>" => r#"{ "kind": "tuple", "params": [ "u64", "string" ] }"#
        },
        defs
    );
}
