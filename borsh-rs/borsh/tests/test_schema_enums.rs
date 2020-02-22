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
pub fn simple_enum() {
    #[derive(borsh::BorshSchema)]
    enum A {
        Bacon,
        Eggs,
    }
    assert_eq!("A".to_string(), A::schema_type_name());
    let mut defs = Default::default();
    A::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "ABacon" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "AEggs" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "A" => r#"{ "kind": "enum", "variants": [ ["Bacon", "ABacon"], ["Eggs", "AEggs"] ] }"#
        },
        defs
    );
}

#[test]
pub fn single_field_enum() {
    #[derive(borsh::BorshSchema)]
    enum A {
        Bacon,
    }
    assert_eq!("A".to_string(), A::schema_type_name());
    let mut defs = Default::default();
    A::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "ABacon" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "A" => r#"{ "kind": "enum", "variants": [ ["Bacon", "ABacon"] ] }"#
        },
        defs
    );
}

#[test]
pub fn complex_enum() {
    #[derive(borsh::BorshSchema)]
    struct Tomatoes;
    #[derive(borsh::BorshSchema)]
    struct Cucumber;
    #[derive(borsh::BorshSchema)]
    struct Oil;
    #[derive(borsh::BorshSchema)]
    struct Wrapper;
    #[derive(borsh::BorshSchema)]
    struct Filling;
    #[derive(borsh::BorshSchema)]
    enum A {
        Bacon,
        Eggs,
        Salad(Tomatoes, Cucumber, Oil),
        Sausage { wrapper: Wrapper, filling: Filling },
    }
    assert_eq!("A".to_string(), A::schema_type_name());
    let mut defs = Default::default();
    A::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "Cucumber" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "ASalad" => r#"{ "kind": "struct", "fields": [ "Tomatoes", "Cucumber", "Oil" ] }"#,
        "ABacon" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "Oil" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "A" => r#"{ "kind": "enum", "variants": [ ["Bacon", "ABacon"], ["Eggs", "AEggs"], ["Salad", "ASalad"], ["Sausage", "ASausage"] ] }"#,
        "Wrapper" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "Tomatoes" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "ASausage" => r#"{ "kind": "struct", "fields": [ ["wrapper", "Wrapper"], ["filling", "Filling"] ] }"#,
        "AEggs" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "Filling" => r#"{ "kind": "struct", "fields": [  ] }"#},
        defs
    );
}

#[test]
pub fn complex_enum_generics() {
    #[derive(borsh::BorshSchema)]
    struct Tomatoes;
    #[derive(borsh::BorshSchema)]
    struct Cucumber;
    #[derive(borsh::BorshSchema)]
    struct Oil;
    #[derive(borsh::BorshSchema)]
    struct Wrapper;
    #[derive(borsh::BorshSchema)]
    struct Filling;
    #[derive(borsh::BorshSchema)]
    enum A<C, W> {
        Bacon,
        Eggs,
        Salad(Tomatoes, C, Oil),
        Sausage { wrapper: W, filling: Filling },
    }
    assert_eq!(
        "A<Cucumber, Wrapper>".to_string(),
        <A<Cucumber, Wrapper>>::schema_type_name()
    );
    let mut defs = Default::default();
    <A<Cucumber, Wrapper>>::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "Cucumber" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "ASalad<Cucumber, Wrapper>" => r#"{ "kind": "struct", "fields": [ "Tomatoes", "Cucumber", "Oil" ] }"#,
        "ABacon<Cucumber, Wrapper>" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "Oil" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "A<Cucumber, Wrapper>" => r#"{ "kind": "enum", "variants": [ ["Bacon", "ABacon<Cucumber, Wrapper>"], ["Eggs", "AEggs<Cucumber, Wrapper>"], ["Salad", "ASalad<Cucumber, Wrapper>"], ["Sausage", "ASausage<Cucumber, Wrapper>"] ] }"#,
        "Wrapper" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "Tomatoes" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "ASausage<Cucumber, Wrapper>" => r#"{ "kind": "struct", "fields": [ ["wrapper", "Wrapper"], ["filling", "Filling"] ] }"#,
        "AEggs<Cucumber, Wrapper>" => r#"{ "kind": "struct", "fields": [  ] }"#,
        "Filling" => r#"{ "kind": "struct", "fields": [  ] }"#},
        defs
    );
}
