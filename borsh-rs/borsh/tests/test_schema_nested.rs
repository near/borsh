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

// Checks that recursive definitions work. Also checks that re-instantiations of templated types work.
#[test]
pub fn duplicated_instantiations() {
    #[derive(borsh::BorshSchema)]
    struct Tomatoes;
    #[derive(borsh::BorshSchema)]
    struct Cucumber;
    #[derive(borsh::BorshSchema)]
    struct Oil<K, V> {
        seeds: std::collections::HashMap<K, V>,
        liquid: Option<K>,
    };
    #[derive(borsh::BorshSchema)]
    struct Wrapper<T> {
        foo: Option<T>,
        bar: Box<A<T, T>>,
    };
    #[derive(borsh::BorshSchema)]
    struct Filling;
    #[derive(borsh::BorshSchema)]
    enum A<C, W> {
        Bacon,
        Eggs,
        Salad(Tomatoes, C, Oil<u64, String>),
        Sausage { wrapper: W, filling: Filling },
    }
    assert_eq!(
        "A<Cucumber, Wrapper<string>>".to_string(),
        <A<Cucumber, Wrapper<String>>>::schema_type_name()
    );
    let mut defs = Default::default();
    <A<Cucumber, Wrapper<String>>>::add_rec_type_definitions(&mut defs);
    assert_eq!(
        map! {
        "A<Cucumber, Wrapper<string>>" => "{ \"kind\": \"enum\", \"variants\": [ [\"Bacon\", \"ABacon<Cucumber, Wrapper<string>>\"], [\"Eggs\", \"AEggs<Cucumber, Wrapper<string>>\"], [\"Salad\", \"ASalad<Cucumber, Wrapper<string>>\"], [\"Sausage\", \"ASausage<Cucumber, Wrapper<string>>\"] ] }",
        "A<string, string>" => "{ \"kind\": \"enum\", \"variants\": [ [\"Bacon\", \"ABacon<string, string>\"], [\"Eggs\", \"AEggs<string, string>\"], [\"Salad\", \"ASalad<string, string>\"], [\"Sausage\", \"ASausage<string, string>\"] ] }",
        "ABacon<Cucumber, Wrapper<string>>" => "{ \"kind\": \"struct\", \"fields\": [  ] }",
        "ABacon<string, string>" => "{ \"kind\": \"struct\", \"fields\": [  ] }",
        "AEggs<Cucumber, Wrapper<string>>" => "{ \"kind\": \"struct\", \"fields\": [  ] }",
        "AEggs<string, string>" => "{ \"kind\": \"struct\", \"fields\": [  ] }",
        "ASalad<Cucumber, Wrapper<string>>" => "{ \"kind\": \"struct\", \"fields\": [ \"Tomatoes\", \"Cucumber\", \"Oil<u64, string>\" ] }",
        "ASalad<string, string>" => "{ \"kind\": \"struct\", \"fields\": [ \"Tomatoes\", \"string\", \"Oil<u64, string>\" ] }",
        "ASausage<Cucumber, Wrapper<string>>" => "{ \"kind\": \"struct\", \"fields\": [ [\"wrapper\", \"Wrapper<string>\"], [\"filling\", \"Filling\"] ] }",
        "ASausage<string, string>" => "{ \"kind\": \"struct\", \"fields\": [ [\"wrapper\", \"string\"], [\"filling\", \"Filling\"] ] }",
        "Cucumber" => "{ \"kind\": \"struct\", \"fields\": [  ] }",
        "Filling" => "{ \"kind\": \"struct\", \"fields\": [  ] }",
        "HashMap<u64, string>" => "{ \"kind\": \"sequence\", \"params\": [ \"Tuple<u64, string>\" ] }",
        "Oil<u64, string>" => "{ \"kind\": \"struct\", \"fields\": [ [\"seeds\", \"HashMap<u64, string>\"], [\"liquid\", \"Option<u64>\"] ] }",
        "Option<string>" => "{ \"kind\": \"enum\", \"variants\": [ [\"None\", \"nil\"], [\"Some\", \"string\"] ] }",
        "Option<u64>" => "{ \"kind\": \"enum\", \"variants\": [ [\"None\", \"nil\"], [\"Some\", \"u64\"] ] }",
        "Tomatoes" => "{ \"kind\": \"struct\", \"fields\": [  ] }",
        "Tuple<u64, string>" => "{ \"kind\": \"tuple\", \"params\": [ \"u64\", \"string\" ] }",
        "Wrapper<string>" => "{ \"kind\": \"struct\", \"fields\": [ [\"foo\", \"Option<string>\"], [\"bar\", \"A<string, string>\"] ] }"
        },
        defs
    );
}
