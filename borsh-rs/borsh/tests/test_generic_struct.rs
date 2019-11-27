use borsh::{BorshDeserialize, BorshSerialize};

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
struct A<T, F, G> {
    x: Vec<T>,
    y: String,
    b: B<F, G>,
    c: Result<T, G>,
}

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
enum B<F, G> {
    X { f: Vec<F> },
    Y(G),
}

#[test]
fn test_generic_struct() {
    let a = A::<String, u64, String> {
        x: vec!["foo".to_string(), "bar".to_string()],
        y: "world".to_string(),
        b: B::X { f: vec![1, 2] },
        c: Err("error".to_string()),
    };
    let data = a.try_to_vec().unwrap();
    let actual_a = A::<String, u64, String>::try_from_slice(&data).unwrap();
    assert_eq!(a, actual_a);
}
