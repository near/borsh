use borsh::{BorshDeserialize, BorshSerialize};

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
struct A<T, F, G, H> {
    x: Vec<T>,
    y: String,
    b: B<F, G>,
    a: Box<H>,
}

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
enum B<F, G> {
    X { f: Vec<F> },
    Y(G),
}

#[test]
fn test_generic_struct() {
    let a = A::<String, u64, String, u32> {
        x: vec!["foo".to_string(), "bar".to_string()],
        y: "world".to_string(),
        b: B::X {f: vec![1, 2]},
        a: Box::new(42)
    };
    let data = a.try_to_vec().unwrap();
    let actual_a = A::<String, u64, String, u32>::try_from_slice(&data).unwrap();
    assert_eq!(a, actual_a);
}
