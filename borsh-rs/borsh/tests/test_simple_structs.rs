use borsh::{BorshDeserialize, BorshSerialize};
use std::collections::{HashMap, HashSet};

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
#[borsh_init(init)]
struct A {
    x: u64,
    b: B,
    y: f32,
    z: String,
    t: (String, u64),
    m: HashMap<String, String>,
    s: HashSet<u64>,
    v: Vec<String>,
    w: Box<[u8]>,
    i: [u8; 32],
    lazy: Option<u64>,
    #[borsh_skip]
    skipped: Option<u64>,
}

impl A {
    pub fn init(&mut self) {
        if let Some(v) = self.lazy.as_mut() {
            *v *= 10;
        }
    }
}

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
struct B {
    x: u64,
    y: i32,
    c: C,
}

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
enum C {
    C1,
    C2(u64),
    C3(u64, u64),
    C4 { x: u64, y: u64 },
    C5(D),
}

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
struct D {
    x: u64,
}

#[derive(BorshSerialize, BorshDeserialize, Debug)]
struct E1;

#[derive(BorshSerialize, BorshDeserialize, Debug)]
struct E2 {}

#[derive(BorshSerialize, BorshDeserialize, Debug)]
struct E3();

#[derive(BorshSerialize, BorshDeserialize, Debug)]
struct E4 {
    #[borsh_skip]
    x: u32,
}

#[test]
fn test_simple_struct() {
    let mut map: HashMap<String, String> = HashMap::new();
    map.insert("test".into(), "test".into());
    let mut set: HashSet<u64> = HashSet::new();
    set.insert(std::u64::MAX);
    let a = A {
        x: 1,
        b: B { x: 2, y: 3, c: C::C5(D { x: 1 }) },
        y: 4.0,
        z: "123".to_string(),
        t: ("Hello".to_string(), 10),
        m: map.clone(),
        s: set.clone(),
        v: vec!["qwe".to_string(), "zxc".to_string()],
        w: vec![0].into_boxed_slice(),
        i: [4u8; 32],
        lazy: Some(5),
        skipped: Some(6),
    };
    let encoded_a = a.try_to_vec().unwrap();
    let decoded_a = A::try_from_slice(&encoded_a).unwrap();
    let expected_a = A {
        x: 1,
        b: B { x: 2, y: 3, c: C::C5(D { x: 1 }) },
        y: 4.0,
        z: a.z,
        t: ("Hello".to_string(), 10),
        m: map.clone(),
        s: set.clone(),
        v: a.v,
        w: a.w,
        i: a.i,
        lazy: Some(50),
        skipped: None,
    };

    assert_eq!(expected_a, decoded_a);
}

#[test]
fn test_unit_struct() {
    let e = E1 {};
    let encoded_e = e.try_to_vec().unwrap();
    assert_eq!(encoded_e, [0u8]);
    let _decoded_e = E1::try_from_slice(&encoded_e).unwrap();

    let broken_encoded_e: [u8; 0] = [];

    E1::try_from_slice(&broken_encoded_e).unwrap_err();
}

#[test]
fn test_unit_struct_with_brace() {
    let e = E2 {};
    let encoded_e = e.try_to_vec().unwrap();
    assert_eq!(encoded_e, [0u8]);
    let _decoded_e = E2::try_from_slice(&encoded_e).unwrap();

    let broken_encoded_e: [u8; 0] = [];

    E2::try_from_slice(&broken_encoded_e).unwrap_err();
}

#[test]
fn test_unit_struct_with_paren() {
    let e = E3 {};
    let encoded_e = e.try_to_vec().unwrap();
    assert_eq!(encoded_e, [0u8]);
    let _decoded_e = E3::try_from_slice(&encoded_e).unwrap();

    let broken_encoded_e: [u8; 0] = [];

    E3::try_from_slice(&broken_encoded_e).unwrap_err();
}

#[test]
fn test_struct_with_all_skip() {
    let e = E4 { x: 2 };
    let encoded_e = e.try_to_vec().unwrap();
    assert_eq!(encoded_e, [0u8]);
    let _decoded_e = E4::try_from_slice(&encoded_e).unwrap();

    let broken_encoded_e: [u8; 0] = [];

    E4::try_from_slice(&broken_encoded_e).unwrap_err();
}
