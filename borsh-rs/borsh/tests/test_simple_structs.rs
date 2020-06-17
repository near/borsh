use borsh::{BorshDeserialize, BorshSerialize};
use std::collections::{HashMap, HashSet};

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
#[borsh_init(init)]
struct A<'a> {
    x: u64,
    b: B,
    y: f32,
    z: String,
    t: (String, u64),
    m: HashMap<String, String>,
    s: HashSet<u64>,
    v: Vec<String>,
    w: Box<[u8]>,
    box_str: Box<str>,
    i: [u8; 32],
    u: std::result::Result<String, String>,
    lazy: Option<u64>,
    c: std::borrow::Cow<'a, str>,
    cow_arr: std::borrow::Cow<'a, [std::borrow::Cow<'a, str>]>,
    #[borsh_skip]
    skipped: Option<u64>,
}

impl A<'_> {
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

#[test]
fn test_simple_struct() {
    let mut map: HashMap<String, String> = HashMap::new();
    map.insert("test".into(), "test".into());
    let mut set: HashSet<u64> = HashSet::new();
    set.insert(std::u64::MAX);
    let cow_arr = [
        std::borrow::Cow::Borrowed("Hello1"),
        std::borrow::Cow::Owned("Hello2".to_string()),
    ];
    let a = A {
        x: 1,
        b: B {
            x: 2,
            y: 3,
            c: C::C5(D { x: 1 }),
        },
        y: 4.0,
        z: "123".to_string(),
        t: ("Hello".to_string(), 10),
        m: map.clone(),
        s: set.clone(),
        v: vec!["qwe".to_string(), "zxc".to_string()],
        w: vec![0].into_boxed_slice(),
        box_str: Box::from("asd"),
        i: [4u8; 32],
        u: Ok("Hello".to_string()),
        lazy: Some(5),
        c: std::borrow::Cow::Borrowed("Hello"),
        cow_arr: std::borrow::Cow::Borrowed(&cow_arr),
        skipped: Some(6),
    };
    let encoded_a = a.try_to_vec().unwrap();
    let decoded_a = A::try_from_slice(&encoded_a).unwrap();
    let expected_a = A {
        x: 1,
        b: B {
            x: 2,
            y: 3,
            c: C::C5(D { x: 1 }),
        },
        y: 4.0,
        z: a.z,
        t: ("Hello".to_string(), 10),
        m: map.clone(),
        s: set.clone(),
        v: a.v,
        w: a.w,
        box_str: Box::from("asd"),
        i: a.i,
        u: Ok("Hello".to_string()),
        lazy: Some(50),
        c: std::borrow::Cow::Owned("Hello".to_string()),
        cow_arr: std::borrow::Cow::Owned(vec![
            std::borrow::Cow::Borrowed("Hello1"),
            std::borrow::Cow::Owned("Hello2".to_string()),
        ]),
        skipped: None,
    };

    assert_eq!(expected_a, decoded_a);
}
