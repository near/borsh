use borsh::{BorshDeserialize, BorshSerialize};

macro_rules! test_string {
    ($test_name: ident, $str: expr) => {
        #[test]
        fn $test_name() {
            let s = $str.to_string();
            let buf = s.try_to_vec().unwrap();
            let actual_s = <String>::try_from_slice(&buf).expect("failed to deserialize a string");
            assert_eq!(actual_s, s);
        }
    };
}

test_string!(test_empty_string, "");
test_string!(test_a, "a");
test_string!(test_hello_world, "hello world");
test_string!(test_x_1024, String::from_utf8(vec![b'X'; 1024]).unwrap());
test_string!(test_x_4096, String::from_utf8(vec![b'X'; 4096]).unwrap());
test_string!(test_x_65535, String::from_utf8(vec![b'X'; 65535]).unwrap());
