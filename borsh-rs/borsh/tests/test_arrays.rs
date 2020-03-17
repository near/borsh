use borsh::{BorshDeserialize, BorshSerialize};

macro_rules! test_array {
    ($v: expr, $t: ty, $len: expr) => {
        let buf = $v.try_to_vec().unwrap();
        let actual_v: [$t; $len] =
            BorshDeserialize::try_from_slice(&buf).expect("failed to deserialize");
        assert_eq!($v.len(), actual_v.len());
        for i in 0..$len {
            assert_eq!($v[i], actual_v[i]);
        }
    };
}

macro_rules! test_arrays {
    ($test_name: ident, $el: expr, $t: ty) => {
        #[test]
        fn $test_name() {
            test_array!([$el; 0], $t, 0);
            test_array!([$el; 1], $t, 1);
            test_array!([$el; 2], $t, 2);
            test_array!([$el; 3], $t, 3);
            test_array!([$el; 4], $t, 4);
            test_array!([$el; 8], $t, 8);
            test_array!([$el; 16], $t, 16);
            test_array!([$el; 32], $t, 32);
            test_array!([$el; 64], $t, 64);
            test_array!([$el; 65], $t, 65);
        }
    };
}

test_arrays!(test_array_u8, 100u8, u8);
test_arrays!(test_array_i8, 100i8, i8);
test_arrays!(test_array_u32, 1000000000u32, u32);
test_arrays!(test_array_u64, 1000000000000000000u64, u64);
test_arrays!(test_array_u128, 1000000000000000000000000000000000000u128, u128);
test_arrays!(test_array_f32, 1000000000.0f32, f32);
test_arrays!(test_array_array_u8, [100u8; 32], [u8; 32]);
