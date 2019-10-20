use borsh::BorshDeserialize;

#[derive(BorshDeserialize, Debug)]
enum A {
    X,
    Y
}

#[derive(BorshDeserialize, Debug)]
struct B {
    x: u64,
    y: u32,
}

#[test]
fn test_missing_bytes() {
    let bytes = vec![1, 0];
    assert_eq!(B::try_from_slice(&bytes).unwrap_err().to_string(), "failed to fill whole buffer");
}

#[test]
fn test_invalid_enum_variant() {
    let bytes = vec![123];
    assert_eq!(A::try_from_slice(&bytes).unwrap_err().to_string(), "Unexpected variant index: 123");
}

#[test]
fn test_extra_bytes() {
    let bytes = vec![1, 0, 0, 0, 32, 32];
    assert_eq!(<Vec<u8>>::try_from_slice(&bytes).unwrap_err().to_string(), "Not all bytes read");
}

#[test]
fn test_invalid_bool() {
    let bytes = vec![255];
    assert_eq!(<bool>::try_from_slice(&bytes).unwrap(), false);
}

#[test]
fn test_invalid_option() {
    let bytes = vec![255, 32];
    assert_eq!(<Option<u8>>::try_from_slice(&bytes).unwrap(), Some(32));
}

#[test]
fn test_invalid_length() {
    let bytes = vec![255u8; 4];
    assert_eq!(<Vec<u64>>::try_from_slice(&bytes).unwrap_err().to_string(), "failed to fill whole buffer");
}

#[test]
fn test_invalid_length_string() {
    let bytes = vec![255u8; 4];
    assert_eq!(String::try_from_slice(&bytes).unwrap_err().to_string(), "failed to fill whole buffer");
}

#[test]
fn test_non_utf_string() {
    let bytes = vec![1, 0, 0, 0, 0xC0];
    assert_eq!(String::try_from_slice(&bytes).unwrap_err().to_string(), "invalid utf-8 sequence of 1 bytes from index 0");
}

#[test]
fn test_nan_float() {
    let bytes = vec![0, 0, 192, 127];
    assert_eq!(f32::try_from_slice(&bytes).unwrap_err().to_string(), "For portability reasons we do not allow to deserialize NaNs.");
}
