use byteorder::{ByteOrder, LittleEndian};
use std::io::{Error, ErrorKind, Result};
use std::mem::size_of;

macro_rules! impl_read {
    ($name: ident, $type: ty) => {
        #[inline]
        fn $name(&mut self) -> Result<$type> {
            if self.len() < size_of::<$type>() {
                return Err(Error::new(
                    ErrorKind::InvalidInput,
                    "failed to fill whole buffer",
                ));
            }
            let res = LittleEndian::$name(&self);
            *self = &self[size_of::<$type>()..];
            Ok(res)
        }
}}

pub trait Input {
    fn rem_len(&mut self) -> Result<usize>;
    fn read_byte(&mut self) -> Result<u8>;
    fn read(&mut self, buf: &mut [u8]) -> Result<()>;

    fn read_u16(&mut self) -> Result<u16>;
    fn read_u32(&mut self) -> Result<u32>;
    fn read_u64(&mut self) -> Result<u64>;
    fn read_u128(&mut self) -> Result<u128>;

    fn read_i16(&mut self) -> Result<i16>;
    fn read_i32(&mut self) -> Result<i32>;
    fn read_i64(&mut self) -> Result<i64>;
    fn read_i128(&mut self) -> Result<i128>;

    fn read_f32(&mut self) -> Result<f32>;
    fn read_f64(&mut self) -> Result<f64>;
}

impl Input for &[u8] {
    #[inline]
    fn rem_len(&mut self) -> Result<usize> {
        Ok(self.len())
    }
    #[inline]
    fn read_byte(&mut self) -> Result<u8> {
        if self.len() < 1 {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                "Cannot read byte from input",
            ));
        }
        let res = self[0];
        *self = &self[1..];
        Ok(res)
    }
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<()> {
        if self.len() < buf.len() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                "failed to fill whole buffer",
            ));
        }
        buf.copy_from_slice(&self[0..buf.len()]);
        *self = &self[buf.len()..];
        Ok(())
    }
    impl_read!(read_u16, u16);
    impl_read!(read_u32, u32);
    impl_read!(read_u64, u64);
    impl_read!(read_u128, u128);

    impl_read!(read_i16, i16);
    impl_read!(read_i32, i32);
    impl_read!(read_i64, i64);
    impl_read!(read_i128, i128);

    impl_read!(read_f32, f32);
    impl_read!(read_f64, f64);
}

#[cfg(test)]
mod tests {
    use super::Input;
    #[test]
    fn test_read() {
        let input = [1u8, 2];
        let mut buf = [0u8; 1];
        let mut slice = &input[..];
        assert_eq!(slice.rem_len().unwrap(), 2);
        slice.read(&mut buf).unwrap();
        assert_eq!(buf, [1]);
        assert_eq!(slice.rem_len().unwrap(), 1);
        assert_eq!(slice, &[2]);
        slice.read(&mut buf).unwrap();
        assert_eq!(buf, [2]);
        assert_eq!(slice, &[]);
        assert_eq!(slice.rem_len().unwrap(), 0);
    }

    #[test]
    #[should_panic]
    fn test_read_end_of_input_err() {
        let input = [1u8, 2];
        let mut buf = [0u8; 3];
        let mut slice = &input[..];
        slice.read(&mut buf).unwrap();
    }

    #[test]
    fn test_read_byte() {
        let input = [1u8, 2];
        let mut slice = &input[..];
        assert_eq!(slice.rem_len().unwrap(), 2);
        assert_eq!(slice.read_byte().unwrap(), 1);
        assert_eq!(slice.read_byte().unwrap(), 2);
        assert_eq!(slice.rem_len().unwrap(), 0);
    }

    #[test]
    #[should_panic]
    fn test_read_byte_end_of_input_err() {
        let input = [1u8];
        let mut slice = &input[..];
        assert_eq!(slice.read_byte().unwrap(), 1);
        assert_eq!(slice.read_byte().unwrap(), 2);
    }
}
