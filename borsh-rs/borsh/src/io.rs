use std::io::{Error, ErrorKind, Result};
use byteorder::{ByteOrder, LittleEndian};

pub trait Input {
    fn rem_len(&mut self) -> Result<usize>;
    fn read_byte(&mut self) -> Result<u8>;
    fn read(&mut self, buf: &mut [u8]) -> Result<()>;
    fn read_u32(&mut self) -> Result<u32>;
}

impl Input for &[u8] {
    fn rem_len(&mut self) -> Result<usize> {
        Ok(self.len())
    }

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

    fn read_u32(&mut self) -> Result<u32> {
        if self.len() < std::mem::size_of::<u32>() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                "failed to fill whole buffer",
            ));
        }
        let result =  LittleEndian::read_u32(self);
        *self = &self[std::mem::size_of::<u32>()..];
        Ok(result)
    }
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
