pub use borsh_derive::{BorshDeserialize, BorshSerialize};

pub mod de;
pub mod ser;

pub use de::BorshDeserialize;
pub use ser::BorshSerialize;

use std::io::{Result, Error, ErrorKind};

pub trait Input {
    fn rem_len(&mut self) -> Result<usize>;
    fn read_byte(&mut self) -> Result<u8>;
    fn read(&mut self, buf: &mut [u8]) -> Result<()>;
}

impl Input for &[u8] {
    fn rem_len(&mut self) -> Result<usize> {
        Ok(self.len())
    }
    fn read_byte(&mut self) -> Result<u8> {
        if self.len() < 1 {
            return Err(Error::new(ErrorKind::InvalidInput, "Cannot read byte from input"));
        }
        let res = self[0];
        *self = &self[1..];
        Ok(res)
    }
    fn read(&mut self, buf: &mut [u8]) -> Result<()> {
        if self.len() < buf.len() {
            return Err(Error::new(ErrorKind::InvalidInput, "failed to fill whole buffer"));
        }
        buf.copy_from_slice(&self[0..buf.len()]);
        *self = &self[buf.len()..];
        Ok(())
    }
}
