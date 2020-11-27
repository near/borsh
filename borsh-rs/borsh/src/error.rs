#[cfg(not(feature = "std"))]
pub use bare_io::{Error, ErrorKind, Result};
#[cfg(feature = "std")]
pub use std::io::{Error, ErrorKind, Result};

// const ERROR_NOT_ALL_BYTES_READ: &str = "Not all bytes read";
// const ERROR_UNEXPECTED_LENGTH_OF_INPUT: &str = "Unexpected length of input";
//
// #[derive(Debug)]
// pub struct Error {
//     kind: ErrorKind,
//     message: alloc::string::String,
// }
//
// #[derive(Debug)]
// pub enum ErrorKind {
//     InvalidData,
//     InvalidInput,
// }
//
// #[cfg(feature = "std")]
// impl std::error::Error for Error {}
//
// pub type Result<T> = core::result::Result<T, Error>;
//
// #[cfg(any(feature = "alloc", feature = "std"))]
// impl Error {
//     pub fn new<E>(kind: ErrorKind, message: E) -> Error
//         where
//             E: Into<String>,
//     {
//         Error {
//             kind,
//             message: message.into(),
//         }
//     }
// }
