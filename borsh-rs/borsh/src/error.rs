#[cfg(not(feature = "std"))]
pub use bare_io::{Error, ErrorKind, Result};
#[cfg(feature = "std")]
pub use std::io::{Error, ErrorKind, Result};
