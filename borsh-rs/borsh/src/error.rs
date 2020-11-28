#[cfg(not(feature = "std"))]
pub use self::_no_std::{Error, ErrorKind, Result};
#[cfg(feature = "std")]
pub use std::io::{Error, ErrorKind, Result};

#[cfg(not(feature = "std"))]
mod _no_std {
    //! Taken from https://github.com/bbqsrc/bare-io (with adjustments)

    use core::{convert::From, fmt, result};
    use crate::lib::String;

    /// A specialized [`Result`] type for I/O operations.
    ///
    /// This type is broadly used across [`std::io`] for any operation which may
    /// produce an error.
    ///
    /// This typedef is generally used to avoid writing out [`io::Error`] directly and
    /// is otherwise a direct mapping to [`Result`].
    ///
    /// While usual Rust style is to import types directly, aliases of [`Result`]
    /// often are not, to make it easier to distinguish between them. [`Result`] is
    /// generally assumed to be [`std::result::Result`][`Result`], and so users of this alias
    /// will generally use `io::Result` instead of shadowing the [prelude]'s import
    /// of [`std::result::Result`][`Result`].
    ///
    /// [`std::io`]: crate::io
    /// [`io::Error`]: Error
    /// [`Result`]: crate::result::Result
    /// [prelude]: crate::prelude
    ///
    /// # Examples
    ///
    /// A convenience function that bubbles an `io::Result` to its caller:
    ///
    /// ```
    /// use std::io;
    ///
    /// fn get_string() -> io::Result<String> {
    ///     let mut buffer = String::new();
    ///
    ///     io::stdin().read_line(&mut buffer)?;
    ///
    ///     Ok(buffer)
    /// }
    /// ```
    pub type Result<T> = result::Result<T, Error>;

    /// The error type for I/O operations of the [`Read`], [`Write`], [`Seek`], and
    /// associated traits.
    ///
    /// Errors mostly originate from the underlying OS, but custom instances of
    /// `Error` can be created with crafted error messages and a particular value of
    /// [`ErrorKind`].
    ///
    /// [`Read`]: crate::io::Read
    /// [`Write`]: crate::io::Write
    /// [`Seek`]: crate::io::Seek
    pub struct Error {
        repr: Repr,
    }

    impl fmt::Debug for Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Debug::fmt(&self.repr, f)
        }
    }

    enum Repr {
        Simple(ErrorKind),
        Custom(Custom),
    }

    #[derive(Debug)]
    struct Custom {
        kind: ErrorKind,
        error: String,
    }

    /// A list specifying general categories of I/O error.
    ///
    /// This list is intended to grow over time and it is not recommended to
    /// exhaustively match against it.
    ///
    /// It is used with the [`io::Error`] type.
    ///
    /// [`io::Error`]: Error
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
// #[allow(deprecated)]
    #[non_exhaustive]
    pub enum ErrorKind {
        /// An entity was not found, often a file.
        NotFound,
        /// The operation lacked the necessary privileges to complete.
        PermissionDenied,
        /// The connection was refused by the remote server.
        ConnectionRefused,
        /// The connection was reset by the remote server.
        ConnectionReset,
        /// The connection was aborted (terminated) by the remote server.
        ConnectionAborted,
        /// The network operation failed because it was not connected yet.
        NotConnected,
        /// A socket address could not be bound because the address is already in
        /// use elsewhere.
        AddrInUse,
        /// A nonexistent interface was requested or the requested address was not
        /// local.
        AddrNotAvailable,
        /// The operation failed because a pipe was closed.
        BrokenPipe,
        /// An entity already exists, often a file.
        AlreadyExists,
        /// The operation needs to block to complete, but the blocking operation was
        /// requested to not occur.
        WouldBlock,
        /// A parameter was incorrect.
        InvalidInput,
        /// Data not valid for the operation were encountered.
        ///
        /// Unlike [`InvalidInput`], this typically means that the operation
        /// parameters were valid, however the error was caused by malformed
        /// input data.
        ///
        /// For example, a function that reads a file into a string will error with
        /// `InvalidData` if the file's contents are not valid UTF-8.
        ///
        /// [`InvalidInput`]: ErrorKind::InvalidInput
        InvalidData,
        /// The I/O operation's timeout expired, causing it to be canceled.
        TimedOut,
        /// An error returned when an operation could not be completed because a
        /// call to [`write`] returned [`Ok(0)`].
        ///
        /// This typically means that an operation could only succeed if it wrote a
        /// particular number of bytes but only a smaller number of bytes could be
        /// written.
        ///
        /// [`write`]: crate::io::Write::write
        /// [`Ok(0)`]: Ok
        WriteZero,
        /// This operation was interrupted.
        ///
        /// Interrupted operations can typically be retried.
        Interrupted,
        /// Any I/O error not part of this list.
        ///
        /// Errors that are `Other` now may move to a different or a new
        /// [`ErrorKind`] variant in the future. It is not recommended to match
        /// an error against `Other` and to expect any additional characteristics,
        /// e.g., a specific [`Error::raw_os_error`] return value.
        Other,

        /// An error returned when an operation could not be completed because an
        /// "end of file" was reached prematurely.
        ///
        /// This typically means that an operation could only succeed if it read a
        /// particular number of bytes but only a smaller number of bytes could be
        /// read.
        UnexpectedEof,
    }

    impl ErrorKind {
        pub(crate) fn as_str(&self) -> &'static str {
            match *self {
                ErrorKind::NotFound => "entity not found",
                ErrorKind::PermissionDenied => "permission denied",
                ErrorKind::ConnectionRefused => "connection refused",
                ErrorKind::ConnectionReset => "connection reset",
                ErrorKind::ConnectionAborted => "connection aborted",
                ErrorKind::NotConnected => "not connected",
                ErrorKind::AddrInUse => "address in use",
                ErrorKind::AddrNotAvailable => "address not available",
                ErrorKind::BrokenPipe => "broken pipe",
                ErrorKind::AlreadyExists => "entity already exists",
                ErrorKind::WouldBlock => "operation would block",
                ErrorKind::InvalidInput => "invalid input parameter",
                ErrorKind::InvalidData => "invalid data",
                ErrorKind::TimedOut => "timed out",
                ErrorKind::WriteZero => "write zero",
                ErrorKind::Interrupted => "operation interrupted",
                ErrorKind::Other => "other os error",
                ErrorKind::UnexpectedEof => "unexpected end of file",
            }
        }
    }

    /// Intended for use for errors not exposed to the user, where allocating onto
    /// the heap (for normal construction via Error::new) is too costly.
    impl From<ErrorKind> for Error {
        /// Converts an [`ErrorKind`] into an [`Error`].
        ///
        /// This conversion allocates a new error with a simple representation of error kind.
        ///
        /// # Examples
        ///
        /// ```
        /// use std::io::{Error, ErrorKind};
        ///
        /// let not_found = ErrorKind::NotFound;
        /// let error = Error::from(not_found);
        /// assert_eq!("entity not found", format!("{}", error));
        /// ```
        #[inline]
        fn from(kind: ErrorKind) -> Error {
            Error {
                repr: Repr::Simple(kind),
            }
        }
    }

    impl Error {
        /// Creates a new I/O error from a known kind of error as well as an
        /// arbitrary error payload.
        ///
        /// This function is used to generically create I/O errors which do not
        /// originate from the OS itself. The `error` argument is an arbitrary
        /// payload which will be contained in this [`Error`].
        ///
        /// # Examples
        ///
        /// ```
        /// use std::io::{Error, ErrorKind};
        ///
        /// // errors can be created from strings
        /// let custom_error = Error::new(ErrorKind::Other, "oh no!");
        ///
        /// // errors can also be created from other errors
        /// let custom_error2 = Error::new(ErrorKind::Interrupted, custom_error);
        /// ```
        pub fn new<T: Into<String>>(kind: ErrorKind, error: T) -> Error {
            Self::_new(kind, error.into())
        }

        fn _new(kind: ErrorKind, error: String) -> Error {
            Error {
                repr: Repr::Custom(Custom { kind, error }),
            }
        }

        /// Returns a reference to the inner error wrapped by this error (if any).
        ///
        /// If this [`Error`] was constructed via [`new`] then this function will
        /// return [`Some`], otherwise it will return [`None`].
        ///
        /// [`new`]: Error::new
        ///
        /// # Examples
        ///
        /// ```
        /// use std::io::{Error, ErrorKind};
        ///
        /// fn print_error(err: &Error) {
        ///     if let Some(inner_err) = err.get_ref() {
        ///         println!("Inner error: {:?}", inner_err);
        ///     } else {
        ///         println!("No inner error");
        ///     }
        /// }
        ///
        /// fn main() {
        ///     // Will print "No inner error".
        ///     print_error(&Error::last_os_error());
        ///     // Will print "Inner error: ...".
        ///     print_error(&Error::new(ErrorKind::Other, "oh no!"));
        /// }
        /// ```
        pub fn get_ref(&self) -> Option<&str> {
            match self.repr {
                Repr::Simple(..) => None,
                Repr::Custom(ref c) => Some(&c.error),
            }
        }

        /// Consumes the `Error`, returning its inner error (if any).
        ///
        /// If this [`Error`] was constructed via [`new`] then this function will
        /// return [`Some`], otherwise it will return [`None`].
        ///
        /// [`new`]: Error::new
        ///
        /// # Examples
        ///
        /// ```
        /// use std::io::{Error, ErrorKind};
        ///
        /// fn print_error(err: Error) {
        ///     if let Some(inner_err) = err.into_inner() {
        ///         println!("Inner error: {}", inner_err);
        ///     } else {
        ///         println!("No inner error");
        ///     }
        /// }
        ///
        /// fn main() {
        ///     // Will print "No inner error".
        ///     print_error(Error::last_os_error());
        ///     // Will print "Inner error: ...".
        ///     print_error(Error::new(ErrorKind::Other, "oh no!"));
        /// }
        /// ```
        pub fn into_inner(self) -> Option<String> {
            match self.repr {
                Repr::Simple(..) => None,
                Repr::Custom(c) => Some(c.error),
            }
        }

        /// Returns the corresponding [`ErrorKind`] for this error.
        ///
        /// # Examples
        ///
        /// ```
        /// use std::io::{Error, ErrorKind};
        ///
        /// fn print_error(err: Error) {
        ///     println!("{:?}", err.kind());
        /// }
        ///
        /// fn main() {
        ///     // Will print "Other".
        ///     print_error(Error::last_os_error());
        ///     // Will print "AddrInUse".
        ///     print_error(Error::new(ErrorKind::AddrInUse, "oh no!"));
        /// }
        /// ```
        pub fn kind(&self) -> ErrorKind {
            match self.repr {
                Repr::Custom(ref c) => c.kind,
                Repr::Simple(kind) => kind,
            }
        }
    }

    impl fmt::Debug for Repr {
        fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
            match *self {
                Repr::Custom(ref c) => fmt::Debug::fmt(&c, fmt),
                Repr::Simple(kind) => fmt.debug_tuple("Kind").field(&kind).finish(),
            }
        }
    }

    impl fmt::Display for Error {
        fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self.repr {
                Repr::Custom(ref c) => c.error.fmt(fmt),
                Repr::Simple(kind) => write!(fmt, "{}", kind.as_str()),
            }
        }
    }

    fn _assert_error_is_sync_send() {
        fn _is_sync_send<T: Sync + Send>() {}
        _is_sync_send::<Error>();
    }
}
