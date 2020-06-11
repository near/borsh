use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::convert::TryInto;
use std::io;
use std::mem::{forget, size_of};

mod hint;

const ERROR_NOT_ALL_BYTES_READ: &str = "Not all bytes read";
const ERROR_UNEXPECTED_LENGTH_OF_INPUT: &str = "Unexpected length of input";

/// A data-structure that can be de-serialized from binary format by NBOR.
pub trait BorshDeserialize: Sized {
    /// Deserializes this instance from a given slice of bytes.
    /// Updates the buffer to point at the remaining bytes.
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self>;

    /// Deserialize this instance from a slice of bytes.
    fn try_from_slice(v: &[u8]) -> io::Result<Self> {
        let mut v_mut = v;
        let result = Self::deserialize(&mut v_mut)?;
        if !v_mut.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                ERROR_NOT_ALL_BYTES_READ,
            ));
        }
        Ok(result)
    }

    /// Whether Self is u8.
    /// NOTE: `Vec<u8>` is the most common use-case for serialization and deserialization, it's
    /// worth handling it as a special case to improve performance.
    /// It's a workaround for specific `Vec<u8>` implementation versus generic `Vec<T>`
    /// implementation. See https://github.com/rust-lang/rfcs/pull/1210 for details.
    #[inline]
    fn is_u8() -> bool {
        false
    }
}

impl BorshDeserialize for u8 {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        if buf.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let res = buf[0];
        *buf = &buf[1..];
        Ok(res)
    }

    #[inline]
    fn is_u8() -> bool {
        true
    }
}

macro_rules! impl_for_integer {
    ($type: ident) => {
        impl BorshDeserialize for $type {
            #[inline]
            fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
                if buf.len() < size_of::<$type>() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        ERROR_UNEXPECTED_LENGTH_OF_INPUT,
                    ));
                }
                let res = $type::from_le_bytes(buf[..size_of::<$type>()].try_into().unwrap());
                *buf = &buf[size_of::<$type>()..];
                Ok(res)
            }
        }
    };
}

impl_for_integer!(i8);
impl_for_integer!(i16);
impl_for_integer!(i32);
impl_for_integer!(i64);
impl_for_integer!(i128);
impl_for_integer!(u16);
impl_for_integer!(u32);
impl_for_integer!(u64);
impl_for_integer!(u128);

// Note NaNs have a portability issue. Specifically, signalling NaNs on MIPS are quiet NaNs on x86,
// and vice-versa. We disallow NaNs to avoid this issue.
macro_rules! impl_for_float {
    ($type: ident, $int_type: ident) => {
        impl BorshDeserialize for $type {
            #[inline]
            fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
                if buf.len() < size_of::<$type>() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        ERROR_UNEXPECTED_LENGTH_OF_INPUT,
                    ));
                }
                let res = $type::from_bits($int_type::from_le_bytes(
                    buf[..size_of::<$int_type>()].try_into().unwrap(),
                ));
                *buf = &buf[size_of::<$int_type>()..];
                if res.is_nan() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "For portability reasons we do not allow to deserialize NaNs.",
                    ));
                }
                Ok(res)
            }
        }
    };
}

impl_for_float!(f32, u32);
impl_for_float!(f64, u64);

impl BorshDeserialize for bool {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        if buf.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let b = buf[0];
        *buf = &buf[1..];
        if b == 0 {
            Ok(false)
        } else if b == 1 {
            Ok(true)
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Invalid bool representation: {}", b),
            ))
        }
    }
}

impl<T> BorshDeserialize for Option<T>
where
    T: BorshDeserialize,
{
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        if buf.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let flag = buf[0];
        *buf = &buf[1..];
        if flag == 0 {
            Ok(None)
        } else if flag == 1 {
            Ok(Some(T::deserialize(buf)?))
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "Invalid Option representation: {}. The first byte must be 0 or 1",
                    flag
                ),
            ))
        }
    }
}

impl<T, E> BorshDeserialize for std::result::Result<T, E>
where
    T: BorshDeserialize,
    E: BorshDeserialize,
{
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        if buf.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let flag = buf[0];
        *buf = &buf[1..];
        if flag == 0 {
            Ok(Err(E::deserialize(buf)?))
        } else if flag == 1 {
            Ok(Ok(T::deserialize(buf)?))
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "Invalid Result representation: {}. The first byte must be 0 or 1",
                    flag
                ),
            ))
        }
    }
}

impl BorshDeserialize for String {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        String::from_utf8(Vec::<u8>::deserialize(buf)?)
            .map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err.to_string()))
    }
}

#[cfg(feature = "std")]
impl<T> BorshDeserialize for Vec<T>
where
    T: BorshDeserialize,
{
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        let len = u32::deserialize(buf)?;
        if len == 0 {
            Ok(Vec::new())
        } else if T::is_u8() && size_of::<T>() == size_of::<u8>() {
            let len = len as usize;
            if buf.len() < len {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    ERROR_UNEXPECTED_LENGTH_OF_INPUT,
                ));
            }
            let result = buf[..len].to_vec();
            *buf = &buf[len..];
            // See comment from https://doc.rust-lang.org/std/mem/fn.transmute.html
            // The no-copy, unsafe way, still using transmute, but not UB.
            // This is equivalent to the original, but safer, and reuses the
            // same `Vec` internals. Therefore, the new inner type must have the
            // exact same size, and the same alignment, as the old type.
            //
            // The size of the memory should match because `size_of::<T>() == size_of::<u8>()`.
            //
            // `T::is_u8()` is a workaround for not being able to implement `Vec<u8>` separately.
            let result = unsafe {
                // Ensure the original vector is not dropped.
                let mut v_clone = std::mem::ManuallyDrop::new(result);
                Vec::from_raw_parts(
                    v_clone.as_mut_ptr() as *mut T,
                    v_clone.len(),
                    v_clone.capacity(),
                )
            };
            Ok(result)
        } else if size_of::<T>() == 0 {
            let mut result = Vec::new();
            result.push(T::deserialize(buf)?);

            let p = result.as_mut_ptr();
            unsafe {
                forget(result);
                let len = len as usize;
                let result = Vec::from_raw_parts(p, len, len);
                Ok(result)
            }
        } else {
            // TODO(16): return capacity allocation when we can safely do that.
            let mut result = Vec::with_capacity(hint::cautious::<T>(len));
            for _ in 0..len {
                result.push(T::deserialize(buf)?);
            }
            Ok(result)
        }
    }
}

impl<T> BorshDeserialize for Cow<'_, T>
where
    T: std::borrow::ToOwned + ?Sized,
    T::Owned: BorshDeserialize,
{
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        Ok(Cow::Owned(BorshDeserialize::deserialize(buf)?))
    }
}

#[cfg(feature = "std")]
impl<T> BorshDeserialize for HashSet<T>
where
    T: BorshDeserialize + Eq + std::hash::Hash,
{
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        let vec = <Vec<T>>::deserialize(buf)?;
        Ok(vec.into_iter().collect::<HashSet<T>>())
    }
}

#[cfg(feature = "std")]
impl<K, V> BorshDeserialize for HashMap<K, V>
where
    K: BorshDeserialize + Eq + std::hash::Hash,
    V: BorshDeserialize,
{
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        let len = u32::deserialize(buf)?;
        // TODO(16): return capacity allocation when we can safely do that.
        let mut result = HashMap::new();
        for _ in 0..len {
            let key = K::deserialize(buf)?;
            let value = V::deserialize(buf)?;
            result.insert(key, value);
        }
        Ok(result)
    }
}

#[cfg(feature = "std")]
impl<K, V> BorshDeserialize for BTreeMap<K, V>
where
    K: BorshDeserialize + Ord + std::hash::Hash,
    V: BorshDeserialize,
{
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        let len = u32::deserialize(buf)?;
        let mut result = BTreeMap::new();
        for _ in 0..len {
            let key = K::deserialize(buf)?;
            let value = V::deserialize(buf)?;
            result.insert(key, value);
        }
        Ok(result)
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddr {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        let kind = u8::deserialize(buf)?;
        match kind {
            0 => std::net::SocketAddrV4::deserialize(buf).map(std::net::SocketAddr::V4),
            1 => std::net::SocketAddrV6::deserialize(buf).map(std::net::SocketAddr::V6),
            value => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Invalid SocketAddr variant: {}", value),
            )),
        }
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddrV4 {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        let ip = std::net::Ipv4Addr::deserialize(buf)?;
        let port = u16::deserialize(buf)?;
        Ok(std::net::SocketAddrV4::new(ip, port))
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddrV6 {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        let ip = std::net::Ipv6Addr::deserialize(buf)?;
        let port = u16::deserialize(buf)?;
        Ok(std::net::SocketAddrV6::new(ip, port, 0, 0))
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::Ipv4Addr {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        if buf.len() < 4 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let bytes: [u8; 4] = buf[..4].try_into().unwrap();
        let res = std::net::Ipv4Addr::from(bytes);
        *buf = &buf[4..];
        Ok(res)
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::Ipv6Addr {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        if buf.len() < 16 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let bytes: [u8; 16] = buf[..16].try_into().unwrap();
        let res = std::net::Ipv6Addr::from(bytes);
        *buf = &buf[16..];
        Ok(res)
    }
}

impl BorshDeserialize for Box<[u8]> {
    #[inline]
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        let len = u32::deserialize(buf)? as usize;
        if buf.len() < len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }
        let res = buf[..len].to_vec().into_boxed_slice();
        *buf = &buf[len..];
        Ok(res)
    }
}

impl<T: BorshDeserialize> BorshDeserialize for Box<T> {
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        Ok(Box::new(T::deserialize(buf)?))
    }
}

macro_rules! impl_arrays {
    ($($len:expr)+) => {
    $(
        impl<T> BorshDeserialize for [T; $len]
        where
            T: BorshDeserialize + Default + Copy
        {
            #[inline]
            fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
                let mut result = [T::default(); $len];
                if T::is_u8() && size_of::<T>() == size_of::<u8>() {
                    if buf.len() < $len {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            ERROR_UNEXPECTED_LENGTH_OF_INPUT,
                        ));
                    }
                    // The size of the memory should match because `size_of::<T>() == size_of::<u8>()`.
                    // `T::is_u8()` is a workaround for not being able to implement `[u8; *]` separately.
                    result.copy_from_slice(unsafe { std::slice::from_raw_parts(buf.as_ptr() as *const T, $len) });
                    *buf = &buf[$len..];
                } else {
                    for i in 0..$len {
                        result[i] = T::deserialize(buf)?;
                    }
                }
                Ok(result)
            }
        }
    )+
    };
}

impl_arrays!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 64 65 128 256 512 1024 2048);

impl<T> BorshDeserialize for [T; 0]
where
    T: BorshDeserialize + Default + Copy,
{
    #[inline]
    fn deserialize(_buf: &mut &[u8]) -> io::Result<Self> {
        Ok([T::default(); 0])
    }
}

impl BorshDeserialize for () {
    fn deserialize(_buf: &mut &[u8]) -> io::Result<Self> {
        Ok(())
    }
}

macro_rules! impl_tuple {
    ($($name:ident)+) => {
      impl<$($name),+> BorshDeserialize for ($($name),+)
      where $($name: BorshDeserialize,)+
      {
        #[inline]
        fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {

            Ok(($($name::deserialize(buf)?,)+))
        }
      }
    };
}

impl_tuple!(T0 T1);
impl_tuple!(T0 T1 T2);
impl_tuple!(T0 T1 T2 T3);
impl_tuple!(T0 T1 T2 T3 T4);
impl_tuple!(T0 T1 T2 T3 T4 T5);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18);
impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19);
