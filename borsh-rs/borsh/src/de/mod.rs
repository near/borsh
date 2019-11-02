use crate::Input;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{Error};
mod hint;

/// A data-structure that can be de-serialized from binary format by NBOR.
pub trait BorshDeserialize: Sized {
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error>;

    /// Deserialize this instance from a slice of bytes.
    fn try_from_slice(mut v: &[u8]) -> Result<Self, Error> {
        let result = Self::deserialize(&mut v)?;
        Ok(result)
    }
}

impl BorshDeserialize for u8 {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        input.read_byte()
    }
}

impl BorshDeserialize for i8 {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        Ok(input.read_byte()? as i8)
    }
}

macro_rules! impl_for_integer {
    ($type: ty, $method: ident) => {
        impl BorshDeserialize for $type {
            #[inline]
            fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
                Ok(input.$method()?)
            }
        }
    };
}

impl_for_integer!(i16, read_i16);
impl_for_integer!(i32, read_i32);
impl_for_integer!(i64, read_i64);
impl_for_integer!(i128, read_i128);
impl_for_integer!(u16, read_u16);
impl_for_integer!(u32, read_u32);
impl_for_integer!(u64, read_u64);
impl_for_integer!(u128, read_u128);

// Note NaNs have a portability issue. Specifically, signalling NaNs on MIPS are quiet NaNs on x86,
// and vice-versa. We disallow NaNs to avoid this issue.
macro_rules! impl_for_float {
    ($type: ty, $method: ident) => {
        impl BorshDeserialize for $type {
            #[inline]
            fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
                let res = input.$method()?;
                if res.is_nan() {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidInput,
                        "For portability reasons we do not allow to deserialize NaNs.",
                    ));
                }
                Ok(res)
            }
        }
    };
}


impl_for_float!(f32, read_f32);
impl_for_float!(f64, read_f64);

impl BorshDeserialize for bool {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        Ok(input.read_byte()? == 1)
    }
}

impl<T> BorshDeserialize for Option<T>
where
    T: BorshDeserialize,
{
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let mut flag = [0u8];
        input.read(&mut flag)?;
        if flag[0] == 0 {
            Ok(None)
        } else {
            Ok(Some(T::deserialize(input)?))
        }
    }
}

impl BorshDeserialize for String {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let len = u32::deserialize(input)?;
        // TODO(16): return capacity allocation when we have the size of the buffer left from the reader.
        let mut result = Vec::with_capacity(hint::cautious::<u8>(input.rem_len()? as u32, len));
        for _ in 0..len {
            result.push(u8::deserialize(input)?);
        }
        String::from_utf8(result)
            .map_err(|err| std::io::Error::new(std::io::ErrorKind::InvalidData, err.to_string()))
    }
}

#[cfg(feature = "std")]
impl<T> BorshDeserialize for Vec<T>
where
    T: BorshDeserialize,
{
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let len = u32::deserialize(input)?;
        // TODO(16): return capacity allocation when we can safely do that.
        let mut result = Vec::with_capacity(hint::cautious::<T>(input.rem_len()? as u32, len));
        for _ in 0..len {
            result.push(T::deserialize(input)?);
        }
        Ok(result)
    }
}

#[cfg(feature = "std")]
impl<T> BorshDeserialize for HashSet<T>
where
    T: BorshDeserialize + Eq + std::hash::Hash,
{
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let vec = <Vec<T>>::deserialize(input)?;
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
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let len = u32::deserialize(input)?;
        // TODO(16): return capacity allocation when we can safely do that.
        let mut result = HashMap::new();
        for _ in 0..len {
            let key = K::deserialize(input)?;
            let value = V::deserialize(input)?;
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
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let len = u32::deserialize(input)?;
        let mut result = BTreeMap::new();
        for _ in 0..len {
            let key = K::deserialize(input)?;
            let value = V::deserialize(input)?;
            result.insert(key, value);
        }
        Ok(result)
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddr {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let kind = u8::deserialize(input)?;
        match kind {
            0 => std::net::SocketAddrV4::deserialize(input).map(std::net::SocketAddr::V4),
            1 => std::net::SocketAddrV6::deserialize(input).map(std::net::SocketAddr::V6),
            value => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("Invalid SocketAddr variant: {}", value),
            )),
        }
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddrV4 {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let ip = std::net::Ipv4Addr::deserialize(input)?;
        let port = u16::deserialize(input)?;
        Ok(std::net::SocketAddrV4::new(ip, port))
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddrV6 {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let ip = std::net::Ipv6Addr::deserialize(input)?;
        let port = u16::deserialize(input)?;
        Ok(std::net::SocketAddrV6::new(ip, port, 0, 0))
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::Ipv4Addr {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let mut buf = [0u8; 4];
        input.read(&mut buf)?;
        Ok(std::net::Ipv4Addr::from(buf))
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::Ipv6Addr {
    #[inline]
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let mut buf = [0u8; 16];
        input.read(&mut buf)?;
        Ok(std::net::Ipv6Addr::from(buf))
    }
}

impl<T: BorshDeserialize> BorshDeserialize for Box<T> {
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        Ok(Box::new(T::deserialize(input)?))
    }
}

impl BorshDeserialize for Box<[u8]> {
    fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
        let len = u32::deserialize(input)?;
        // TODO(16): return capacity allocation when we can safely do that.
        let mut result = Vec::with_capacity(hint::cautious::<u8>(input.rem_len()? as u32, len));
        for _ in 0..len {
            result.push(u8::deserialize(input)?);
        }
        Ok(result.into_boxed_slice())
    }
}

macro_rules! impl_arrays {
    ($($len:expr)+) => {
    $(
      impl BorshDeserialize for [u8; $len]
      {
        #[inline]
        fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
            let mut result = [0u8; $len];
            input.read(&mut result)?;
            Ok(result)
        }
      }
      )+
    };
}

impl_arrays!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 32 64 65);

macro_rules! impl_tuple {
    ($($name:ident)+) => {
      impl<$($name),+> BorshDeserialize for ($($name),+)
      where $($name: BorshDeserialize,)+
      {
        #[inline]
        fn deserialize<I: Input>(input: &mut I) -> Result<Self, Error> {
            Ok(($($name::deserialize(input)?,)+))
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
