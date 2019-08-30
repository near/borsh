use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{Cursor, Error, Read};
use std::mem::size_of;

/// A data-structure that can be de-serialized from binary format by NBOR.
pub trait BorshDeserialize: Sized {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error>;

    /// Deserialize this instance from a slice of bytes.
    fn try_from_slice(v: &[u8]) -> Result<Self, Error> {
        let mut c = Cursor::new(v);
        Self::deserialize(&mut c)
    }
}

macro_rules! impl_for_integer {
    ($type: ident) => {
        impl BorshDeserialize for $type {
            fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
                let mut data = [0u8; size_of::<$type>()];
                reader.read_exact(&mut data)?;
                Ok($type::from_le_bytes(data))
            }
        }
    };
}

impl_for_integer!(i8);
impl_for_integer!(i16);
impl_for_integer!(i32);
impl_for_integer!(i64);
impl_for_integer!(i128);
impl_for_integer!(isize);
impl_for_integer!(u8);
impl_for_integer!(u16);
impl_for_integer!(u32);
impl_for_integer!(u64);
impl_for_integer!(u128);
impl_for_integer!(usize);

// Note NaNs have a portability issue. Specifically, signalling NaNs on MIPS are quiet NaNs on x86,
// and vice-versa. We disallow NaNs to avoid this issue.
macro_rules! impl_for_float {
    ($type: ident, $int_type: ident) => {
        impl BorshDeserialize for $type {
            fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
                let mut data = [0u8; size_of::<$type>()];
                reader.read_exact(&mut data)?;
                let res = $type::from_bits($int_type::from_le_bytes(data));
                assert!(
                    !res.is_nan(),
                    "For portability reasons we do not allow to deserialize NaNs."
                );
                Ok(res)
            }
        }
    };
}

impl_for_float!(f32, u32);
impl_for_float!(f64, u64);

impl BorshDeserialize for bool {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let mut buf = [0u8];
        reader.read(&mut buf)?;
        Ok(buf[0] == 1)
    }
}

impl<T> BorshDeserialize for Option<T>
where
    T: BorshDeserialize,
{
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let mut flag = [0u8];
        reader.read_exact(&mut flag)?;
        if flag[0] == 0 {
            Ok(None)
        } else {
            Ok(Some(T::deserialize(reader)?))
        }
    }
}

impl BorshDeserialize for String {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let len = u32::deserialize(reader)?;
        let mut result = vec![0; len as usize];
        reader.read(&mut result)?;
        String::from_utf8(result)
            .map_err(|err| std::io::Error::new(std::io::ErrorKind::Other, err.to_string()))
    }
}

#[cfg(feature = "std")]
impl<T> BorshDeserialize for Vec<T>
where
    T: BorshDeserialize,
{
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let len = u32::deserialize(reader)?;
        let mut result = Vec::with_capacity(len as usize);
        for i in 0..len {
            result.push(T::deserialize(reader).map_err(|x| {
                println!("ind {}", i);
                x
            })?);
        }
        Ok(result)
    }
}

#[cfg(feature = "std")]
impl<T> BorshDeserialize for HashSet<T>
where
    T: BorshDeserialize + Eq + std::hash::Hash,
{
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let vec = <Vec<T>>::deserialize(reader)?;
        Ok(vec.into_iter().collect::<HashSet<T>>())
    }
}

#[cfg(feature = "std")]
impl<K, V> BorshDeserialize for HashMap<K, V>
where
    K: BorshDeserialize + Eq + std::hash::Hash,
    V: BorshDeserialize,
{
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let len = u32::deserialize(reader)?;
        let mut result = HashMap::with_capacity(len as usize);
        for _ in 0..len {
            let key = K::deserialize(reader)?;
            let value = V::deserialize(reader)?;
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
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let len = u32::deserialize(reader)?;
        let mut result = BTreeMap::new();
        for _ in 0..len {
            let key = K::deserialize(reader)?;
            let value = V::deserialize(reader)?;
            result.insert(key, value);
        }
        Ok(result)
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddr {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let kind = u8::deserialize(reader)?;
        match kind {
            0 => std::net::SocketAddrV4::deserialize(reader).map(|addr| std::net::SocketAddr::V4(addr)),
            1 => std::net::SocketAddrV6::deserialize(reader).map(|addr| std::net::SocketAddr::V6(addr)),
            value => panic!(format!("Invalid SocketAddr variant: {}", value)),
        }
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddrV4 {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let ip = std::net::Ipv4Addr::deserialize(reader)?;
        let port = u16::deserialize(reader)?;
        Ok(std::net::SocketAddrV4::new(ip, port))
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::SocketAddrV6 {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let ip = std::net::Ipv6Addr::deserialize(reader)?;
        let port = u16::deserialize(reader)?;
        Ok(std::net::SocketAddrV6::new(ip, port, 0, 0))
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::Ipv4Addr {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let mut buf = [0u8; 4];
        reader.read(&mut buf)?;
        Ok(std::net::Ipv4Addr::from(buf))
    }
}

#[cfg(feature = "std")]
impl BorshDeserialize for std::net::Ipv6Addr {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let mut buf = [0u8; 16];
        reader.read(&mut buf)?;
        Ok(std::net::Ipv6Addr::from(buf))
    }
}

impl BorshDeserialize for [u8; 32] {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let mut res = [0u8; 32];
        reader.read(&mut res)?;
        Ok(res)
    }
}

impl BorshDeserialize for Box<[u8]> {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, Error> {
        let len = u32::deserialize(reader)?;
        let mut res = Vec::with_capacity(len as usize);
        reader.read(&mut res)?;
        Ok(res.into_boxed_slice())
    }
}
