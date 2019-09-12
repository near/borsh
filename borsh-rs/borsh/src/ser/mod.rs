use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{Error, Write};

const DEFAULT_SERIALIZER_CAPACITY: usize = 1024;

/// A data-structure that can be serialized into binary format by NBOR.
pub trait BorshSerialize {
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error>;

    /// Serialize this instance into a vector of bytes.
    fn try_to_vec(&self) -> Result<Vec<u8>, Error> {
        let mut result = Vec::with_capacity(DEFAULT_SERIALIZER_CAPACITY);
        self.serialize(&mut result)?;
        Ok(result)
    }
}

impl BorshSerialize for u8 {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        writer.write(std::slice::from_ref(self)).map(|_| ())
    }
}

macro_rules! impl_for_integer {
    ($type: ident) => {
        impl BorshSerialize for $type {
            #[inline]
            fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
                writer.write(&self.to_le_bytes()).map(|_| ())
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
impl_for_integer!(u16);
impl_for_integer!(u32);
impl_for_integer!(u64);
impl_for_integer!(u128);
impl_for_integer!(usize);

// Note NaNs have a portability issue. Specifically, signalling NaNs on MIPS are quiet NaNs on x86,
// and vice-versa. We disallow NaNs to avoid this issue.
macro_rules! impl_for_float {
    ($type: ident) => {
        impl BorshSerialize for $type {
            #[inline]
            fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
                assert!(
                    !self.is_nan(),
                    "For portability reasons we do not allow to serialize NaNs."
                );
                writer.write(&self.to_bits().to_le_bytes()).map(|_| ())
            }
        }
    };
}

impl_for_float!(f32);
impl_for_float!(f64);

impl BorshSerialize for bool {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        (if *self { 1u8 } else { 0u8 }).serialize(writer)
    }
}

impl<T> BorshSerialize for Option<T>
where
    T: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        match self {
            None => 0u8.serialize(writer),
            Some(value) => {
                1u8.serialize(writer)?;
                value.serialize(writer)
            }
        }
    }
}

impl BorshSerialize for String {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        writer.write(&(self.len() as u32).to_le_bytes())?;
        writer.write(self.as_bytes())?;
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<T> BorshSerialize for Vec<T>
where
    T: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        writer.write(&(self.len() as u32).to_le_bytes())?;
        for item in self {
            item.serialize(writer)?;
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<T> BorshSerialize for HashSet<T>
where
    T: BorshSerialize + PartialOrd,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        let mut vec = self.iter().collect::<Vec<_>>();
        vec.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (vec.len() as u32).serialize(writer)?;
        for item in vec {
            item.serialize(writer)?;
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<K, V> BorshSerialize for HashMap<K, V>
where
    K: BorshSerialize + PartialOrd,
    V: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        let mut vec = self.iter().collect::<Vec<_>>();
        vec.sort_by(|(a, _), (b, _)| a.partial_cmp(b).unwrap());
        (vec.len() as u32).serialize(writer)?;
        for (key, value) in vec {
            key.serialize(writer)?;
            value.serialize(writer)?;
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<K, V> BorshSerialize for BTreeMap<K, V>
where
    K: BorshSerialize + PartialOrd,
    V: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        (self.len() as u32).serialize(writer)?;
        for (key, value) in self.iter() {
            key.serialize(writer)?;
            value.serialize(writer)?;
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
impl BorshSerialize for std::net::SocketAddr {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        match *self {
            std::net::SocketAddr::V4(ref addr) => {
                0u8.serialize(writer)?;
                addr.serialize(writer)
            }
            std::net::SocketAddr::V6(ref addr) => {
                1u8.serialize(writer)?;
                addr.serialize(writer)
            }
        }
    }
}

#[cfg(feature = "std")]
impl BorshSerialize for std::net::SocketAddrV4 {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        self.ip().serialize(writer)?;
        self.port().serialize(writer)
    }
}

#[cfg(feature = "std")]
impl BorshSerialize for std::net::SocketAddrV6 {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        self.ip().serialize(writer)?;
        self.port().serialize(writer)
    }
}

#[cfg(feature = "std")]
impl BorshSerialize for std::net::Ipv4Addr {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        writer.write(&self.octets()).map(|_| ())
    }
}

#[cfg(feature = "std")]
impl BorshSerialize for std::net::Ipv6Addr {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        writer.write(&self.octets()).map(|_| ())
    }
}

macro_rules! impl_for_fixed_len_array {
    ($len: expr) => {
        impl BorshSerialize for [u8; $len] {
            #[inline]
            fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
                writer.write(self).map(|_| ())
            }
        }
    };
}

impl_for_fixed_len_array!(32);
impl_for_fixed_len_array!(64);
impl_for_fixed_len_array!(65);

impl BorshSerialize for Box<[u8]> {
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        (self.len() as u32).serialize(writer)?;
        writer.write(self).map(|_| ())
    }
}

