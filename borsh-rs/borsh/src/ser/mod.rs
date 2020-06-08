use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::mem::size_of;
use std::{io, io::Write};

const DEFAULT_SERIALIZER_CAPACITY: usize = 1024;

/// A data-structure that can be serialized into binary format by NBOR.
pub trait BorshSerialize {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()>;

    /// Serialize this instance into a vector of bytes.
    fn try_to_vec(&self) -> io::Result<Vec<u8>> {
        let mut result = Vec::with_capacity(DEFAULT_SERIALIZER_CAPACITY);
        self.serialize(&mut result)?;
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

impl BorshSerialize for u8 {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(std::slice::from_ref(self))
    }

    #[inline]
    fn is_u8() -> bool {
        true
    }
}

macro_rules! impl_for_integer {
    ($type: ident) => {
        impl BorshSerialize for $type {
            #[inline]
            fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
                writer.write_all(&self.to_le_bytes())
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
    ($type: ident) => {
        impl BorshSerialize for $type {
            #[inline]
            fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
                assert!(
                    !self.is_nan(),
                    "For portability reasons we do not allow to serialize NaNs."
                );
                writer.write_all(&self.to_bits().to_le_bytes())
            }
        }
    };
}

impl_for_float!(f32);
impl_for_float!(f64);

impl BorshSerialize for bool {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        (if *self { 1u8 } else { 0u8 }).serialize(writer)
    }
}

impl<T> BorshSerialize for Option<T>
where
    T: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            None => 0u8.serialize(writer),
            Some(value) => {
                1u8.serialize(writer)?;
                value.serialize(writer)
            }
        }
    }
}

impl<T, E> BorshSerialize for std::result::Result<T, E>
where
    T: BorshSerialize,
    E: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            Err(e) => {
                0u8.serialize(writer)?;
                e.serialize(writer)
            }
            Ok(v) => {
                1u8.serialize(writer)?;
                v.serialize(writer)
            }
        }
    }
}

impl BorshSerialize for str {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.as_bytes().serialize(writer)
    }
}

impl BorshSerialize for String {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.as_bytes().serialize(writer)
    }
}

impl<T> BorshSerialize for [T]
where
    T: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&(self.len() as u32).to_le_bytes())?;
        if T::is_u8() && size_of::<T>() == size_of::<u8>() {
            // The code below uses unsafe memory representation from `&[T]` to `&[u8]`.
            // The size of the memory should match because `size_of::<T>() == size_of::<u8>()`.
            //
            // `T::is_u8()` is a workaround for not being able to implement `Vec<u8>` separately.
            let buf = unsafe { std::slice::from_raw_parts(self.as_ptr() as *const u8, self.len()) };
            writer.write_all(buf)?;
        } else {
            for item in self {
                item.serialize(writer)?;
            }
        }
        Ok(())
    }
}

impl<T> BorshSerialize for Cow<'_, T>
where
    T: BorshSerialize + std::borrow::ToOwned + ?Sized,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.as_ref().serialize(writer)
    }
}

#[cfg(feature = "std")]
impl<T> BorshSerialize for Vec<T>
where
    T: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.as_slice().serialize(writer)
    }
}

#[cfg(feature = "std")]
impl<T> BorshSerialize for HashSet<T>
where
    T: BorshSerialize + PartialOrd,
{
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
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
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
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
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
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
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
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
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.ip().serialize(writer)?;
        self.port().serialize(writer)
    }
}

#[cfg(feature = "std")]
impl BorshSerialize for std::net::SocketAddrV6 {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.ip().serialize(writer)?;
        self.port().serialize(writer)
    }
}

#[cfg(feature = "std")]
impl BorshSerialize for std::net::Ipv4Addr {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.octets())
    }
}

#[cfg(feature = "std")]
impl BorshSerialize for std::net::Ipv6Addr {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.octets())
    }
}

impl BorshSerialize for Box<[u8]> {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        (self.len() as u32).serialize(writer)?;
        writer.write_all(self)
    }
}

impl<T: BorshSerialize> BorshSerialize for Box<T> {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.as_ref().serialize(writer)
    }
}

macro_rules! impl_arrays {
    ($($len:expr)+) => {
    $(
        impl<T> BorshSerialize for [T; $len]
        where T: BorshSerialize
        {
            #[inline]
            fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
                if T::is_u8() && size_of::<T>() == size_of::<u8>() {
                    // The code below uses unsafe memory representation from `&[T]` to `&[u8]`.
                    // The size of the memory should match because `size_of::<T>() == size_of::<u8>()`.
                    //
                    // `T::is_u8()` is a workaround for not being able to implement `[u8; *]` separately.
                    let buf = unsafe { std::slice::from_raw_parts(self.as_ptr() as *const u8, self.len()) };
                    writer.write_all(buf)?;
                } else {
                    for el in self.iter() {
                        el.serialize(writer)?;
                    }
                }
                Ok(())
            }
        }
    )+
    };
}

impl<T> BorshSerialize for [T; 0]
where
    T: BorshSerialize,
{
    #[inline]
    fn serialize<W: Write>(&self, _writer: &mut W) -> io::Result<()> {
        Ok(())
    }
}

impl_arrays!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 64 65 128 256 512 1024 2048);

impl BorshSerialize for () {
    fn serialize<W: Write>(&self, _writer: &mut W) -> io::Result<()> {
        Ok(())
    }
}

macro_rules! impl_tuple {
    ($($idx:tt $name:ident)+) => {
      impl<$($name),+> BorshSerialize for ($($name),+)
      where $($name: BorshSerialize,)+
      {
        #[inline]
        fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
            $(self.$idx.serialize(writer)?;)+
            Ok(())
        }
      }
    };
}

impl_tuple!(0 T0 1 T1);
impl_tuple!(0 T0 1 T1 2 T2);
impl_tuple!(0 T0 1 T1 2 T2 3 T3);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14 15 T15);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14 15 T15 16 T16);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14 15 T15 16 T16 17 T17);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14 15 T15 16 T16 17 T17 18 T18);
impl_tuple!(0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14 15 T15 16 T16 17 T17 18 T18 19 T19);
