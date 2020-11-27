#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std as alloc;

pub use borsh_derive::{BorshDeserialize, BorshSchema, BorshSerialize};

pub mod de;
pub mod schema;
pub mod schema_helpers;
pub mod ser;
pub mod error;

pub use de::BorshDeserialize;
pub use schema::BorshSchema;
pub use schema_helpers::{try_from_slice_with_schema, try_to_vec_with_schema};
pub use ser::BorshSerialize;

/// A facade around all the types we need from the `std`, `core`, and `alloc`
/// crates. This avoids elaborate import wrangling having to happen in every
/// module.
pub mod lib {
    mod core {
        #[cfg(not(feature = "std"))]
        pub use core::*;
        #[cfg(feature = "std")]
        pub use std::*;
    }

    pub use self::core::{cmp, iter, mem, num, slice, str};
    pub use self::core::{f32, f64};
    pub use self::core::{i16, i32, i64, i8, isize};
    pub use self::core::{u16, u32, u64, u8, usize};

    pub use self::core::cell::{Cell, RefCell};
    pub use self::core::clone::{self, Clone};
    pub use self::core::convert::{self, From, Into};
    pub use self::core::default::{self, Default};
    pub use self::core::fmt::{self, Debug, Display};
    pub use self::core::marker::{self, PhantomData};
    pub use self::core::ops::Range;
    pub use self::core::option::{self, Option};
    pub use self::core::result::{self, Result};

    pub use alloc::borrow::{Cow, ToOwned};
    pub use alloc::string::{String, ToString};
    pub use alloc::vec::Vec;
    pub use alloc::boxed::Box;
    pub use alloc::rc::{Rc, Weak as RcWeak};
    pub use alloc::sync::{Arc, Weak as ArcWeak};
    pub use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};

    #[cfg(feature = "std")]
    pub use std::io::Write;
    #[cfg(not(feature = "std"))]
    pub use bare_io::Write;

    pub use alloc::{vec, format};

    pub use hashbrown::HashMap;

    pub mod hash_map {
        pub use hashbrown::hash_map::Entry;
    }
}
