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
#[cfg(not(feature = "std"))]
mod write;

pub use de::BorshDeserialize;
pub use schema::BorshSchema;
pub use schema_helpers::{try_from_slice_with_schema, try_to_vec_with_schema};
pub use ser::BorshSerialize;

/// A facade around all the types we need from the `std`, `core`, and `alloc`
/// crates. This avoids elaborate import wrangling having to happen in every
/// module.
#[cfg(feature = "std")]
pub mod lib {
    pub use std::{cmp, iter, mem, num, slice, str};
    pub use std::{f32, f64};
    pub use std::{i16, i32, i64, i8, isize};
    pub use std::{u16, u32, u64, u8, usize};

    pub use std::cell::{Cell, RefCell};
    pub use std::clone::{self, Clone};
    pub use std::convert::{self, From, Into};
    pub use std::default::{self, Default};
    pub use std::fmt::{self, Debug, Display};
    pub use std::marker::{self, PhantomData};
    pub use std::ops::Range;
    pub use std::option::{self, Option};
    pub use std::result::{self, Result};

    pub use std::borrow::{Cow, ToOwned};
    pub use std::string::{String, ToString};
    pub use std::vec::Vec;
    pub use std::boxed::Box;
    pub use std::rc::{Rc, Weak as RcWeak};
    pub use std::sync::{Arc, Weak as ArcWeak};
    pub use std::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
    pub use std::io::Write;

    pub use std::{vec, format};
    pub use std::collections::{HashMap, HashSet};
    pub mod hash_map {
        pub use std::collections::hash_map::Entry;
    }
}


#[cfg(not(feature = "std"))]
pub mod lib {
    pub use core::{cmp, iter, mem, num, slice, str};
    pub use core::{f32, f64};
    pub use core::{i16, i32, i64, i8, isize};
    pub use core::{u16, u32, u64, u8, usize};

    pub use core::cell::{Cell, RefCell};
    pub use core::clone::{self, Clone};
    pub use core::convert::{self, From, Into};
    pub use core::default::{self, Default};
    pub use core::fmt::{self, Debug, Display};
    pub use core::marker::{self, PhantomData};
    pub use core::ops::Range;
    pub use core::option::{self, Option};
    pub use core::result::{self, Result};

    pub use alloc::borrow::{Cow, ToOwned};
    pub use alloc::string::{String, ToString};
    pub use alloc::vec::Vec;
    pub use alloc::boxed::Box;
    pub use alloc::rc::{Rc, Weak as RcWeak};
    pub use alloc::sync::{Arc, Weak as ArcWeak};
    pub use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};

    pub use crate::write::Write;
    pub use alloc::{vec, format};
    pub use hashbrown::{HashMap, HashSet};

    pub mod hash_map {
        pub use hashbrown::hash_map::Entry;
    }
}
