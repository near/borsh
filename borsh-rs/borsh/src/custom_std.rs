// Based on https://github.com/serde-rs/serde/blob/e3d871ff7bf10dadf10bdc234a55692228358d0e/serde/src/lib.rs#L150
// TODO: Remove unused
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
pub use self::core::convert::{self, From, Into, TryFrom};
pub use self::core::default::{self, Default};
pub use self::core::fmt::{self, Debug, Display};
pub use self::core::marker::{self, PhantomData};
pub use self::core::ops::Range;
pub use self::core::option::{self, Option};
pub use self::core::result::{self, Result};

#[cfg(all(feature = "alloc", not(feature = "std")))]
pub use alloc::borrow;
#[cfg(feature = "std")]
pub use std::borrow;

#[cfg(all(feature = "alloc", not(feature = "std")))]
pub use alloc::string::{String, ToString};
#[cfg(feature = "std")]
pub use std::string::{String, ToString};

#[cfg(all(feature = "alloc", not(feature = "std")))]
pub use alloc::vec::Vec;
#[cfg(feature = "std")]
pub use std::vec::Vec;

#[cfg(all(feature = "alloc", not(feature = "std")))]
pub use alloc::boxed::Box;
#[cfg(feature = "std")]
pub use std::boxed::Box;

#[cfg(all(feature = "rc", feature = "alloc", not(feature = "std")))]
pub use alloc::rc::{Rc, Weak as RcWeak};
#[cfg(all(feature = "rc", feature = "std"))]
pub use std::rc::{Rc, Weak as RcWeak};

#[cfg(all(feature = "rc", feature = "alloc", not(feature = "std")))]
pub use alloc::sync::{Arc, Weak as ArcWeak};
#[cfg(all(feature = "rc", feature = "std"))]
pub use std::sync::{Arc, Weak as ArcWeak};

#[cfg(feature = "std")]
pub use std::{error, net};

pub mod collections {
    #[cfg(feature = "std")]
    pub use std::collections::{HashMap, HashSet, BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque, hash_map};

    #[cfg(all(feature = "alloc", not(feature = "std")))]
    pub use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};

    #[cfg(all(feature = "std", collections_bound))]
    pub use std::collections::Bound;
}

#[cfg(feature = "std")]
pub use std::ffi::{CStr, CString, OsStr, OsString};
#[cfg(feature = "std")]
pub use std::hash::{BuildHasher, Hash};
#[cfg(feature = "std")]
pub use std::io;
#[cfg(not(feature = "std"))]
pub use bare_io as io;
#[cfg(feature = "std")]
pub use std::num::Wrapping;
#[cfg(feature = "std")]
pub use std::path::{Path, PathBuf};
#[cfg(feature = "std")]
pub use std::sync::{Mutex, RwLock};
#[cfg(feature = "std")]
pub use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(core_reverse)]
pub use self::core::cmp::Reverse;

#[cfg(ops_bound)]
pub use self::core::ops::Bound;

#[cfg(range_inclusive)]
pub use self::core::ops::RangeInclusive;

#[cfg(all(feature = "std", std_atomic))]
pub use std::sync::atomic::{
    AtomicBool, AtomicI16, AtomicI32, AtomicI8, AtomicIsize, AtomicU16, AtomicU32, AtomicU8,
    AtomicUsize, Ordering,
};
#[cfg(all(feature = "std", std_atomic64))]
pub use std::sync::atomic::{AtomicI64, AtomicU64};

#[cfg(any(core_duration, feature = "std"))]
pub use self::core::time::Duration;
