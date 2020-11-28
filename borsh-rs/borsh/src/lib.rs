#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

pub use borsh_derive::{BorshDeserialize, BorshSchema, BorshSerialize};

pub mod de;
pub mod schema;
pub mod schema_helpers;
pub mod ser;


pub use de::BorshDeserialize;
pub use schema::BorshSchema;
pub use schema_helpers::{try_from_slice_with_schema, try_to_vec_with_schema};
pub use ser::BorshSerialize;

/// A facade around all the types we need from the `std`, `core`, and `alloc`
/// crates. This avoids elaborate import wrangling having to happen in every
/// module.
#[cfg(feature = "std")]
pub mod maybestd {
    pub use std::{
        borrow, string, vec, format, boxed, rc, sync, collections, io
    };
}

#[cfg(not(feature = "std"))]
mod nostd_io;

#[cfg(not(feature = "std"))]
pub mod maybestd {
    pub use alloc::{
        borrow, string, vec, format, boxed, rc, sync, 
    };

    pub mod collections {
        pub use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
        pub use hashbrown::*;
    }

    pub mod io {
        pub use super::super::nostd_io::*;
    }
    
    pub use hashbrown::{HashMap, HashSet};

    pub mod hash_map {
        pub use hashbrown::hash_map::Entry;
    }
}
