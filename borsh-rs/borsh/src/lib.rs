#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub use borsh_derive::{BorshDeserialize, BorshSchema, BorshSerialize};

mod custom_std;
pub mod de;
pub mod schema;
pub mod schema_helpers;
pub mod ser;
// pub mod error;

pub use de::BorshDeserialize;
pub use schema::BorshSchema;
pub use schema_helpers::{try_from_slice_with_schema, try_to_vec_with_schema};
pub use ser::BorshSerialize;
