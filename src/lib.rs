//! This crate implements a 256-bit unsigned integer type.
//!
//! The implementation tries to follow as closely as possible to primitive
//! integer types, and should implement all the common methods and traits as the
//! primitive integer types.

#![deny(missing_docs)]
#![no_std]

#[cfg(test)]
extern crate alloc;

#[macro_use]
mod macros {
    #[macro_use]
    pub mod cmp;
    #[macro_use]
    pub mod fmt;
    #[macro_use]
    pub mod ops;
    #[macro_use]
    pub mod iter;
}

mod error;
mod fmt;
mod int;
pub mod intrinsics;
mod uint;

/// Convenience re-export of 256-integer types and as- conversion traits.
pub mod prelude {
    pub use crate::int::{AsI256, I256};
    pub use crate::uint::{AsU256, U256};
}

pub use self::prelude::*;

/// A 256-bit signed integer type.
#[allow(non_camel_case_types)]
pub type i256 = I256;

/// A 256-bit unsigned integer type.
#[allow(non_camel_case_types)]
pub type u256 = U256;
