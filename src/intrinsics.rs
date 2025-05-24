//! This module contains intrinsics used by the [`I256`](struct@crate::I256) and
//! [`U256`](struct@crate::U256) implementations.
//!
//! # Stability
//!
//! Be careful when using these intrinsics directly. Semantic versioning API
//! compatibility is **not guaranteed** for any of these intrinsics.

#![allow(missing_docs)]

#[macro_use]
mod cast;

pub mod signed;

#[allow(clippy::module_inception)]
#[cfg(feature = "intrinsics")]
mod intrinsics;
#[cfg(feature = "intrinsics")]
pub use self::intrinsics::*;

#[cfg(not(feature = "intrinsics"))]
mod native;
#[cfg(not(feature = "intrinsics"))]
pub use self::native::*;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::uint::U256;
    use core::mem::MaybeUninit;

    #[test]
    fn unchecked_addition() {
        let mut res = MaybeUninit::uninit();
        add3(&mut res, &U256([1, 2]), &U256([3, 0]));
        assert_eq!(unsafe { res.assume_init() }, U256([4, 2]));
    }
}
