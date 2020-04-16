//! This module contains intrinsics used by the [`U256`] implementation.
//!
//! [`U256`]: struct.U256.html

#![allow(missing_docs)]

#[cfg(feature = "llvm-intrinsics")]
mod llvm;
#[cfg(not(feature = "llvm-intrinsics"))]
mod native;

#[cfg(feature = "llvm-intrinsics")]
pub use self::llvm::*;
#[cfg(not(feature = "llvm-intrinsics"))]
pub use self::native::*;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::U256;
    use core::mem::MaybeUninit;

    #[test]
    fn unchecked_addition() {
        let mut res = MaybeUninit::uninit();
        add3(&mut res, &U256([1, 2]), &U256([3, 0]));
        assert_eq!(unsafe { res.assume_init() }, U256([4, 2]));
    }
}
