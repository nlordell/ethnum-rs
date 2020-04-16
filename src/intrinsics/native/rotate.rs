//! This module implements right and left rotation (**not** shifting) intrinsics
//! for 256-bit integers.

use crate::U256;
use core::mem::MaybeUninit;

#[inline]
pub fn rotate_left(r: &mut MaybeUninit<U256>, a: &U256, b: u32) {
    unsafe {
        r.as_mut_ptr()
            .write((a << (b & 0xff)) | (a >> ((256 - b) & 0xff)))
    };
}

#[inline]
pub fn rotate_right(r: &mut MaybeUninit<U256>, a: &U256, b: u32) {
    unsafe {
        r.as_mut_ptr()
            .write((a >> (b & 0xff)) | (a << ((256 - b) & 0xff)))
    };
}
