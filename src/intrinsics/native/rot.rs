//! This module implements right and left rotation (**not** shifting) intrinsics
//! for 256-bit integers.

use crate::uint::U256;
use core::mem::{transmute, MaybeUninit};

#[inline]
#[allow(clippy::collapsible_else_if)]
pub fn rol3(r: &mut MaybeUninit<U256>, a: &U256, b: u32) {
    let arr = unsafe { transmute::<U256, [u64; 4]>(*a) };
    let mut arr_2 = arr;
    let mask = (-((b & 63) as i64) >> 63) as u64;
    for i in 0..4 {
        #[cfg(target_endian = "little")]
        {
            arr_2[i] = ((arr[(i + 3) & 3] >> (64 - (b & 63))) & mask) | arr[i].wrapping_shl(b);
        }
        #[cfg(target_endian = "big")]
        {
            arr_2[i] = ((arr[(i + 1) & 3] >> (64 - (b & 63))) & mask) | arr[i].wrapping_shl(b);
        }
    }
    if b & 128 != 0 {
        if b & 64 != 0 {
            r.write(unsafe {
                transmute::<[u64; 4], U256>([arr_2[1], arr_2[2], arr_2[3], arr_2[0]])
            });
        } else {
            r.write(unsafe {
                transmute::<[u64; 4], U256>([arr_2[2], arr_2[3], arr_2[0], arr_2[1]])
            });
        }
    } else {
        if b & 64 != 0 {
            r.write(unsafe {
                transmute::<[u64; 4], U256>([arr_2[3], arr_2[0], arr_2[1], arr_2[2]])
            });
        } else {
            r.write(unsafe { transmute::<[u64; 4], U256>(arr_2) });
        }
    }
}

#[inline]
pub fn ror3(r: &mut MaybeUninit<U256>, a: &U256, b: u32) {
    rol3(r, a, 0u32.wrapping_sub(b) & 255)
}
