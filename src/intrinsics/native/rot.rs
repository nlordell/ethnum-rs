//! This module implements right and left rotation (**not** shifting) intrinsics
//! for 256-bit integers.

use crate::uint::U256;
use core::mem::MaybeUninit;

#[inline]
pub fn rol3(r: &mut MaybeUninit<U256>, a: &U256, b: u32) {
    let lmask = u64::MAX.wrapping_shl(b);
    let rmask = !lmask;
    let mut arr = unsafe { core::mem::transmute::<U256, [u64; 4]>(*a) };
    let mut arr_2 = [0u64; 4];
    for i in 0..4 {
        arr[i] = arr[i].rotate_left(b);
        arr_2[i] = arr[i] & rmask;
        arr[i] &= lmask;
    }
    for i in 0..4 {
        #[cfg(target_endian = "little")]
        {
            arr[i] |= arr_2[(i + 3) & 3];
        }
        #[cfg(target_endian = "big")]
        {
            arr[i] |= arr_2[(i + 1) & 3];
        }
    }
    if b & 128 != 0 {
        if b & 64 != 0 {
            r.write(unsafe { core::mem::transmute::<[u64; 4], U256>(
                [arr[1], arr[2], arr[3], arr[0]]
            ) });
        } else {
            r.write(unsafe { core::mem::transmute::<[u64; 4], U256>(
                [arr[2], arr[3], arr[0], arr[1]]
            ) });
        }
    } else {
        if b & 64 != 0 {
            r.write(unsafe { core::mem::transmute::<[u64; 4], U256>(
                [arr[3], arr[0], arr[1], arr[2]]
            ) });
        } else {
            r.write(unsafe { core::mem::transmute::<[u64; 4], U256>(arr) });
        }
    }
}

// Perhaps this function should get its own code.
#[inline]
pub fn ror3(r: &mut MaybeUninit<U256>, a: &U256, b: u32) {
    rol3(r, a, 0u32.wrapping_sub(b) & 255)
}
