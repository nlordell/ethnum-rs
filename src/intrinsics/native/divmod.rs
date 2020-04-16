//! This module contains a Rust port of the `__udivmodti4` compiler builtin that
//! is typically used for implementing 64-bit unsigned division on 32-bit
//! platforms.
//!
//! This port is adapted to use 128-bit high and low words in order to implement
//! 256-bit unsigned division.
//!
//! This source is ported from LLVM project from C:
//! https://github.com/llvm/llvm-project/blob/master/compiler-rt/lib/builtins/udivmodti4.c

use crate::{AsU256, U256};
use core::mem::MaybeUninit;

#[allow(clippy::many_single_char_names)]
pub fn udivmod4(
    res: &mut MaybeUninit<U256>,
    a: &U256,
    b: &U256,
    rem: Option<&mut MaybeUninit<U256>>,
) {
    macro_rules! set {
        ($x:ident = $value:expr) => {
            unsafe { $x.as_mut_ptr().write($value) }
        };
    }

    const N_UDWORD_BITS: u32 = 128;
    const N_UTWORD_BITS: u32 = 256;
    let n = a;
    let d = b;
    let mut q = MaybeUninit::<U256>::uninit();
    let mut r = MaybeUninit::<U256>::uninit();
    let mut sr: u32;
    // special cases, X is unknown, K != 0
    if *n.high() == 0 {
        if *d.high() == 0 {
            // 0 X
            // ---
            // 0 X
            if let Some(rem) = rem {
                set!(rem = U256::new(n.low() % d.low()));
            }
            set!(res = U256::new(n.low() / d.low()));
            return;
        }
        // 0 X
        // ---
        // K X
        if let Some(rem) = rem {
            set!(rem = U256::new(*n.low()));
        }
        set!(res = U256::ZERO);
        return;
    }
    // n.high() != 0
    if *d.low() == 0 {
        if *d.high() == 0 {
            // K X
            // ---
            // 0 0
            if let Some(rem) = rem {
                set!(rem = U256::new(n.high() % d.low()));
            }
            set!(res = U256::new(n.high() / d.low()));
            return;
        }
        // d.high() != 0
        if *n.low() == 0 {
            // K 0
            // ---
            // K 0
            if let Some(rem) = rem {
                set!(rem = U256::from_words(n.high() % d.high(), 0));
            }
            set!(res = U256::new(n.high() / d.high()));
            return;
        }
        // K K
        // ---
        // K 0
        // NOTE: Modified from `if (d.high() & (d.high() - 1)) == 0`
        if d.high().is_power_of_two() {
            /* if d is a power of 2 */
            if let Some(rem) = rem {
                set!(rem = U256::from_words(n.high() & (d.high() - 1), *n.low()));
            }
            set!(res = U256::new(n.high() >> d.high().trailing_zeros()));
            return;
        }
        // K K
        // ---
        // K 0
        sr = d
            .high()
            .leading_zeros()
            .wrapping_sub(n.high().leading_zeros());
        // 0 <= sr <= N_UDWORD_BITS - 2 or sr large
        if sr > N_UDWORD_BITS - 2 {
            if let Some(rem) = rem {
                set!(rem = *n);
            }
            set!(res = U256::ZERO);
            return;
        }
        sr += 1;
        // 1 <= sr <= N_UDWORD_BITS - 1
        // q.all = n.all << (N_UTWORD_BITS - sr);
        set!(q = U256::from_words(n.low() << (N_UDWORD_BITS - sr), 0));
        // r.all = n.all >> sr;
        set!(
            r = U256::from_words(
                n.high() >> sr,
                (n.high() << (N_UDWORD_BITS - sr)) | (n.low() >> sr),
            )
        );
    } else {
        /* d.low() != 0 */
        if *d.high() == 0 {
            // K X
            // ---
            // 0 K
            // NOTE: Modified from `if (d.low() & (d.low() - 1)) == 0`.
            if d.low().is_power_of_two() {
                /* if d is a power of 2 */
                if let Some(rem) = rem {
                    set!(rem = U256::new(n.low() & (d.low() - 1)));
                }
                if *d.low() == 1 {
                    set!(res = *n);
                    return;
                }
                sr = d.low().trailing_zeros();
                set!(
                    res = U256::from_words(
                        n.high() >> sr,
                        (n.high() << (N_UDWORD_BITS - sr)) | (n.low() >> sr),
                    )
                );
                return;
            }
            // K X
            // ---
            // 0 K
            sr = 1 + N_UDWORD_BITS + d.low().leading_zeros() - (n.high()).leading_zeros();
            // 2 <= sr <= N_UTWORD_BITS - 1
            // q.all = n.all << (N_UTWORD_BITS - sr);
            // r.all = n.all >> sr;
            #[allow(clippy::comparison_chain)]
            if sr == N_UDWORD_BITS {
                set!(q = U256::from_words(*n.low(), 0));
                set!(r = U256::from_words(0, *n.high()));
            } else if sr < N_UDWORD_BITS {
                /* 2 <= sr <= N_UDWORD_BITS - 1 */
                set!(q = U256::from_words(n.low() << (N_UDWORD_BITS - sr), 0));
                set!(
                    r = U256::from_words(
                        n.high() >> sr,
                        (n.high() << (N_UDWORD_BITS - sr)) | (n.low() >> sr),
                    )
                );
            } else {
                /* N_UDWORD_BITS + 1 <= sr <= N_UTWORD_BITS - 1 */
                set!(
                    q = U256::from_words(
                        (n.high() << (N_UTWORD_BITS - sr)) | (n.low() >> (sr - N_UDWORD_BITS)),
                        n.low() << (N_UTWORD_BITS - sr),
                    )
                );
                set!(r = U256::from_words(0, n.high() >> (sr - N_UDWORD_BITS)));
            }
        } else {
            // K X
            // ---
            // K K
            sr = (d.high())
                .leading_zeros()
                .wrapping_sub((n.high()).leading_zeros());
            // 0 <= sr <= N_UDWORD_BITS - 1 or sr large
            if sr > N_UDWORD_BITS - 1 {
                if let Some(rem) = rem {
                    set!(rem = *n);
                }
                set!(res = U256::ZERO);
                return;
            }
            sr += 1;
            // 1 <= sr <= N_UDWORD_BITS
            // q.all = n.all << (N_UTWORD_BITS - sr);
            // r.all = n.all >> sr;
            if sr == N_UDWORD_BITS {
                set!(q = U256::from_words(*n.low(), 0));
                set!(r = U256::from_words(0, *n.high()));
            } else {
                set!(
                    r = U256::from_words(
                        n.high() >> sr,
                        (n.high() << (N_UDWORD_BITS - sr)) | (n.low() >> sr),
                    )
                );
                set!(q = U256::from_words(n.low() << (N_UDWORD_BITS - sr), 0));
            }
        }
    }
    // Not a special case
    // q and r are initialized with:
    // q.all = n.all << (N_UTWORD_BITS - sr);
    // r.all = n.all >> sr;
    // 1 <= sr <= N_UTWORD_BITS - 1
    let mut carry = 0u128;
    let mut q = unsafe { q.assume_init() };
    let mut r = unsafe { r.assume_init() };
    while sr > 0 {
        // r:q = ((r:q)  << 1) | carry
        *r.high_mut() = (r.high() << 1) | (r.low() >> (N_UDWORD_BITS - 1));
        *r.low_mut() = (r.low() << 1) | (q.high() >> (N_UDWORD_BITS - 1));
        *q.high_mut() = (q.high() << 1) | (q.low() >> (N_UDWORD_BITS - 1));
        *q.low_mut() = (q.low() << 1) | carry;
        // carry = 0;
        // if (r.all >= d.all)
        // {
        //     r.all -= d.all;
        //      carry = 1;
        // }
        // NOTE: Modified from `(d - r - 1) >> (N_UTWORD_BITS - 1)` to be an
        // **arithmetic** shift.
        let s = {
            let (hi, _) = d.wrapping_sub(r).wrapping_sub(U256::ONE).into_words();
            ((hi as i128) >> 127).as_u256()
        };
        carry = s.low() & 1;
        r -= d & s;

        sr -= 1;
    }
    q = (q << 1) | U256::new(carry);
    if let Some(rem) = rem {
        set!(rem = r);
    }
    set!(res = q);
}

pub fn div2(r: &mut U256, a: &U256) {
    let (a, b) = (*r, a);
    // SAFETY: `udivmod4` does not write `MaybeUninit::uninit()` to `res` and
    // `U256` does not implement `Drop`.
    let res = unsafe { &mut *(r as *mut U256).cast() };
    udivmod4(res, &a, b, None);
}

pub fn div3(r: &mut MaybeUninit<U256>, a: &U256, b: &U256) {
    udivmod4(r, a, b, None);
}

pub fn rem2(r: &mut U256, a: &U256) {
    let mut res = MaybeUninit::uninit();
    let (a, b) = (*r, a);
    // SAFETY: `udivmod4` does not write `MaybeUninit::uninit()` to `rem` and
    // `U256` does not implement `Drop`.
    let r = unsafe { &mut *(r as *mut U256).cast() };
    udivmod4(&mut res, &a, b, Some(r));
}

pub fn rem3(r: &mut MaybeUninit<U256>, a: &U256, b: &U256) {
    let mut res = MaybeUninit::uninit();
    udivmod4(&mut res, &a, b, Some(r));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn div(a: impl AsU256, b: impl AsU256) -> U256 {
        let mut r = MaybeUninit::uninit();
        div3(&mut r, &a.as_u256(), &b.as_u256());
        unsafe { r.assume_init() }
    }

    fn rem(a: impl AsU256, b: impl AsU256) -> U256 {
        let mut r = MaybeUninit::uninit();
        rem3(&mut r, &a.as_u256(), &b.as_u256());
        unsafe { r.assume_init() }
    }

    #[test]
    fn division() {
        // 0 X
        // ---
        // 0 X
        assert_eq!(div(100, 9), 11);

        // 0 X
        // ---
        // K X
        assert_eq!(div(!0u128, U256::ONE << 128u32), 0);

        // K 0
        // ---
        // K 0
        assert_eq!(div(U256::from_words(100, 0), U256::from_words(10, 0)), 10);

        // K K
        // ---
        // K 0
        assert_eq!(div(U256::from_words(100, 1337), U256::ONE << 130u32), 25);
        assert_eq!(div(U256::from_words(1337, !0), U256::from_words(63, 0)), 21);

        // K X
        // ---
        // 0 K
        assert_eq!(
            div(U256::from_words(42, 0), U256::ONE),
            U256::from_words(42, 0),
        );
        assert_eq!(
            div(U256::from_words(42, 42), U256::ONE << 42),
            42u128 << (128 - 42),
        );
        assert_eq!(
            div(U256::from_words(1337, !0), 0xc0ffee),
            35996389033280467545299711090127855,
        );
        assert_eq!(
            div(U256::from_words(42, 0), 99),
            144362216269489045105674075880144089708,
        );

        // K X
        // ---
        // K K
        assert_eq!(
            div(U256::from_words(100, 100), U256::from_words(1000, 1000)),
            0,
        );
        assert_eq!(
            div(U256::from_words(1337, !0), U256::from_words(43, !0)),
            30,
        );
    }

    #[test]
    #[should_panic]
    fn division_by_zero() {
        div(1, 0);
    }

    #[test]
    fn remainder() {
        // 0 X
        // ---
        // 0 X
        assert_eq!(rem(100, 9), 1);

        // 0 X
        // ---
        // K X
        assert_eq!(rem(!0u128, U256::ONE << 128u32), !0u128);

        // K 0
        // ---
        // K 0
        assert_eq!(rem(U256::from_words(100, 0), U256::from_words(10, 0)), 0);

        // K K
        // ---
        // K 0
        assert_eq!(rem(U256::from_words(100, 1337), U256::ONE << 130u32), 1337);
        assert_eq!(
            rem(U256::from_words(1337, !0), U256::from_words(63, 0)),
            U256::from_words(14, !0),
        );

        // K X
        // ---
        // 0 K
        assert_eq!(rem(U256::from_words(42, 0), U256::ONE), 0);
        assert_eq!(rem(U256::from_words(42, 42), U256::ONE << 42), 42);
        assert_eq!(rem(U256::from_words(1337, !0), 0xc0ffee), 1910477);
        assert_eq!(rem(U256::from_words(42, 0), 99), 60);

        // K X
        // ---
        // K K
        assert_eq!(
            rem(U256::from_words(100, 100), U256::from_words(1000, 1000)),
            U256::from_words(100, 100),
        );
        assert_eq!(
            rem(U256::from_words(1337, !0), U256::from_words(43, !0)),
            U256::from_words(18, 29),
        );
    }

    #[test]
    #[should_panic]
    fn remainder_by_zero() {
        rem(1, 0);
    }
}
