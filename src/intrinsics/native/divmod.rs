//! This module contains a Rust port of the `__u?divmodti4` compiler builtins
//! that are typically used for implementing 64-bit signed and unsigned division
//! on 32-bit platforms.
//!
//! This port is adapted to use 128-bit high and low words in order to implement
//! 256-bit division.
//!
//! This source is ported from LLVM project from C:
//! - signed division: <https://github.com/llvm/llvm-project/blob/main/compiler-rt/lib/builtins/divmodti4.c>
//! - unsigned division: <https://github.com/llvm/llvm-project/blob/main/compiler-rt/lib/builtins/udivmodti4.c>

use super::{idivmod4, udivmod4};
use crate::{int::I256, uint::U256};
use core::mem::MaybeUninit;

#[inline]
pub fn udiv2(r: &mut U256, a: &U256) {
    let (a, b) = (*r, a);
    // SAFETY: `udivmod4` does not write `MaybeUninit::uninit()` to `res` and
    // `U256` does not implement `Drop`.
    let res = unsafe { &mut *(r as *mut U256).cast() };
    udivmod4(res, &a, b, None);
}

#[inline]
pub fn udiv3(r: &mut MaybeUninit<U256>, a: &U256, b: &U256) {
    udivmod4(r, a, b, None);
}

#[inline]
pub fn urem2(r: &mut U256, a: &U256) {
    let mut res = MaybeUninit::uninit();
    let (a, b) = (*r, a);
    // SAFETY: `udivmod4` does not write `MaybeUninit::uninit()` to `rem` and
    // `U256` does not implement `Drop`.
    let r = unsafe { &mut *(r as *mut U256).cast() };
    udivmod4(&mut res, &a, b, Some(r));
}

#[inline]
pub fn urem3(r: &mut MaybeUninit<U256>, a: &U256, b: &U256) {
    let mut res = MaybeUninit::uninit();
    udivmod4(&mut res, a, b, Some(r));
}

#[inline]
pub fn idiv2(r: &mut I256, a: &I256) {
    let (a, b) = (*r, a);
    // SAFETY: `udivmod4` does not write `MaybeUninit::uninit()` to `res` and
    // `U256` does not implement `Drop`.
    let res = unsafe { &mut *(r as *mut I256).cast() };
    idivmod4(res, &a, b, None);
}

#[inline]
pub fn idiv3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) {
    idivmod4(r, a, b, None);
}

#[inline]
pub fn irem2(r: &mut I256, a: &I256) {
    let mut res = MaybeUninit::uninit();
    let (a, b) = (*r, a);
    // SAFETY: `udivmod4` does not write `MaybeUninit::uninit()` to `rem` and
    // `U256` does not implement `Drop`.
    let r = unsafe { &mut *(r as *mut I256).cast() };
    idivmod4(&mut res, &a, b, Some(r));
}

#[inline]
pub fn irem3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) {
    let mut res = MaybeUninit::uninit();
    idivmod4(&mut res, a, b, Some(r));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AsU256;

    fn udiv(a: impl AsU256, b: impl AsU256) -> U256 {
        let mut r = MaybeUninit::uninit();
        udiv3(&mut r, &a.as_u256(), &b.as_u256());
        unsafe { r.assume_init() }
    }

    fn urem(a: impl AsU256, b: impl AsU256) -> U256 {
        let mut r = MaybeUninit::uninit();
        urem3(&mut r, &a.as_u256(), &b.as_u256());
        unsafe { r.assume_init() }
    }

    #[test]
    fn division() {
        // 0 X
        // ---
        // 0 X
        assert_eq!(udiv(100, 9), 11);

        // 0 X
        // ---
        // K X
        assert_eq!(udiv(!0u128, U256::ONE << 128u32), 0);

        // K 0
        // ---
        // K 0
        assert_eq!(udiv(U256::from_words(100, 0), U256::from_words(10, 0)), 10);

        // K K
        // ---
        // K 0
        assert_eq!(udiv(U256::from_words(100, 1337), U256::ONE << 130u32), 25);
        assert_eq!(
            udiv(U256::from_words(1337, !0), U256::from_words(63, 0)),
            21
        );

        // K X
        // ---
        // 0 K
        assert_eq!(
            udiv(U256::from_words(42, 0), U256::ONE),
            U256::from_words(42, 0),
        );
        assert_eq!(
            udiv(U256::from_words(42, 42), U256::ONE << 42),
            42u128 << (128 - 42),
        );
        assert_eq!(
            udiv(U256::from_words(1337, !0), 0xc0ffee),
            35996389033280467545299711090127855,
        );
        assert_eq!(
            udiv(U256::from_words(42, 0), 99),
            144362216269489045105674075880144089708,
        );

        // K X
        // ---
        // K K
        assert_eq!(
            udiv(U256::from_words(100, 100), U256::from_words(1000, 1000)),
            0,
        );
        assert_eq!(
            udiv(U256::from_words(1337, !0), U256::from_words(43, !0)),
            30,
        );
    }

    #[test]
    #[should_panic]
    fn division_by_zero() {
        udiv(1, 0);
    }

    #[test]
    fn remainder() {
        // 0 X
        // ---
        // 0 X
        assert_eq!(urem(100, 9), 1);

        // 0 X
        // ---
        // K X
        assert_eq!(urem(!0u128, U256::ONE << 128u32), !0u128);

        // K 0
        // ---
        // K 0
        assert_eq!(urem(U256::from_words(100, 0), U256::from_words(10, 0)), 0);

        // K K
        // ---
        // K 0
        assert_eq!(urem(U256::from_words(100, 1337), U256::ONE << 130u32), 1337);
        assert_eq!(
            urem(U256::from_words(1337, !0), U256::from_words(63, 0)),
            U256::from_words(14, !0),
        );

        // K X
        // ---
        // 0 K
        assert_eq!(urem(U256::from_words(42, 0), U256::ONE), 0);
        assert_eq!(urem(U256::from_words(42, 42), U256::ONE << 42), 42);
        assert_eq!(urem(U256::from_words(1337, !0), 0xc0ffee), 1910477);
        assert_eq!(urem(U256::from_words(42, 0), 99), 60);

        // K X
        // ---
        // K K
        assert_eq!(
            urem(U256::from_words(100, 100), U256::from_words(1000, 1000)),
            U256::from_words(100, 100),
        );
        assert_eq!(
            urem(U256::from_words(1337, !0), U256::from_words(43, !0)),
            U256::from_words(18, 29),
        );
    }

    #[test]
    #[should_panic]
    fn remainder_by_zero() {
        urem(1, 0);
    }
}
