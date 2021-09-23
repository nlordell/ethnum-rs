//! This module contains a Rust port of the `__udivmodti4` compiler builtin that
//! is typically used for implementing 64-bit unsigned division on 32-bit
//! platforms.
//!
//! This port is adapted to use 128-bit high and low words in order to implement
//! 256-bit unsigned division.
//!
//! This source is ported from LLVM project from C:
//! https://github.com/llvm/llvm-project/blob/main/compiler-rt/lib/builtins/udivmodti4.c

use crate::U256;
use core::mem::MaybeUninit;

#[inline(always)]
fn udiv256_by_128_to_128(u1: u128, u0: u128, mut v: u128, r: &mut u128) -> u128 {
    const N_UDWORD_BITS: u32 = 128;
    const B: u128 = 1 << (N_UDWORD_BITS / 2); // Number base (128 bits)
    let (un1, un0): (u128, u128); // Norm. dividend LSD's
    let (vn1, vn0): (u128, u128); // Norm. divisor digits
    let (mut q1, mut q0): (u128, u128); // Quotient digits
    let (un128, un21, un10): (u128, u128, u128); // Dividend digit pairs
    let mut rhat: u128; // A remainder
    let s: u32; // Shift amount for normalization

    s = v.leading_zeros();
    if s > 0 {
        // Normalize the divisor.
        v <<= s;
        un128 = (u1 << s) | (u0 >> (N_UDWORD_BITS - s));
        un10 = u0 << s; // Shift dividend left
    } else {
        // Avoid undefined behavior of (u0 >> 64).
        un128 = u1;
        un10 = u0;
    }

    // Break divisor up into two 64-bit digits.
    vn1 = v >> (N_UDWORD_BITS / 2);
    vn0 = v & 0xFFFF_FFFF_FFFF_FFFF;

    // Break right half of dividend into two digits.
    un1 = un10 >> (N_UDWORD_BITS / 2);
    un0 = un10 & 0xFFFF_FFFF_FFFF_FFFF;

    // Compute the first quotient digit, q1.
    q1 = un128 / vn1;
    rhat = un128 - q1 * vn1;

    // q1 has at most error 2. No more than 2 iterations.
    while q1 >= B || q1 * vn0 > B * rhat + un1 {
        q1 -= 1;
        rhat += vn1;
        if rhat >= B {
            break;
        }
    }

    un21 = un128
        .wrapping_mul(B)
        .wrapping_add(un1)
        .wrapping_sub(q1.wrapping_mul(v));

    // Compute the second quotient digit.
    q0 = un21 / vn1;
    rhat = un21 - q0 * vn1;

    // q0 has at most error 2. No more than 2 iterations.
    while q0 >= B || q0 * vn0 > B * rhat + un0 {
        q0 -= 1;
        rhat += vn1;
        if rhat >= B {
            break;
        }
    }

    *r = (un21
        .wrapping_mul(B)
        .wrapping_add(un0)
        .wrapping_sub(q0.wrapping_mul(v)))
        >> s;
    q1 * B + q0
}

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

    // In the LLVM version on the x86_64 platform, `udiv256_by_128_to_128` would
    // defer to `divq` instruction, which divides a 128-bit value by a 64-bit
    // one returning a 64-bit value, making it very performant when dividing
    // small values:
    // ```
    //   du_int result;
    //   __asm__("divq %[v]"
    //           : "=a"(result), "=d"(*r)
    //           : [ v ] "r"(v), "a"(u0), "d"(u1));
    //   return result;
    // ```
    // Unfortunately, there is no 256-bit equivalent on x86_64, but we can still
    // shortcut if the high and low values of the operands are 0:
    if a.high() | b.high() == 0 {
        if let Some(rem) = rem {
            set!(rem = U256::from_words(0, a.low() % b.low()));
        }
        set!(res = U256::from_words(0, a.low() / b.low()));
        return;
    }

    const N_UDWORD_BITS: u32 = 128;

    let mut dividend = *a;
    let mut divisor = *b;
    let mut quotient: U256;
    let mut remainder: U256;

    if divisor > dividend {
        if let Some(rem) = rem {
            set!(rem = dividend);
        }
        set!(res = U256::ZERO);
        return;
    }
    // When the divisor fits in 128 bits, we can use an optimized path.
    if *divisor.high() == 0 {
        remainder = U256::ZERO;
        if dividend.high() < divisor.low() {
            // The result fits in 128 bits.
            quotient = U256::from_words(
                0,
                udiv256_by_128_to_128(
                    *dividend.high(),
                    *dividend.low(),
                    *divisor.low(),
                    remainder.low_mut(),
                ),
            );
        } else {
            // First, divide with the high part to get the remainder in dividend.s.high.
            // After that dividend.s.high < divisor.s.low.
            quotient = U256::from_words(
                dividend.high() / divisor.low(),
                udiv256_by_128_to_128(
                    dividend.high() % divisor.low(),
                    *dividend.low(),
                    *divisor.low(),
                    remainder.low_mut(),
                ),
            );
        }
        if let Some(rem) = rem {
            set!(rem = remainder);
        }
        set!(res = quotient);
        return;
    }

    // 0 <= shift <= 127.
    let shift = divisor.high().leading_zeros() - dividend.high().leading_zeros();

    divisor <<= shift;
    quotient = U256::ZERO;
    for _ in 0..=shift {
        *quotient.low_mut() <<= 1;
        // Branch free version of.
        // if (dividend.all >= divisor.all)
        // {
        //    dividend.all -= divisor.all;
        //    carry = 1;
        // }
        let s = ((*divisor
            .wrapping_sub(dividend)
            .wrapping_sub(U256::ONE)
            .high() as i128)
            >> (N_UDWORD_BITS - 1)) as u128;
        *quotient.low_mut() |= s & 1;
        dividend -= divisor & U256::from_words(s, s);
        divisor >>= 1;
    }
    if let Some(rem) = rem {
        set!(rem = dividend);
    }
    set!(res = quotient);
}

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
