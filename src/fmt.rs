//! Module implementing formatting for `U256` type.
//!
//! Most of these implementations were ported from the Rust standard library's
//! implementation for primitive integer types:
//! https://doc.rust-lang.org/src/core/fmt/num.rs.html

use crate::{AsU256, U256};
use core::fmt;
use core::mem::{self, MaybeUninit};
use core::num::ParseIntError;
use core::ptr;
use core::slice;
use core::str::{self, FromStr};

/// Converts a string slice in a given base to an `U256`.
pub(crate) fn from_str_radix(src: &str, radix: u32) -> Result<U256, ParseIntError> {
    assert!(
        radix >= 2 && radix <= 36,
        "from_str_radix_int: must lie in the range `[2, 36]` - found {}",
        radix
    );

    if src.is_empty() {
        return Err(Pie::Empty.into());
    }

    let mut result = U256::ZERO;
    for &c in src.as_bytes() {
        let x = match (c as char).to_digit(radix) {
            Some(x) => x,
            None => return Err(Pie::InvalidDigit.into()),
        };
        result = match result.checked_mul(radix.as_u256()) {
            Some(result) => result,
            None => return Err(Pie::Overflow.into()),
        };
        result = match result.checked_add(x.as_u256()) {
            Some(result) => result,
            None => return Err(Pie::Overflow.into()),
        };
    }

    Ok(result)
}

/// Helper type for constructing `ParseIntError` since there is no public API
/// for doing so.
enum Pie {
    Empty,
    InvalidDigit,
    Overflow,
}

impl Into<ParseIntError> for Pie {
    #[inline]
    fn into(self) -> ParseIntError {
        unsafe { mem::transmute(self) }
    }
}

impl FromStr for U256 {
    type Err = ParseIntError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_radix(s, 10)
    }
}

impl fmt::Debug for U256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // NOTE: Work around `Formatter::debug_{lower,upper}_hex` being private
        // and not stabilized.
        const DEBUG_LOWER_HEX: u32 = 1 << 4;
        const DEBUG_UPPER_HEX: u32 = 1 << 5;

        #[allow(deprecated)]
        let flags = f.flags();

        if flags & DEBUG_LOWER_HEX != 0 {
            fmt::LowerHex::fmt(self, f)
        } else if flags & DEBUG_UPPER_HEX != 0 {
            fmt::UpperHex::fmt(self, f)
        } else {
            fmt::Display::fmt(self, f)
        }
    }
}

const DEC_DIGITS_LUT: &[u8; 200] = b"\
    0001020304050607080910111213141516171819\
    2021222324252627282930313233343536373839\
    4041424344454647484950515253545556575859\
    6061626364656667686970717273747576777879\
    8081828384858687888990919293949596979899";

impl fmt::Display for U256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut n = *self;

        // 2^256 is about 1*10^78, so 79 gives an extra byte of space
        let mut buf = [MaybeUninit::<u8>::uninit(); 79];
        let mut curr = buf.len() as isize;
        let buf_ptr = &mut buf[0] as *mut _ as *mut u8;
        let lut_ptr = DEC_DIGITS_LUT.as_ptr();

        // SAFETY: Since `d1` and `d2` are always less than or equal to `198`, we
        // can copy from `lut_ptr[d1..d1 + 1]` and `lut_ptr[d2..d2 + 1]`. To show
        // that it's OK to copy into `buf_ptr`, notice that at the beginning
        // `curr == buf.len() == 39 > log(n)` since `n < 2^128 < 10^39`, and at
        // each step this is kept the same as `n` is divided. Since `n` is always
        // non-negative, this means that `curr > 0` so `buf_ptr[curr..curr + 1]`
        // is safe to access.
        unsafe {
            // eagerly decode 4 characters at a time
            while n >= 10000 {
                let rem = *(n % 10000).low() as isize;
                n /= 10000;

                let d1 = (rem / 100) << 1;
                let d2 = (rem % 100) << 1;
                curr -= 4;

                // We are allowed to copy to `buf_ptr[curr..curr + 3]` here since
                // otherwise `curr < 0`. But then `n` was originally at least `10000^10`
                // which is `10^40 > 2^128 > n`.
                ptr::copy_nonoverlapping(lut_ptr.offset(d1), buf_ptr.offset(curr), 2);
                ptr::copy_nonoverlapping(lut_ptr.offset(d2), buf_ptr.offset(curr + 2), 2);
            }

            // if we reach here numbers are <= 9999, so at most 4 chars long
            let mut n = *n.low() as isize; // possibly reduce 64bit math

            // decode 2 more chars, if > 2 chars
            if n >= 100 {
                let d1 = (n % 100) << 1;
                n /= 100;
                curr -= 2;
                ptr::copy_nonoverlapping(lut_ptr.offset(d1), buf_ptr.offset(curr), 2);
            }

            // decode last 1 or 2 chars
            if n < 10 {
                curr -= 1;
                *buf_ptr.offset(curr) = (n as u8) + b'0';
            } else {
                let d1 = n << 1;
                curr -= 2;
                ptr::copy_nonoverlapping(lut_ptr.offset(d1), buf_ptr.offset(curr), 2);
            }
        }

        // SAFETY: `curr` > 0 (since we made `buf` large enough), and all the chars are valid
        // UTF-8 since `DEC_DIGITS_LUT` is
        let buf_slice = unsafe {
            str::from_utf8_unchecked(slice::from_raw_parts(
                buf_ptr.offset(curr),
                buf.len() - curr as usize,
            ))
        };
        f.pad_integral(true, "", buf_slice)
    }
}

pub(crate) fn fmt_radix(
    mut x: U256,
    base: usize,
    prefix: &str,
    digits: &[u8],
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let mut buf = [MaybeUninit::<u8>::uninit(); 256];
    let mut curr = buf.len();

    // Accumulate each digit of the number from the least significant
    // to the most significant figure.
    for byte in buf.iter_mut().rev() {
        let n = (*x.low() as usize) % base;
        x /= base.as_u256(); // Deaccumulate the number.
        unsafe {
            #[cfg(debug_assertions)]
            let digit = digits[n];
            #[cfg(not(debug_assertions))]
            let digit = *digits.get_unchecked(n);

            byte.as_mut_ptr().write(digit); // Store the digit in the buffer.
        };
        curr -= 1;
        if x == 0 {
            // No more digits left to accumulate.
            break;
        };
    }
    let buf = &buf[curr..];

    // SAFETY: The only chars in `buf` are created by `Self::digit` which are assumed to be
    // valid UTF-8
    let buf = unsafe { str::from_utf8_unchecked(&*(buf as *const _ as *const [u8])) };
    f.pad_integral(true, prefix, buf)
}

impl fmt::Binary for U256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_radix(*self, 2, "0b", b"01", f)
    }
}

impl fmt::Octal for U256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_radix(*self, 8, "0o", b"01234567", f)
    }
}

impl fmt::LowerHex for U256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_radix(*self, 16, "0x", b"0123456789abcdef", f)
    }
}

impl fmt::UpperHex for U256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_radix(*self, 16, "0x", b"0123456789ABCDEF", f)
    }
}

impl fmt::LowerExp for U256 {
    #[allow(unused_comparisons)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO(nlordell): Ideally this should be implemented with a similar
        // to the primitive integer types as seen here:
        // https://doc.rust-lang.org/src/core/fmt/num.rs.html#274
        // Unfortunately, just porting this implementation is not possible as it
        // requires private standard library items. For now, just convert to
        // a `f64` as an approximation.
        fmt::LowerExp::fmt(&self.as_f64(), f)
    }
}

impl fmt::UpperExp for U256 {
    #[allow(unused_comparisons)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperExp::fmt(&self.as_f64(), f)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::format;

    #[test]
    fn parse_int_error() {
        assert_eq!(U256::from_str_radix("", 2), Err(Pie::Empty.into()));
        assert_eq!(U256::from_str_radix("?", 2), Err(Pie::InvalidDigit.into()));
        assert_eq!(
            U256::from_str_radix("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", 36),
            Err(Pie::Overflow.into())
        );
    }

    #[test]
    fn debug() {
        assert_eq!(
            format!("{:?}", U256::MAX),
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
        );
        assert_eq!(
            format!("{:x?}", U256::MAX),
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        );
        assert_eq!(
            format!("{:#X?}", U256::MAX),
            "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        );
    }

    #[test]
    fn display() {
        assert_eq!(
            format!("{}", U256::MAX),
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
        );
    }

    #[test]
    fn radix() {
        assert_eq!(format!("{:b}", U256::new(42)), "101010");
        assert_eq!(format!("{:o}", U256::new(42)), "52");
        assert_eq!(format!("{:x}", U256::new(42)), "2a");
    }

    #[test]
    fn exp() {
        assert_eq!(format!("{:e}", U256::new(42)), "4.2e1");
        assert_eq!(format!("{:e}", U256::new(10).pow(77)), "1e77");
        assert_eq!(format!("{:E}", U256::new(10).pow(39) * 1337), "1.337E42");
    }
}
