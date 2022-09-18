//! Minimal parsing implementation for 256-bit integers.

use std::fmt::{self, Display, Formatter};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Int {
    hi: i128,
    lo: u128,
}

impl Int {
    pub fn into_words(self) -> (i128, i128) {
        (self.hi, self.lo as _)
    }

    pub fn from_literal(src: &str) -> Result<Self, LiteralError> {
        from_literal(src)
    }

    fn neg(&self) -> Self {
        let (lo, carry) = (!self.lo).overflowing_add(1);
        let hi = (!self.hi).wrapping_add(carry as _);

        Self { hi, lo }
    }

    fn is_negative(&self) -> bool {
        self.hi.is_negative()
    }

    fn abs(&self) -> (bool, Uint) {
        let is_negative = self.is_negative();
        let abs = match is_negative {
            true => self.neg(),
            false => *self,
        };

        (
            is_negative,
            Uint {
                hi: abs.hi as _,
                lo: abs.lo,
            },
        )
    }

    fn new(is_negative: bool, abs: Uint) -> Option<Self> {
        let mut signed = Int {
            hi: abs.hi as _,
            lo: abs.lo,
        };
        if is_negative {
            signed = signed.neg();
        }
        if is_negative != signed.is_negative() {
            return None;
        }

        Some(signed)
    }
}

impl FromLiteral for Int {
    fn is_signed() -> bool {
        true
    }

    fn mul_radix(&self, radix: u32) -> Option<Self> {
        let (is_negative, abs) = self.abs();
        let result = abs.mul_radix(radix)?;
        Self::new(is_negative, result)
    }

    fn add_digit(&self, digit: u32) -> Option<Self> {
        let (lo, carry) = self.lo.overflowing_add(digit as _);
        let hi = self.hi.wrapping_add(carry as _);
        if (hi, lo) < (self.hi, self.lo) {
            return None;
        }

        Some(Self { hi, lo })
    }

    fn sub_digit(&self, digit: u32) -> Option<Self> {
        let (lo, carry) = self.lo.overflowing_sub(digit as _);
        let hi = self.hi.wrapping_sub(carry as _);
        if (hi, lo) > (self.hi, self.lo) {
            return None;
        }

        Some(Self { hi, lo })
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Uint {
    hi: u128,
    lo: u128,
}

impl Uint {
    pub fn into_words(self) -> (u128, u128) {
        (self.hi, self.lo)
    }

    pub fn from_literal(src: &str) -> Result<Self, LiteralError> {
        from_literal(src)
    }
}

impl FromLiteral for Uint {
    fn is_signed() -> bool {
        false
    }

    fn mul_radix(&self, radix: u32) -> Option<Self> {
        let radix = radix as u128;
        let (lh, ll) = (
            (self.lo >> 64) as u128,
            (self.lo & (u64::MAX as u128)) as u128,
        );

        let llx = ll * radix;
        let lhx = lh * radix;
        let (lo, carry) = llx.overflowing_add(lhx << 64);

        let hlx = (lhx >> 64) + (carry as u128);
        let hhx = self.hi.checked_mul(radix)?;
        let hi = hhx.checked_add(hlx)?;

        Some(Self { hi, lo })
    }

    fn add_digit(&self, digit: u32) -> Option<Self> {
        let (lo, carry) = self.lo.overflowing_add(digit as _);
        let hi = self.hi.checked_add(carry as _)?;

        Some(Self { hi, lo })
    }

    fn sub_digit(&self, _: u32) -> Option<Self> {
        None
    }
}

trait FromLiteral: Default {
    fn is_signed() -> bool;
    fn mul_radix(&self, radix: u32) -> Option<Self>;
    fn add_digit(&self, digit: u32) -> Option<Self>;
    fn sub_digit(&self, digit: u32) -> Option<Self>;
}

fn from_literal<T: FromLiteral>(src: &str) -> Result<T, LiteralError> {
    if src.is_empty() {
        return Err(LiteralError::Empty);
    }

    let src = src.as_bytes();
    let (is_positive, prefixed_digits) = match src[0] {
        b'+' | b'-' if src[1..].is_empty() => {
            return Err(LiteralError::InvalidDigit);
        }
        b'+' => (true, &src[1..]),
        b'-' if T::is_signed() => (false, &src[1..]),
        _ => (true, src),
    };

    let (radix, digits) = match prefixed_digits.get(..2) {
        Some(b"0b") => (2, &prefixed_digits[2..]),
        Some(b"0o") => (8, &prefixed_digits[2..]),
        Some(b"0x") => (16, &prefixed_digits[2..]),
        _ => (10, prefixed_digits),
    };

    type Op<T> = fn(&T, u32) -> Option<T>;
    let (op, overflow_err) = match is_positive {
        true => (T::add_digit as Op<T>, LiteralError::PosOverflow),
        false => (T::sub_digit as Op<T>, LiteralError::NegOverflow),
    };

    let mut result = T::default();
    let mut empty = true;
    for &c in digits {
        if c == b'_' || c.is_ascii_whitespace() {
            // Allow separators and inner-whitespace
            continue;
        }

        let x = (c as char)
            .to_digit(radix)
            .ok_or(LiteralError::InvalidDigit)?;
        result = result
            .mul_radix(radix)
            .and_then(|r| op(&r, x))
            .ok_or(overflow_err)?;
        empty = false;
    }

    if empty {
        return Err(LiteralError::InvalidDigit);
    }

    Ok(result)
}

#[derive(Clone, Copy, Debug)]
pub enum LiteralError {
    Empty,
    InvalidDigit,
    PosOverflow,
    NegOverflow,
}

impl Display for LiteralError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Empty => f.write_str("cannot parse empty integer literal"),
            Self::InvalidDigit => f.write_str("invalid digit found in integer literal"),
            Self::PosOverflow => f.write_str("integer literal too large"),
            Self::NegOverflow => f.write_str("integer literal too small"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_negative_answer() {
        let answer = Int::default()
            .mul_radix(10)
            .unwrap()
            .sub_digit(4)
            .unwrap()
            .mul_radix(10)
            .unwrap()
            .sub_digit(2)
            .unwrap();

        assert_eq!(
            answer,
            Int {
                hi: -1,
                lo: -42 as _,
            }
        )
    }

    #[test]
    fn the_answer() {
        let answer = Uint::default()
            .mul_radix(10)
            .unwrap()
            .add_digit(4)
            .unwrap()
            .mul_radix(10)
            .unwrap()
            .add_digit(2)
            .unwrap();

        assert_eq!(answer, Uint { hi: 0, lo: 42 })
    }

    #[test]
    fn signed_limits() {
        for s in [
            "-0b1000000000000000000000000000000000000000000000000000000000000000
                0000000000000000000000000000000000000000000000000000000000000000
                0000000000000000000000000000000000000000000000000000000000000000
                0000000000000000000000000000000000000000000000000000000000000000",
            "-0o1000000000000000000000000000000000000000000
                0000000000000000000000000000000000000000000",
            "-57896044618658097711785492504343953926634992332820282019728792003956564819968",
            "-0x8000000000000000000000000000000000000000000000000000000000000000",
        ] {
            assert_eq!(
                Int::from_literal(s).unwrap(),
                Int {
                    hi: i128::MIN,
                    lo: u128::MIN
                },
            );
        }

        for s in ["0b0", "0o0", "0", "0x0"] {
            assert_eq!(Int::from_literal(s).unwrap(), Int::default());
        }

        for s in [
            "0b0111111111111111111111111111111111111111111111111111111111111111
               1111111111111111111111111111111111111111111111111111111111111111
               1111111111111111111111111111111111111111111111111111111111111111
               1111111111111111111111111111111111111111111111111111111111111111",
            "0o0777777777777777777777777777777777777777777
               7777777777777777777777777777777777777777777",
            "57896044618658097711785492504343953926634992332820282019728792003956564819967",
            "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        ] {
            assert_eq!(
                Int::from_literal(s).unwrap(),
                Int {
                    hi: i128::MAX,
                    lo: u128::MAX
                },
            );
        }
    }

    #[test]
    fn unsigned_limits() {
        for s in ["0b0", "0o0", "0", "0x0"] {
            assert_eq!(Uint::from_literal(s).unwrap(), Uint::default());
        }

        for s in [
            "0b1111111111111111111111111111111111111111111111111111111111111111
               1111111111111111111111111111111111111111111111111111111111111111
               1111111111111111111111111111111111111111111111111111111111111111
               1111111111111111111111111111111111111111111111111111111111111111",
            "0o1777777777777777777777777777777777777777777
               7777777777777777777777777777777777777777777",
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        ] {
            assert_eq!(
                Uint::from_literal(s).unwrap(),
                Uint {
                    hi: u128::MAX,
                    lo: u128::MAX
                },
            );
        }
    }

    #[test]
    fn signed_overflow() {
        for s in [
            "-0b1000000000000000000000000000000000000000000000000000000000000000
                0000000000000000000000000000000000000000000000000000000000000000
                0000000000000000000000000000000000000000000000000000000000000000
                0000000000000000000000000000000000000000000000000000000000000001",
            "-0o1000000000000000000000000000000000000000000
                0000000000000000000000000000000000000000001",
            "-57896044618658097711785492504343953926634992332820282019728792003956564819969",
            "-0x8000000000000000000000000000000000000000000000000000000000000001",
        ] {
            assert!(matches!(
                Int::from_literal(s).unwrap_err(),
                LiteralError::NegOverflow,
            ));
        }

        for s in [
            "0b1000000000000000000000000000000000000000000000000000000000000000
               0000000000000000000000000000000000000000000000000000000000000000
               0000000000000000000000000000000000000000000000000000000000000000
               0000000000000000000000000000000000000000000000000000000000000000",
            "0o1000000000000000000000000000000000000000000
               0000000000000000000000000000000000000000000",
            "57896044618658097711785492504343953926634992332820282019728792003956564819968",
            "0x8000000000000000000000000000000000000000000000000000000000000000",
        ] {
            assert!(matches!(
                Int::from_literal(s).unwrap_err(),
                LiteralError::PosOverflow,
            ));
        }
    }

    #[test]
    fn unsigned_overflow() {
        for s in [
            "0b1
               0000000000000000000000000000000000000000000000000000000000000000
               0000000000000000000000000000000000000000000000000000000000000000
               0000000000000000000000000000000000000000000000000000000000000000
               0000000000000000000000000000000000000000000000000000000000000000",
            "0o2000000000000000000000000000000000000000000
               0000000000000000000000000000000000000000000",
            "115792089237316195423570985008687907853269984665640564039457584007913129639936",
            "0x1
               0000000000000000000000000000000000000000000000000000000000000000",
        ] {
            assert!(matches!(
                Uint::from_literal(s).unwrap_err(),
                LiteralError::PosOverflow,
            ));
        }
    }

    #[test]
    fn separators() {
        assert_eq!(
            Int::from_literal(
                "0b0000000000000000000000000000000000000000000000000000000000000000
                   1010101010101010101010101010101010101010101010101010101010101010
                   0000000000000000000000000000000000000000000000000000000000000000
                   0101010101010101010101010101010101010101010101010101010101010101"
            )
            .unwrap(),
            Int {
                hi: 0b1010101010101010101010101010101010101010101010101010101010101010,
                lo: 0b0101010101010101010101010101010101010101010101010101010101010101,
            }
        );

        assert_eq!(
            Int::from_literal("0o 0123 4567").unwrap(),
            Int {
                hi: 0,
                lo: 0o_0123_4567,
            }
        );

        assert_eq!(
            Int::from_literal("0xffff_ffff").unwrap(),
            Int {
                hi: 0,
                lo: 0xffff_ffff,
            }
        );
    }

    #[test]
    fn empty_with_separators() {
        for s in ["-", "0b _ _", "+_"] {
            assert!(matches!(
                Int::from_literal(s).unwrap_err(),
                LiteralError::InvalidDigit,
            ));
        }
    }
}
