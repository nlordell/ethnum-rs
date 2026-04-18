//! Module with safe helpers for creating error variants for standard library
//! errors without public constructors.

use core::num::{IntErrorKind, ParseIntError, TryFromIntError};

/// Returns a `ParseIntError` with the specified `IntErrorKind`.
pub fn pie(kind: IntErrorKind) -> ParseIntError {
    match kind {
        IntErrorKind::Empty => u8_parse_error(""),
        IntErrorKind::InvalidDigit => u8_parse_error("?"),
        IntErrorKind::PosOverflow => u8_parse_error("256"),
        IntErrorKind::NegOverflow => i8_parse_error("-129"),
        IntErrorKind::Zero => zero_parse_error(),
        _ => u8_parse_error("?"), // fallback for future variants
    }
}

fn u8_parse_error(s: &str) -> ParseIntError {
    s.parse::<u8>().unwrap_err()
}

fn i8_parse_error(s: &str) -> ParseIntError {
    s.parse::<i8>().unwrap_err()
}

fn zero_parse_error() -> ParseIntError {
    "0".parse::<core::num::NonZeroU8>().unwrap_err()
}

/// Returns a `TryFromIntError`.
pub fn tfie() -> TryFromIntError {
    u8::try_from(-1i8).unwrap_err()
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;

    #[test]
    #[allow(clippy::from_str_radix_10)]
    fn parse_int_error() {
        assert_eq!(
            pie(IntErrorKind::Empty),
            u8::from_str_radix("", 2).unwrap_err(),
        );
        assert_eq!(
            pie(IntErrorKind::InvalidDigit),
            u8::from_str_radix("?", 2).unwrap_err(),
        );
        assert_eq!(
            pie(IntErrorKind::PosOverflow),
            u8::from_str_radix("zzz", 36).unwrap_err(),
        );
        assert_eq!(
            pie(IntErrorKind::NegOverflow),
            i8::from_str_radix("-1337", 10).unwrap_err(),
        );
        assert_eq!(
            pie(IntErrorKind::Zero),
            "0".parse::<NonZeroU32>().unwrap_err(),
        );
    }

    #[test]
    fn try_from_int_error() {
        assert_eq!(tfie(), u8::try_from(-1).unwrap_err());
    }
}
