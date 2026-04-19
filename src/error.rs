//! Module with hacks for creating error variants for standard library errors
//! without public interfaces.

use core::{
    mem,
    num::{IntErrorKind, ParseIntError, TryFromIntError},
};

/// Returns a `ParseIntError` from an `IntErrorKind`.
pub const fn pie(kind: IntErrorKind) -> ParseIntError {
    unsafe { mem::transmute(kind) }
}

/// Returns a `TryFromIntError`.
///
/// `TryFromIntError` has no public constructor. We construct it from a
/// zero-initialized buffer of the correct size, which works regardless of
/// the type's internal layout across Rust versions.
pub const fn tfie() -> TryFromIntError {
    // SAFETY: `TryFromIntError` is a simple error type with no invariants
    // beyond its size. A zero-initialized value is valid for all known
    // layouts (zero-sized on Rust < 1.97, one byte on Rust >= 1.97).
    unsafe { mem::MaybeUninit::<TryFromIntError>::zeroed().assume_init() }
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
