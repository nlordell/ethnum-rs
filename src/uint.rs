//! Root module for 256-bit unsigned integer type.

mod api;
mod cmp;
mod convert;
mod fmt;
mod iter;
mod ops;

pub use self::convert::AsU256;
use crate::I256;

/// A 256-bit unsigned integer type.
#[derive(Clone, Copy, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct U256(pub [u128; 2]);

impl U256 {
    /// The additive identity for this integer type, i.e. `0`.
    pub const ZERO: Self = U256([0; 2]);

    /// The multiplicative identity for this integer type, i.e. `1`.
    pub const ONE: Self = U256::new(1);

    /// Creates a new 256-bit integer value from a primitive `u128` integer.
    #[inline]
    pub const fn new(value: u128) -> Self {
        U256::from_words(0, value)
    }

    /// Creates a new 256-bit integer value from high and low words.
    #[inline]
    pub const fn from_words(hi: u128, lo: u128) -> Self {
        #[cfg(target_endian = "little")]
        {
            U256([lo, hi])
        }
        #[cfg(target_endian = "big")]
        {
            U256([hi, lo])
        }
    }

    /// Splits a 256-bit integer into high and low words.
    #[inline]
    pub const fn into_words(self) -> (u128, u128) {
        #[cfg(target_endian = "little")]
        {
            let U256([lo, hi]) = self;
            (hi, lo)
        }
        #[cfg(target_endian = "big")]
        {
            let U256([hi, lo]) = self;
            (hi, lo)
        }
    }

    /// Get the low 128-bit word for this unsigned integer.
    #[inline]
    pub fn low(&self) -> &u128 {
        #[cfg(target_endian = "little")]
        {
            &self.0[0]
        }
        #[cfg(target_endian = "big")]
        {
            &self.0[1]
        }
    }

    /// Get the low 128-bit word for this unsigned integer as a mutable
    /// reference.
    #[inline]
    pub fn low_mut(&mut self) -> &mut u128 {
        #[cfg(target_endian = "little")]
        {
            &mut self.0[0]
        }
        #[cfg(target_endian = "big")]
        {
            &mut self.0[1]
        }
    }

    /// Get the high 128-bit word for this unsigned integer.
    #[inline]
    pub fn high(&self) -> &u128 {
        #[cfg(target_endian = "little")]
        {
            &self.0[1]
        }
        #[cfg(target_endian = "big")]
        {
            &self.0[0]
        }
    }

    /// Get the high 128-bit word for this unsigned integer as a mutable
    /// reference.
    #[inline]
    pub fn high_mut(&mut self) -> &mut u128 {
        #[cfg(target_endian = "little")]
        {
            &mut self.0[1]
        }
        #[cfg(target_endian = "big")]
        {
            &mut self.0[0]
        }
    }

    /// Cast to a primitive `i8`.
    pub const fn as_i8(self) -> i8 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `i16`.
    pub const fn as_i16(self) -> i16 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `i32`.
    pub const fn as_i32(self) -> i32 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `i64`.
    pub const fn as_i64(self) -> i64 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `i128`.
    pub const fn as_i128(self) -> i128 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a `I256`.
    pub const fn as_i256(self) -> I256 {
        let Self([a, b]) = self;
        I256([a as _, b as _])
    }

    /// Cast to a primitive `u8`.
    pub const fn as_u8(self) -> u8 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `u16`.
    pub const fn as_u16(self) -> u16 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `u32`.
    pub const fn as_u32(self) -> u32 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `u64`.
    pub const fn as_u64(self) -> u64 {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `u128`.
    pub const fn as_u128(self) -> u128 {
        let (_, lo) = self.into_words();
        lo
    }

    /// Cast to a primitive `isize`.
    pub const fn as_isize(self) -> isize {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `usize`.
    pub const fn as_usize(self) -> usize {
        let (_, lo) = self.into_words();
        lo as _
    }

    /// Cast to a primitive `f32`.
    pub fn as_f32(self) -> f32 {
        match self.into_words() {
            (0, lo) => lo as _,
            _ => f32::INFINITY,
        }
    }

    /// Cast to a primitive `f64`.
    pub fn as_f64(self) -> f64 {
        // NOTE: Binary representation of 2**128. This is used because `powi` is
        // neither `const` nor `no_std`.
        const HI: u64 = 0x47f0000000000000;
        let (hi, lo) = self.into_words();
        (hi as f64) * f64::from_bits(HI) + (lo as f64)
    }
}

#[cfg(test)]
mod tests {
    use crate::uint::U256;

    #[test]
    #[allow(clippy::float_cmp)]
    fn converts_to_f64() {
        assert_eq!(U256::from_words(1, 0).as_f64(), 2.0f64.powi(128))
    }
}
