//! Integer convers to and from [`num::BigInt`] allowing it to be used as a
//! reference implementation for various operations.

use ethnum::{I256, U256};
use num::{bigint::Sign, BigInt};

/// Trait with common integer methods used for [`num::BigInt`] conversions.
pub trait Int: Sized {
    fn from_nibbles(n: [u64; 4]) -> (Self, bool);
    fn neg(&self) -> (Self, bool);
    fn le(&self) -> ([u8; 32], bool);
}

macro_rules! impl_int {
    ($($int:ty),*) => {$(
        impl Int for $int {
            fn from_nibbles(n: [u64; 4]) -> (Self, bool) {
                let hi = ((n[0] as u128) << 64) + (n[1] as u128);
                let lo = ((n[2] as u128) << 64) + (n[3] as u128);
                let int = Self::from_words(hi as _, lo as _);
                (int, int < 0)
            }

            fn neg(&self) -> (Self, bool) {
                self.overflowing_neg()
            }

            fn le(&self) -> ([u8; 32], bool) {
                (self.to_le_bytes(), *self < 0)
            }
        }
    )*};
}

impl_int! { I256, U256 }

/// Converts an integer type to a big integer.
pub fn from_bigint<T>(n: &BigInt) -> (T, bool)
where
    T: Int,
{
    let mut digits = n.iter_u64_digits();
    let mut nibbles = [0_u64; 4];
    for nibble in nibbles.iter_mut().rev() {
        *nibble = digits.next().unwrap_or_default();
    }

    let (result, negative) = T::from_nibbles(nibbles);
    let overflowed = digits.next().is_some();

    if let Sign::Minus = n.sign() {
        let (neg, overflow) = result.neg();
        (neg, overflowed || (negative ^ overflow))
    } else {
        (result, overflowed || negative)
    }
}

/// Converts a big integer type to an integer.
pub fn to_bigint<T>(n: &T) -> BigInt
where
    T: Int,
{
    let (bytes, negative) = n.le();
    let sign = if negative { 0xff } else { 0 };

    let mut buffer = [0_u8; 33];
    buffer[..32].copy_from_slice(&bytes);
    buffer[32] = sign;

    BigInt::from_signed_bytes_le(&buffer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::{Num as _, One as _, Zero as _};

    #[test]
    fn from_bigint_conversions() {
        let n = BigInt::from_str_radix(
            "1234567890123456789012345678901234567890123456789012345678901234567890",
            16,
        )
        .unwrap();
        let u = U256::from_words(
            0x78901234567890123456789012345678,
            0x90123456789012345678901234567890,
        );

        assert_eq!(from_bigint::<U256>(&n), (u, true));
        assert_eq!(from_bigint::<I256>(&n), (u.as_i256(), true));

        let n = -n;
        assert_eq!(from_bigint::<U256>(&n), (u.wrapping_neg(), true));
        assert_eq!(from_bigint::<I256>(&n), (u.wrapping_neg().as_i256(), true));

        let n = -BigInt::one();
        assert_eq!(from_bigint::<U256>(&n), (U256::MAX, true));
        assert_eq!(from_bigint::<I256>(&n), (I256::MINUS_ONE, false));

        let n = (BigInt::one() << 256) - 1;
        assert_eq!(from_bigint::<U256>(&n), (U256::MAX, false));
        assert_eq!(from_bigint::<I256>(&n), (I256::MINUS_ONE, true));

        let n = BigInt::one() << 255;
        assert_eq!(from_bigint::<U256>(&n), (U256::ONE << 255, false));
        assert_eq!(from_bigint::<I256>(&n), (I256::MIN, true));

        let n = -n;
        assert_eq!(from_bigint::<U256>(&n), (U256::ONE << 255, true));
        assert_eq!(from_bigint::<I256>(&n), (I256::MIN, false));
    }

    #[test]
    fn to_bigint_conversions() {
        assert_eq!(to_bigint(&U256::ZERO), BigInt::zero());
        assert_eq!(to_bigint(&U256::ONE), BigInt::one());
        assert_eq!(to_bigint(&U256::MAX), (BigInt::one() << 256) - 1);

        //assert_eq!(to_bigint(&I256::MIN), -(BigInt::one() << 255));
        assert_eq!(to_bigint(&I256::MINUS_ONE), -BigInt::one());
        assert_eq!(to_bigint(&I256::ZERO), BigInt::zero());
        assert_eq!(to_bigint(&I256::ONE), BigInt::one());
        assert_eq!(to_bigint(&I256::MAX), (BigInt::one() << 255) - 1);
    }
}
