use core::num::ParseIntError;

use num_traits::{AsPrimitive, Bounded, CheckedAdd, CheckedDiv, CheckedEuclid, CheckedMul, CheckedNeg, CheckedRem, CheckedShl, CheckedShr, CheckedSub, ConstOne, ConstZero, Euclid, FromBytes, FromPrimitive, MulAdd, MulAddAssign, Num, NumCast, One, Pow, PrimInt, Saturating, SaturatingAdd, SaturatingMul, SaturatingSub, Signed, ToBytes, ToPrimitive, WrappingAdd, WrappingMul, WrappingNeg, WrappingShl, WrappingShr, WrappingSub, Zero};
use num_integer::{ExtendedGcd, Integer, Roots};

use crate::{AsI256, I256, U256};

impl AsPrimitive<u8> for I256
{
    #[inline]
    fn as_(self) -> u8 {
        self.as_u8()
    }
}
impl AsPrimitive<i8> for I256
{
    #[inline]
    fn as_(self) -> i8 {
        self.as_i8()
    }
}
impl AsPrimitive<u16> for I256
{
    #[inline]
    fn as_(self) -> u16 {
        self.as_u16()
    }
}
impl AsPrimitive<i16> for I256
{
    #[inline]
    fn as_(self) -> i16 {
        self.as_i16()
    }
}
impl AsPrimitive<u32> for I256
{
    #[inline]
    fn as_(self) -> u32 {
        self.as_u32()
    }
}
impl AsPrimitive<i32> for I256
{
    #[inline]
    fn as_(self) -> i32 {
        self.as_i32()
    }
}
impl AsPrimitive<u64> for I256
{
    #[inline]
    fn as_(self) -> u64 {
        self.as_u64()
    }
}
impl AsPrimitive<i64> for I256
{
    #[inline]
    fn as_(self) -> i64 {
        self.as_i64()
    }
}
impl AsPrimitive<u128> for I256
{
    #[inline]
    fn as_(self) -> u128 {
        self.as_u128()
    }
}
impl AsPrimitive<i128> for I256
{
    #[inline]
    fn as_(self) -> i128 {
        self.as_i128()
    }
}
impl AsPrimitive<U256> for I256
{
    #[inline]
    fn as_(self) -> U256 {
        self.as_u256()
    }
}
impl AsPrimitive<I256> for I256
{
    #[inline]
    fn as_(self) -> I256 {
        self
    }
}

impl Bounded for I256
{
    #[inline]
    fn max_value() -> Self {
        Self::MAX
    }
    #[inline]
    fn min_value() -> Self {
        Self::MIN
    }
}

impl CheckedAdd for I256
{
    #[inline]
    fn checked_add(&self, v: &Self) -> Option<Self> {
        (*self).checked_add(*v)
    }
}
impl CheckedDiv for I256
{
    #[inline]
    fn checked_div(&self, v: &Self) -> Option<Self> {
        (*self).checked_div(*v)
    }
}
impl CheckedEuclid for I256
{
    #[inline]
    fn checked_div_euclid(&self, v: &Self) -> Option<Self> {
        (*self).checked_div_euclid(*v)
    }

    #[inline]
    fn checked_rem_euclid(&self, v: &Self) -> Option<Self> {
        (*self).checked_rem_euclid(*v)
    }
}
impl CheckedMul for I256
{
    #[inline]
    fn checked_mul(&self, v: &Self) -> Option<Self> {
        (*self).checked_mul(*v)
    }
}
impl CheckedNeg for I256
{
    #[inline]
    fn checked_neg(&self) -> Option<Self> {
        (*self).checked_neg()
    }
}
impl CheckedRem for I256
{
    #[inline]
    fn checked_rem(&self, v: &Self) -> Option<Self> {
        (*self).checked_rem(*v)
    }
}
impl CheckedShl for I256
{
    #[inline]
    fn checked_shl(&self, rhs: u32) -> Option<Self> {
        (*self).checked_shl(rhs)
    }
}
impl CheckedShr for I256
{
    #[inline]
    fn checked_shr(&self, rhs: u32) -> Option<Self> {
        (*self).checked_shr(rhs)
    }
}
impl CheckedSub for I256
{
    #[inline]
    fn checked_sub(&self, v: &Self) -> Option<Self> {
        (*self).checked_sub(*v)
    }
}

impl ConstOne for I256
{
    const ONE: Self = Self::ONE;
}
impl ConstZero for I256
{
    const ZERO: Self = Self::ZERO;
}

impl Euclid for I256
{
    #[inline]
    fn div_euclid(&self, v: &I256) -> Self {
        (*self).div_euclid(*v)
    }

    #[inline]
    fn rem_euclid(&self, v: &I256) -> Self {
        (*self).rem_euclid(*v)
    }
}

impl FromBytes for I256
{
    type Bytes = [u8; 32];

    #[inline]
    fn from_be_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_be_bytes(*bytes)
    }
    #[inline]
    fn from_le_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_le_bytes(*bytes)
    }
    #[inline]
    fn from_ne_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_ne_bytes(*bytes)
    }
}

impl FromPrimitive for I256
{
    #[inline]
    fn from_isize(n: isize) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_i8(n: i8) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_i16(n: i16) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_i32(n: i32) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_i64(n: i64) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_i128(n: i128) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_usize(n: usize) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_u8(n: u8) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_u16(n: u16) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_u32(n: u32) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_u64(n: u64) -> Option<Self> {
        Some(n.as_i256())
    }

    #[inline]
    fn from_u128(n: u128) -> Option<Self> {
        Some(n.as_i256())
    }
    
    #[inline]
    fn from_f32(n: f32) -> Option<Self> {
        if n < Self::MIN.as_f32() || n > Self::MAX.as_f32()
        {
            return None
        }
        Some(n.as_i256())
    }

    #[inline]
    fn from_f64(n: f64) -> Option<Self> {
        if n < Self::MIN.as_f64() || n > Self::MAX.as_f64()
        {
            return None
        }
        Some(n.as_i256())
    }
}

impl MulAdd for I256
{
    type Output = Self;

    #[inline]
    fn mul_add(self, a: Self, b: Self) -> Self::Output {
        (self * a) + b
    }
}
impl MulAddAssign for I256
{
    #[inline]
    fn mul_add_assign(&mut self, a: Self, b: Self) {
        *self = self.mul_add(a, b)
    }
}

impl Num for I256
{
    type FromStrRadixErr = ParseIntError;

    #[inline]
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr>
    {
        Self::from_str_radix(str, radix)
    }
}

impl NumCast for I256
{
    #[inline]
    fn from<T: ToPrimitive>(n: T) -> Option<Self>
    {
        n.to_i128()
            .and_then(|n| Self::from_i128(n))
    }
}

impl One for I256
{
    #[inline]
    fn one() -> Self {
        Self::ONE
    }
    #[inline]
    fn is_one(&self) -> bool {
        *self == Self::ONE
    }
}
impl Pow<u8> for I256
{
    type Output = I256;

    #[inline]
    fn pow(self, rhs: u8) -> Self::Output {
        self.pow(rhs as u32)
    }
}
impl Pow<u16> for I256
{
    type Output = I256;

    #[inline]
    fn pow(self, rhs: u16) -> Self::Output {
        self.pow(rhs as u32)
    }
}
impl Pow<u32> for I256
{
    type Output = I256;

    #[inline]
    fn pow(self, rhs: u32) -> Self::Output {
        self.pow(rhs)
    }
}

impl PrimInt for I256
{
    #[inline]
    fn count_ones(self) -> u32 {
        self.count_ones()
    }

    #[inline]
    fn count_zeros(self) -> u32 {
        self.count_zeros()
    }

    #[inline]
    fn leading_ones(self) -> u32 {
        self.leading_ones()
    }

    #[inline]
    fn leading_zeros(self) -> u32 {
        self.leading_zeros()
    }

    #[inline]
    fn trailing_ones(self) -> u32 {
        self.trailing_ones()
    }

    #[inline]
    fn trailing_zeros(self) -> u32 {
        self.trailing_zeros()
    }

    #[inline]
    fn rotate_left(self, n: u32) -> Self {
        self.rotate_left(n)
    }

    #[inline]
    fn rotate_right(self, n: u32) -> Self {
        self.rotate_right(n)
    }

    #[inline]
    fn signed_shl(self, n: u32) -> Self {
        self << n
    }

    #[inline]
    fn signed_shr(self, n: u32) -> Self {
        self >> n
    }

    #[inline]
    fn unsigned_shl(self, n: u32) -> Self {
        ((self.as_u256()) << n).as_i256()
    }

    #[inline]
    fn unsigned_shr(self, n: u32) -> Self {
        ((self.as_u256()) >> n).as_i256()
    }

    #[inline]
    fn swap_bytes(self) -> Self {
        self.swap_bytes()
    }

    #[inline]
    fn reverse_bits(self) -> Self {
        self.reverse_bits()
    }

    #[inline]
    fn from_be(x: Self) -> Self {
        Self::from_be(x)
    }

    #[inline]
    fn from_le(x: Self) -> Self {
        Self::from_le(x)
    }

    #[inline]
    fn to_be(self) -> Self {
        self.to_be()
    }

    #[inline]
    fn to_le(self) -> Self {
        self.to_le()
    }

    #[inline]
    fn pow(self, exp: u32) -> Self {
        self.pow(exp)
    }
}

impl Saturating for I256
{
    #[inline]
    fn saturating_add(self, v: Self) -> Self {
        self.saturating_add(v)
    }

    #[inline]
    fn saturating_sub(self, v: Self) -> Self {
        self.saturating_sub(v)
    }
}
impl SaturatingAdd for I256
{
    #[inline]
    fn saturating_add(&self, v: &Self) -> Self {
        (*self).saturating_add(*v)
    }
}
impl SaturatingMul for I256
{
    #[inline]
    fn saturating_mul(&self, v: &Self) -> Self {
        (*self).saturating_mul(*v)
    }
}
impl SaturatingSub for I256
{
    #[inline]
    fn saturating_sub(&self, v: &Self) -> Self {
        (*self).saturating_sub(*v)
    }
}

impl Signed for I256
{
    #[inline]
    fn abs(&self) -> Self {
        if self.is_negative() {
            -*self
        } else {
            *self
        }
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        (*self).abs_diff(*other).as_i256()
    }

    #[inline]
    fn signum(&self) -> Self {
        self.signum128().into()
    }

    #[inline]
    fn is_positive(&self) -> bool {
        (*self).is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        (*self).is_negative()
    }
}

impl ToBytes for I256
{
    type Bytes = [u8; 32];

    #[inline]
    fn to_be_bytes(&self) -> Self::Bytes {
        (*self).to_be_bytes()
    }

    #[inline]
    fn to_le_bytes(&self) -> Self::Bytes {
        (*self).to_le_bytes()
    }

    #[inline]
    fn to_ne_bytes(&self) -> Self::Bytes {
        (*self).to_ne_bytes()
    }
}

impl ToPrimitive for I256
{
    #[inline]
    fn to_isize(&self) -> Option<isize> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_i8(&self) -> Option<i8> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_i16(&self) -> Option<i16> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_i32(&self) -> Option<i32> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_i64(&self) -> Option<i64> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_i128(&self) -> Option<i128> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_usize(&self) -> Option<usize> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_u8(&self) -> Option<u8> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_u16(&self) -> Option<u16> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_u32(&self) -> Option<u32> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_u64(&self) -> Option<u64> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_u128(&self) -> Option<u128> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_f32(&self) -> Option<f32> {
        (*self).try_into().ok()
    }

    #[inline]
    fn to_f64(&self) -> Option<f64> {
        (*self).try_into().ok()
    }
}

impl WrappingAdd for I256
{
    #[inline]
    fn wrapping_add(&self, v: &Self) -> Self {
        (*self).wrapping_add(*v)
    }
}
impl WrappingMul for I256
{
    #[inline]
    fn wrapping_mul(&self, v: &Self) -> Self {
        (*self).wrapping_mul(*v)
    }
}
impl WrappingNeg for I256
{
    #[inline]
    fn wrapping_neg(&self) -> Self {
        (*self).wrapping_neg()
    }
}
impl WrappingShl for I256
{
    #[inline]
    fn wrapping_shl(&self, rhs: u32) -> Self {
        (*self).wrapping_shl(rhs)
    }
}
impl WrappingShr for I256
{
    #[inline]
    fn wrapping_shr(&self, rhs: u32) -> Self {
        (*self).wrapping_shr(rhs)
    }
}
impl WrappingSub for I256
{
    #[inline]
    fn wrapping_sub(&self, v: &Self) -> Self {
        (*self).wrapping_sub(*v)
    }
}

impl Zero for I256
{
    #[inline]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }
}

impl Integer for I256
{
    /// Floored integer division
    #[inline]
    fn div_floor(&self, other: &Self) -> Self {
        // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
        // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
        let (d, r) = self.div_rem(other);
        if (r > 0 && *other < 0) || (r < 0 && *other > 0) {
            d - 1
        } else {
            d
        }
    }

    /// Floored integer modulo
    #[inline]
    fn mod_floor(&self, other: &Self) -> Self {
        // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
        // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
        let r = *self % *other;
        if (r > 0 && *other < 0) || (r < 0 && *other > 0) {
            r + *other
        } else {
            r
        }
    }

    /// Calculates `div_floor` and `mod_floor` simultaneously
    #[inline]
    fn div_mod_floor(&self, other: &Self) -> (Self, Self) {
        // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
        // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
        let (d, r) = self.div_rem(other);
        if (r > 0 && *other < 0) || (r < 0 && *other > 0) {
            (d - 1, r + *other)
        } else {
            (d, r)
        }
    }

    #[inline]
    fn div_ceil(&self, other: &Self) -> Self {
        let (d, r) = self.div_rem(other);
        if (r > 0 && *other > 0) || (r < 0 && *other < 0) {
            d + 1
        } else {
            d
        }
    }

    /// Calculates the Greatest Common Divisor (GCD) of the number and
    /// `other`. The result is always non-negative.
    #[inline]
    fn gcd(&self, other: &Self) -> Self {
        // Use Stein's algorithm
        let mut m = *self;
        let mut n = *other;
        if m == 0 || n == 0 {
            return (m | n).abs();
        }

        // find common factors of 2
        let shift = (m | n).trailing_zeros();

        // The algorithm needs positive numbers, but the minimum value
        // can't be represented as a positive one.
        // It's also a power of two, so the gcd can be
        // calculated by bitshifting in that case

        // Assuming two's complement, the number created by the shift
        // is positive for all numbers except gcd = abs(min value)
        // The call to .abs() causes a panic in debug mode
        if m == Self::min_value() || n == Self::min_value() {
            return (Self::ONE << shift).abs();
        }

        // guaranteed to be positive now, rest like unsigned algorithm
        m = m.abs();
        n = n.abs();

        // divide n and m by 2 until odd
        m >>= m.trailing_zeros();
        n >>= n.trailing_zeros();

        while m != n {
            if m > n {
                m -= n;
                m >>= m.trailing_zeros();
            } else {
                n -= m;
                n >>= n.trailing_zeros();
            }
        }
        m << shift
    }

    #[inline]
    fn extended_gcd_lcm(&self, other: &Self) -> (ExtendedGcd<Self>, Self) {
        let egcd = self.extended_gcd(other);
        // should not have to recalculate abs
        let lcm = if egcd.gcd.is_zero() {
            Self::zero()
        } else {
            (*self * (*other / egcd.gcd)).abs()
        };
        (egcd, lcm)
    }

    /// Calculates the Lowest Common Multiple (LCM) of the number and
    /// `other`.
    #[inline]
    fn lcm(&self, other: &Self) -> Self {
        self.gcd_lcm(other).1
    }

    /// Calculates the Greatest Common Divisor (GCD) and
    /// Lowest Common Multiple (LCM) of the number and `other`.
    #[inline]
    fn gcd_lcm(&self, other: &Self) -> (Self, Self) {
        if self.is_zero() && other.is_zero() {
            return (Self::zero(), Self::zero());
        }
        let gcd = self.gcd(other);
        // should not have to recalculate abs
        let lcm = (*self * (*other / gcd)).abs();
        (gcd, lcm)
    }

    /// Returns `true` if the number is a multiple of `other`.
    #[inline]
    fn is_multiple_of(&self, other: &Self) -> bool {
        if other.is_zero() {
            return self.is_zero();
        }
        *self % *other == 0
    }

    /// Returns `true` if the number is divisible by `2`
    #[inline]
    fn is_even(&self) -> bool {
        (*self) & 1 == 0
    }

    /// Returns `true` if the number is not divisible by `2`
    #[inline]
    fn is_odd(&self) -> bool {
        !self.is_even()
    }

    /// Simultaneous truncated integer division and modulus.
    #[inline]
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        (*self / *other, *self % *other)
    }

    /// Rounds up to nearest multiple of argument.
    #[inline]
    fn next_multiple_of(&self, other: &Self) -> Self {
        // Avoid the overflow of `MIN % -1`
        if *other == -1 {
            return *self;
        }

        let m = Integer::mod_floor(self, other);
        *self + if m == 0 { Self::ZERO } else { other - m }
    }

    /// Rounds down to nearest multiple of argument.
    #[inline]
    fn prev_multiple_of(&self, other: &Self) -> Self {
        // Avoid the overflow of `MIN % -1`
        if *other == -1 {
            return *self;
        }

        *self - Integer::mod_floor(self, other)
    }
}

impl Roots for I256
{
    #[inline]
    fn nth_root(&self, n: u32) -> Self {
        if *self >= 0 {
            self.as_u256().nth_root(n).as_i256()
        } else {
            assert!(n.is_odd(), "even roots of a negative are imaginary");
            -self.wrapping_neg().as_u256().nth_root(n).as_i256()
        }
    }

    #[inline]
    fn sqrt(&self) -> Self {
        assert!(*self >= 0, "the square root of a negative is imaginary");
        self.as_u256().sqrt().as_i256()
    }

    #[inline]
    fn cbrt(&self) -> Self {
        if *self >= 0 {
            self.as_u256().cbrt().as_i256()
        } else {
            -self.wrapping_neg().as_u256().cbrt().as_i256()
        }
    }
}