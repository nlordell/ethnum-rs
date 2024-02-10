use core::num::ParseIntError;

use num_traits::{AsPrimitive, Bounded, CheckedAdd, CheckedDiv, CheckedEuclid, CheckedMul, CheckedNeg, CheckedRem, CheckedShl, CheckedShr, CheckedSub, ConstOne, ConstZero, Euclid, FromBytes, FromPrimitive, MulAdd, MulAddAssign, Num, NumCast, One, Pow, PrimInt, Saturating, SaturatingAdd, SaturatingMul, SaturatingSub, ToBytes, ToPrimitive, Unsigned, WrappingAdd, WrappingMul, WrappingNeg, WrappingShl, WrappingShr, WrappingSub, Zero};
use num_integer::{ExtendedGcd, Integer, Roots};

use crate::{AsU256, I256, U256};

impl AsPrimitive<u8> for U256
{
    #[inline]
    fn as_(self) -> u8 {
        self.as_u8()
    }
}
impl AsPrimitive<i8> for U256
{
    #[inline]
    fn as_(self) -> i8 {
        self.as_i8()
    }
}
impl AsPrimitive<u16> for U256
{
    #[inline]
    fn as_(self) -> u16 {
        self.as_u16()
    }
}
impl AsPrimitive<i16> for U256
{
    #[inline]
    fn as_(self) -> i16 {
        self.as_i16()
    }
}
impl AsPrimitive<u32> for U256
{
    #[inline]
    fn as_(self) -> u32 {
        self.as_u32()
    }
}
impl AsPrimitive<i32> for U256
{
    #[inline]
    fn as_(self) -> i32 {
        self.as_i32()
    }
}
impl AsPrimitive<u64> for U256
{
    #[inline]
    fn as_(self) -> u64 {
        self.as_u64()
    }
}
impl AsPrimitive<i64> for U256
{
    #[inline]
    fn as_(self) -> i64 {
        self.as_i64()
    }
}
impl AsPrimitive<u128> for U256
{
    #[inline]
    fn as_(self) -> u128 {
        self.as_u128()
    }
}
impl AsPrimitive<i128> for U256
{
    #[inline]
    fn as_(self) -> i128 {
        self.as_i128()
    }
}
impl AsPrimitive<U256> for U256
{
    #[inline]
    fn as_(self) -> U256 {
        self
    }
}
impl AsPrimitive<I256> for U256
{
    #[inline]
    fn as_(self) -> I256 {
        self.as_i256()
    }
}

impl Bounded for U256
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

impl CheckedAdd for U256
{
    #[inline]
    fn checked_add(&self, v: &Self) -> Option<Self> {
        (*self).checked_add(*v)
    }
}
impl CheckedDiv for U256
{
    #[inline]
    fn checked_div(&self, v: &Self) -> Option<Self> {
        (*self).checked_div(*v)
    }
}
impl CheckedEuclid for U256
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
impl CheckedMul for U256
{
    #[inline]
    fn checked_mul(&self, v: &Self) -> Option<Self> {
        (*self).checked_mul(*v)
    }
}
impl CheckedNeg for U256
{
    #[inline]
    fn checked_neg(&self) -> Option<Self> {
        (*self).checked_neg()
    }
}
impl CheckedRem for U256
{
    #[inline]
    fn checked_rem(&self, v: &Self) -> Option<Self> {
        (*self).checked_rem(*v)
    }
}
impl CheckedShl for U256
{
    #[inline]
    fn checked_shl(&self, rhs: u32) -> Option<Self> {
        (*self).checked_shl(rhs)
    }
}
impl CheckedShr for U256
{
    #[inline]
    fn checked_shr(&self, rhs: u32) -> Option<Self> {
        (*self).checked_shr(rhs)
    }
}
impl CheckedSub for U256
{
    #[inline]
    fn checked_sub(&self, v: &Self) -> Option<Self> {
        (*self).checked_sub(*v)
    }
}

impl ConstOne for U256
{
    const ONE: Self = Self::ONE;
}
impl ConstZero for U256
{
    const ZERO: Self = Self::ZERO;
}

impl Euclid for U256
{
    #[inline]
    fn div_euclid(&self, v: &U256) -> Self {
        (*self).div_euclid(*v)
    }

    #[inline]
    fn rem_euclid(&self, v: &U256) -> Self {
        (*self).rem_euclid(*v)
    }
}

impl FromBytes for U256
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

impl FromPrimitive for U256
{
    #[inline]
    fn from_isize(n: isize) -> Option<Self> {
        if n < 0
        {
            return None
        }
        Some(n.as_u256())
    }

    #[inline]
    fn from_i8(n: i8) -> Option<Self> {
        if n < 0
        {
            return None
        }
        Some(n.as_u256())
    }

    #[inline]
    fn from_i16(n: i16) -> Option<Self> {
        if n < 0
        {
            return None
        }
        Some(n.as_u256())
    }

    #[inline]
    fn from_i32(n: i32) -> Option<Self> {
        if n < 0
        {
            return None
        }
        Some(n.as_u256())
    }

    #[inline]
    fn from_i64(n: i64) -> Option<Self> {
        if n < 0
        {
            return None
        }
        Some(n.as_u256())
    }

    #[inline]
    fn from_i128(n: i128) -> Option<Self> {
        if n < 0
        {
            return None
        }
        Some(n.as_u256())
    }

    #[inline]
    fn from_usize(n: usize) -> Option<Self> {
        Some(n.as_u256())
    }

    #[inline]
    fn from_u8(n: u8) -> Option<Self> {
        Some(n.as_u256())
    }

    #[inline]
    fn from_u16(n: u16) -> Option<Self> {
        Some(n.as_u256())
    }

    #[inline]
    fn from_u32(n: u32) -> Option<Self> {
        Some(n.as_u256())
    }

    #[inline]
    fn from_u64(n: u64) -> Option<Self> {
        Some(n.as_u256())
    }

    #[inline]
    fn from_u128(n: u128) -> Option<Self> {
        Some(n.as_u256())
    }
    
    #[inline]
    fn from_f32(n: f32) -> Option<Self> {
        if n < Self::MIN.as_f32() || n > Self::MAX.as_f32()
        {
            return None
        }
        Some(n.as_u256())
    }

    #[inline]
    fn from_f64(n: f64) -> Option<Self> {
        if n < Self::MIN.as_f64() || n > Self::MAX.as_f64()
        {
            return None
        }
        Some(n.as_u256())
    }
}

impl MulAdd for U256
{
    type Output = Self;

    #[inline]
    fn mul_add(self, a: Self, b: Self) -> Self::Output {
        (self * a) + b
    }
}
impl MulAddAssign for U256
{
    #[inline]
    fn mul_add_assign(&mut self, a: Self, b: Self) {
        *self = self.mul_add(a, b)
    }
}

impl Num for U256
{
    type FromStrRadixErr = ParseIntError;

    #[inline]
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr>
    {
        Self::from_str_radix(str, radix)
    }
}

impl NumCast for U256
{
    #[inline]
    fn from<T: ToPrimitive>(n: T) -> Option<Self>
    {
        n.to_u128()
            .and_then(|n| Self::from_u128(n))
    }
}

impl One for U256
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
impl Pow<u8> for U256
{
    type Output = U256;

    #[inline]
    fn pow(self, rhs: u8) -> Self::Output {
        self.pow(rhs as u32)
    }
}
impl Pow<u16> for U256
{
    type Output = U256;

    #[inline]
    fn pow(self, rhs: u16) -> Self::Output {
        self.pow(rhs as u32)
    }
}
impl Pow<u32> for U256
{
    type Output = U256;

    #[inline]
    fn pow(self, rhs: u32) -> Self::Output {
        self.pow(rhs)
    }
}

impl PrimInt for U256
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
        ((self.as_i256()) << n).as_u256()
    }

    #[inline]
    fn signed_shr(self, n: u32) -> Self {
        ((self.as_i256()) >> n).as_u256()
    }

    #[inline]
    fn unsigned_shl(self, n: u32) -> Self {
        self << n
    }

    #[inline]
    fn unsigned_shr(self, n: u32) -> Self {
        self >> n
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

impl Saturating for U256
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
impl SaturatingAdd for U256
{
    #[inline]
    fn saturating_add(&self, v: &Self) -> Self {
        (*self).saturating_add(*v)
    }
}
impl SaturatingMul for U256
{
    #[inline]
    fn saturating_mul(&self, v: &Self) -> Self {
        (*self).saturating_mul(*v)
    }
}
impl SaturatingSub for U256
{
    #[inline]
    fn saturating_sub(&self, v: &Self) -> Self {
        (*self).saturating_sub(*v)
    }
}

impl ToBytes for U256
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

impl ToPrimitive for U256
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

impl Unsigned for U256 {}

impl WrappingAdd for U256
{
    #[inline]
    fn wrapping_add(&self, v: &Self) -> Self {
        (*self).wrapping_add(*v)
    }
}
impl WrappingMul for U256
{
    #[inline]
    fn wrapping_mul(&self, v: &Self) -> Self {
        (*self).wrapping_mul(*v)
    }
}
impl WrappingNeg for U256
{
    #[inline]
    fn wrapping_neg(&self) -> Self {
        (*self).wrapping_neg()
    }
}
impl WrappingShl for U256
{
    #[inline]
    fn wrapping_shl(&self, rhs: u32) -> Self {
        (*self).wrapping_shl(rhs)
    }
}
impl WrappingShr for U256
{
    #[inline]
    fn wrapping_shr(&self, rhs: u32) -> Self {
        (*self).wrapping_shr(rhs)
    }
}
impl WrappingSub for U256
{
    #[inline]
    fn wrapping_sub(&self, v: &Self) -> Self {
        (*self).wrapping_sub(*v)
    }
}

impl Zero for U256
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

impl Integer for U256
{
    /// Unsigned integer division. Returns the same result as `div` (`/`).
    #[inline]
    fn div_floor(&self, other: &Self) -> Self {
        *self / *other
    }

    /// Unsigned integer modulo operation. Returns the same result as `rem` (`%`).
    #[inline]
    fn mod_floor(&self, other: &Self) -> Self {
        *self % *other
    }

    #[inline]
    fn div_ceil(&self, other: &Self) -> Self {
        *self / *other + if Self::ZERO != *self % *other {Self::ONE} else {Self::ZERO}
    }

    /// Calculates the Greatest Common Divisor (GCD) of the number and `other`
    #[inline]
    fn gcd(&self, other: &Self) -> Self {
        // Use Stein's algorithm
        let mut m = *self;
        let mut n = *other;
        if m == 0 || n == 0 {
            return m | n;
        }

        // find common factors of 2
        let shift = (m | n).trailing_zeros();

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
            *self * (*other / egcd.gcd)
        };
        (egcd, lcm)
    }

    /// Calculates the Lowest Common Multiple (LCM) of the number and `other`.
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
        let lcm = *self * (*other / gcd);
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

    /// Returns `true` if the number is divisible by `2`.
    #[inline]
    fn is_even(&self) -> bool {
        *self % 2 == 0
    }

    /// Returns `true` if the number is not divisible by `2`.
    #[inline]
    fn is_odd(&self) -> bool {
        !self.is_even()
    }

    /// Simultaneous truncated integer division and modulus.
    #[inline]
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        (*self / *other, *self % *other)
    }
}

#[inline]
fn bits<T>() -> u32 {
    8 * core::mem::size_of::<T>() as u32
}

impl Roots for U256
{
    #[inline]
    fn nth_root(&self, n: u32) -> Self {
        fn go(a: U256, n: u32) -> U256 {
            // Specialize small roots
            match n {
                0 => panic!("can't find a root of degree 0!"),
                1 => return a,
                2 => return a.sqrt(),
                3 => return a.cbrt(),
                _ => (),
            }

            // The root of values less than 2ⁿ can only be 0 or 1.
            if bits::<U256>() <= n || a < (1 << n) {
                return if a > 0 {U256::ONE} else {U256::ZERO}
            }

            // 128-bit division is slow, so do a bitwise `nth_root` until it's small enough.
            if a <= core::u64::MAX.as_u256() {
                a.as_u64().nth_root(n).as_u256()
            } else {
                let lo = (a >> n).nth_root(n) << 1;
                let hi: U256 = lo + U256::ONE;
                // 128-bit `checked_mul` also involves division, but we can't always
                // compute `hiⁿ` without risking overflow.  Try to avoid it though...
                if hi.next_power_of_two().trailing_zeros() * n >= bits::<U256>() {
                    match num_traits::checked_pow(hi, n as usize) {
                        Some(x) if x <= a => hi,
                        _ => lo,
                    }
                } else {
                    if hi.pow(n) <= a {
                        hi
                    } else {
                        lo
                    }
                }
            }
        }
        go(*self, n)
    }

    #[inline]
    fn sqrt(&self) -> Self {
        fn go(a: U256) -> U256 {
            if a <= core::u64::MAX.as_u256() {
                (a.as_u64()).sqrt().as_u256()
            } else {
                let lo = (a >> 2u32).sqrt() << 1;
                let hi = lo + 1;
                if hi * hi <= a {
                    hi
                } else {
                    lo
                }
            }
        }
        go(*self)
    }

    #[inline]
    fn cbrt(&self) -> Self {
        fn go(a: U256) -> U256 {
            if a <= core::u64::MAX.as_u256() {
                a.as_f64().cbrt().as_u256()
            } else {
                let lo = (a >> 3u32).cbrt() << 1;
                let hi = lo + 1;
                if hi * hi * hi <= a {
                    hi
                } else {
                    lo
                }
            }
        }
        go(*self)
    }
}