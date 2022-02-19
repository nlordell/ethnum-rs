//! Module containing macros for implementing `core::fmt` traits.

macro_rules! impl_fmt {
    (impl Fmt for $int:ident;) => {
        impl $crate::fmt::FromStrRadixHelper for $int {
            #[inline]
            fn min_value() -> Self {
                Self::MIN
            }
            #[inline]
            fn max_value() -> Self {
                Self::MAX
            }
            #[inline]
            fn from_u32(u: u32) -> Self {
                Self::from(u)
            }
            #[inline]
            fn checked_mul(&self, other: u32) -> Option<Self> {
                Self::checked_mul(*self, Self::from(other))
            }
            #[inline]
            fn checked_sub(&self, other: u32) -> Option<Self> {
                Self::checked_sub(*self, Self::from(other))
            }
            #[inline]
            fn checked_add(&self, other: u32) -> Option<Self> {
                Self::checked_add(*self, Self::from(other))
            }
        }

        impl ::core::str::FromStr for $int {
            type Err = ::core::num::ParseIntError;

            #[inline]
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                $crate::fmt::from_str_radix(s, 10)
            }
        }

        __impl_fmt_base! { Binary   for $int }
        __impl_fmt_base! { Octal    for $int }
        __impl_fmt_base! { LowerHex for $int }
        __impl_fmt_base! { UpperHex for $int }

        impl ::core::fmt::Debug for $int {
            #[inline]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                // NOTE: Work around `Formatter::debug_{lower,upper}_hex` being private
                // and not stabilized.
                #[allow(deprecated)]
                let flags = f.flags();
                const DEBUG_LOWER_HEX: u32 = 1 << 4;
                const DEBUG_UPPER_HEX: u32 = 1 << 5;

                if flags & DEBUG_LOWER_HEX != 0 {
                    ::core::fmt::LowerHex::fmt(self, f)
                } else if flags & DEBUG_UPPER_HEX != 0 {
                    ::core::fmt::UpperHex::fmt(self, f)
                } else {
                    ::core::fmt::Display::fmt(self, f)
                }
            }
        }

        impl ::core::fmt::Display for $int {
            #[allow(unused_comparisons, unused_imports)]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                use $crate::uint::AsU256;

                let is_nonnegative = *self >= 0;
                let n = if is_nonnegative {
                    self.as_u256()
                } else {
                    // convert the negative num to positive by summing 1 to it's 2 complement
                    (!self.as_u256()).wrapping_add($crate::uint::U256::ONE)
                };
                $crate::fmt::fmt_u256(n, is_nonnegative, f)
            }
        }

        impl ::core::fmt::LowerExp for $int {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                // TODO(nlordell): Ideally this should be implemented similarly
                // to the primitive integer types as seen here:
                // https://doc.rust-lang.org/src/core/fmt/num.rs.html#274
                // Unfortunately, just porting this implementation is not
                // possible as it requires private standard library items. For
                // now, just convert to a `f64` as an approximation.
                ::core::fmt::LowerExp::fmt(&self.as_f64(), f)
            }
        }

        impl ::core::fmt::UpperExp for $int {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                ::core::fmt::UpperExp::fmt(&self.as_f64(), f)
            }
        }
    };
}

macro_rules! __impl_fmt_base {
    ($base:ident for $int:ident) => {
        impl ::core::fmt::$base for $int {
            #[allow(unused_imports)]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                use $crate::{fmt::GenericRadix, uint::AsU256};

                $crate::fmt::$base.fmt_u256(self.as_u256(), f)
            }
        }
    };
}
