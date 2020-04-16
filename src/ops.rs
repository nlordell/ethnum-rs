//! Module containing macros for implementing `core::ops` traits.

use crate::intrinsics::*;
use crate::U256;
use core::mem::MaybeUninit;
use core::ops;

macro_rules! impl_binops {
    ($(
        $op:ident {
            $method:ident =>
            $wrap:path,
            $overflow:path; $msg:expr
        }
    )*) => {$(
        impl ops::$op<&'_ U256> for &'_ U256 {
            type Output = U256;

            #[inline]
            fn $method(self, rhs: &'_ U256) -> Self::Output {
                binop!($wrap, $overflow [ self, rhs ] $msg)
            }
        }

        impl_auto_binop!($op { $method });
    )*};
}

macro_rules! binop {
    ($wrap:path, $overflow:path [ $lhs:expr, $rhs:expr ] $msg:expr) => {{
        let mut result = MaybeUninit::uninit();
        #[cfg(not(debug_assertions))]
        {
            $wrap(&mut result, $lhs, $rhs);
        }
        #[cfg(debug_assertions)]
        {
            let overflow = $overflow(&mut result, $lhs, $rhs);
            if overflow {
                panic!(concat!("attempt to ", $msg));
            }
        }
        unsafe { result.assume_init() }
    }};
}

macro_rules! impl_auto_binop {
    ($op:ident { $method:ident }) => {
        impl_ref_binop! {
            $op <&U256 ; &U256>::$method (rhs) {
                <U256> for &'_ U256 => { &rhs }
                <&'_ U256> for U256 => { rhs }
                <U256> for U256 => { &rhs }
            }
        }

        impl_ref_binop! {
            $op <&U256 ; U256>::$method (rhs) { u128 } => { U256::new(rhs) }
        }
    };
}

macro_rules! impl_ref_binop {
    (
        $op:ident <$ref:ty ; $tr:ty> :: $method:ident ($x:ident) {$(
            <$rhs:ty> for $lhs:ty => $conv:block
        )*}
    ) => {$(
        impl ops::$op<$rhs> for $lhs {
            type Output = U256;

            #[inline]
            fn $method(self, $x: $rhs) -> Self::Output {
                <$ref as ops::$op<$tr>>::$method(&self, $conv)
            }
        }
    )*};
    (
        $op:ident <$ref:ty ; $tr:ty> :: $method:ident ($x:ident) {
            $($rhs:ty),* $(,)?
        } => $conv:block
    ) => {$(
        impl_ref_binop! {
            $op <&U256 ; $tr>::$method (rhs) {
                <&'_ $rhs> for &'_ U256 => { let $x = *rhs; $conv }
                <&'_ $rhs> for U256 => { let $x = *rhs; $conv }
                <$rhs> for &'_ U256 => { let $x = rhs; $conv }
                <$rhs> for U256 => { let $x = rhs; $conv }
            }
        }
    )*};
}

impl_binops! {
    Add { add => add3, addc; "add with overflow" }
    Mul { mul => mul3, mulc; "multiply with overflow" }
    Sub { sub => sub3, subc; "subtract with overflow" }
}

impl ops::Div for &'_ U256 {
    type Output = U256;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        if rhs == &U256::ZERO {
            panic!("attempt to divide by zero");
        }

        let mut result = MaybeUninit::uninit();
        div3(&mut result, self, rhs);
        unsafe { result.assume_init() }
    }
}

impl_auto_binop!(Div { div });

impl ops::Rem for &'_ U256 {
    type Output = U256;

    #[inline]
    fn rem(self, rhs: Self) -> Self::Output {
        if rhs == &U256::ZERO {
            panic!("attempt to calculate the remainder with a divisor of zero");
        }

        let mut result = MaybeUninit::uninit();
        rem3(&mut result, self, rhs);
        unsafe { result.assume_init() }
    }
}

impl_auto_binop!(Rem { rem });

macro_rules! impl_shifts {
    ($(
        $op:ident {
            $method:ident =>
            $wrap:path; $msg:expr
        }
    )*) => {$(
        impl ops::$op<u32> for &'_ U256 {
            type Output = U256;

            #[inline]
            fn $method(self, rhs: u32) -> Self::Output {
                shift!($wrap [ self, rhs ] $msg)
            }
        }

        impl_ref_binop! {
            $op <&U256 ; u32>::$method (rhs) {
                <&'_ u32> for &'_ U256 => { *rhs }
                <&'_ u32> for U256 => { *rhs }
                <u32> for U256 => { rhs }
            }
        }

        impl_ref_binop! {
            $op <&U256 ; u32>::$method (rhs) { U256 } => { *rhs.low() as _ }
        }

        impl_ref_binop! {
            $op <&U256 ; u32>::$method (rhs) {
                i8, i16, i32, i64, i128, isize,
                u8, u16, u64, u128, usize,
            } => { rhs as _ }
        }
    )*};
}

macro_rules! shift {
    ($wrap:path [ $lhs:expr, $rhs:expr ] $msg:expr) => {{
        #[cfg(debug_assertions)]
        if $rhs > 0xff {
            panic!(concat!("attempt to ", $msg));
        }

        let mut result = MaybeUninit::uninit();
        $wrap(&mut result, $lhs, $rhs);

        unsafe { result.assume_init() }
    }};
}

impl_shifts! {
    Shl { shl => shl3; "shift left with overflow" }
    Shr { shr => shr3; "shift right with overflow" }
}

impl ops::Not for U256 {
    type Output = U256;

    #[inline]
    fn not(self) -> Self::Output {
        let U256([a, b]) = self;
        U256([!a, !b])
    }
}

impl ops::Not for &'_ U256 {
    type Output = U256;

    #[inline]
    fn not(self) -> Self::Output {
        let U256([a, b]) = self;
        U256([!a, !b])
    }
}

macro_rules! impl_bitwiseops {
    ($(
        $op:ident { $method:ident }
    )*) => {$(
        impl ops::$op<&'_ U256> for &'_ U256 {
            type Output = U256;

            #[inline]
            fn $method(self, rhs: &'_ U256) -> Self::Output {
                let U256([a, b]) = self;
                let U256([rhs_a, rhs_b]) = rhs;
                U256([a.$method(rhs_a), b.$method(rhs_b)])
            }
        }

        impl_auto_binop!($op { $method });
    )*};
}

impl_bitwiseops! {
    BitAnd { bitand }
    BitOr { bitor }
    BitXor { bitxor }
}

macro_rules! impl_binops_assign {
    ($(
        $op:ident {
            $method:ident =>
            $wrap:path,
            $binop:tt
        }
    )*) => {$(
        impl ops::$op<&'_ U256> for U256 {
            #[inline]
            fn $method(&mut self, rhs: &'_ U256) {
                binop_assign!($wrap, $binop [ self, rhs ])
            }
        }

        impl_auto_binop_assign!($op { $method });
    )*};
}

macro_rules! binop_assign {
    ($wrap:path, $binop:tt [ $lhs:expr, $rhs:expr ]) => {{
        #[cfg(not(debug_assertions))]
        {
            $wrap($lhs, $rhs);
        }
        #[cfg(debug_assertions)]
        {
            *($lhs) = *($lhs) $binop $rhs;
        }
    }};
}

macro_rules! impl_auto_binop_assign {
    ($op:ident { $method:ident }) => {
        impl_ref_binop_assign! {
            $op <U256 ; &U256>::$method (rhs) {
                <U256> for U256 => { &rhs }
            }
        }

        impl_ref_binop_assign! {
            $op <U256 ; U256>::$method (rhs) { u128 } => { U256::new(rhs) }
        }
    };
}

macro_rules! impl_ref_binop_assign {
    (
        $op:ident <$ref:ty ; $tr:ty> :: $method:ident ($x:ident) {$(
            <$rhs:ty> for U256 => $conv:block
        )*}
    ) => {$(
        impl ops::$op<$rhs> for U256 {
            #[inline]
            fn $method(&mut self, $x: $rhs) {
                <$ref as ops::$op<$tr>>::$method(self, $conv)
            }
        }
    )*};
    (
        $op:ident <$ref:ty ; $tr:ty> :: $method:ident ($x:ident) {
            $($rhs:ty),* $(,)?
        } => $conv:block
    ) => {$(
        impl_ref_binop_assign! {
            $op <U256 ; $tr>::$method (rhs) {
                <&'_ $rhs> for U256 => { let $x = *rhs; $conv }
                <$rhs> for U256 => { let $x = rhs; $conv }
            }
        }
    )*};
}

impl_binops_assign! {
    AddAssign { add_assign => add2, + }
    DivAssign { div_assign => div2, / }
    MulAssign { mul_assign => mul2, * }
    RemAssign { rem_assign => rem2, % }
    SubAssign { sub_assign => sub2, - }
}

macro_rules! impl_shifts_assign {
    ($(
        $op:ident {
            $method:ident =>
                $wrap:path, $sh:tt
        }
    )*) => {$(
        impl ops::$op<u32> for U256 {
            #[inline]
            fn $method(&mut self, rhs: u32) {
                binop_assign!($wrap, $sh [ self, rhs ])
            }
        }

        impl_ref_binop_assign! {
            $op <U256 ; u32>::$method (rhs) {
                <&'_ u32> for U256 => { *rhs }
            }
        }

        impl_ref_binop_assign! {
            $op <U256 ; u32>::$method (rhs) { U256 } => { *rhs.low() as _ }
        }

        impl_ref_binop_assign! {
            $op <U256 ; u32>::$method (rhs) {
                i8, i16, i32, i64, i128, isize,
                u8, u16, u64, u128, usize,
            } => { rhs as _ }
        }
    )*};
}

impl_shifts_assign! {
    ShlAssign { shl_assign => shl2, << }
    ShrAssign { shr_assign => shr2, >> }
}

macro_rules! impl_bitwiseops_assign {
    ($(
        $op:ident { $method:ident }
    )*) => {$(
        impl ops::$op<&'_ U256> for U256 {
            #[inline]
            fn $method(&mut self, rhs: &'_ U256) {
                let U256([a, b]) = self;
                let U256([rhs_a, rhs_b]) = rhs;
                a.$method(rhs_a);
                b.$method(rhs_b);
            }
        }

        impl_auto_binop_assign!($op { $method });
    )*};
}

impl_bitwiseops_assign! {
    BitAndAssign { bitand_assign }
    BitOrAssign { bitor_assign }
    BitXorAssign { bitxor_assign }
}

#[cfg(test)]
mod tests {
    use crate::U256;
    use core::ops::*;

    #[test]
    fn trait_implementations() {
        trait Implements {}
        impl Implements for U256 {}
        impl Implements for &'_ U256 {}

        fn assert_ops<T>()
        where
            for<'a> T: Implements
                + Add<&'a u128>
                + Add<&'a U256>
                + Add<u128>
                + Add<U256>
                + AddAssign<&'a u128>
                + AddAssign<&'a U256>
                + AddAssign<u128>
                + AddAssign<U256>
                + BitAnd<&'a u128>
                + BitAnd<&'a U256>
                + BitAnd<u128>
                + BitAnd<U256>
                + BitAndAssign<&'a u128>
                + BitAndAssign<&'a U256>
                + BitAndAssign<u128>
                + BitAndAssign<U256>
                + BitOr<&'a u128>
                + BitOr<&'a U256>
                + BitOr<u128>
                + BitOr<U256>
                + BitOrAssign<&'a u128>
                + BitOrAssign<&'a U256>
                + BitOrAssign<u128>
                + BitOrAssign<U256>
                + BitXor<&'a u128>
                + BitXor<&'a U256>
                + BitXor<u128>
                + BitXor<U256>
                + BitXorAssign<&'a u128>
                + BitXorAssign<&'a U256>
                + BitXorAssign<u128>
                + BitXorAssign<U256>
                + Div<&'a u128>
                + Div<&'a U256>
                + Div<u128>
                + Div<U256>
                + DivAssign<&'a u128>
                + DivAssign<&'a U256>
                + DivAssign<u128>
                + DivAssign<U256>
                + Mul<&'a u128>
                + Mul<&'a U256>
                + Mul<u128>
                + Mul<U256>
                + MulAssign<&'a u128>
                + MulAssign<&'a U256>
                + MulAssign<u128>
                + MulAssign<U256>
                + Not
                + Rem<&'a u128>
                + Rem<&'a U256>
                + Rem<u128>
                + Rem<U256>
                + RemAssign<&'a u128>
                + RemAssign<&'a U256>
                + RemAssign<u128>
                + RemAssign<U256>
                + Shl<&'a i128>
                + Shl<&'a i16>
                + Shl<&'a i32>
                + Shl<&'a i64>
                + Shl<&'a i8>
                + Shl<&'a isize>
                + Shl<&'a u128>
                + Shl<&'a u16>
                + Shl<&'a U256>
                + Shl<&'a u32>
                + Shl<&'a u64>
                + Shl<&'a u8>
                + Shl<&'a usize>
                + Shl<i128>
                + Shl<i16>
                + Shl<i32>
                + Shl<i64>
                + Shl<i8>
                + Shl<isize>
                + Shl<u128>
                + Shl<u16>
                + Shl<U256>
                + Shl<u32>
                + Shl<u64>
                + Shl<u8>
                + Shl<usize>
                + ShlAssign<&'a i128>
                + ShlAssign<&'a i16>
                + ShlAssign<&'a i32>
                + ShlAssign<&'a i64>
                + ShlAssign<&'a i8>
                + ShlAssign<&'a isize>
                + ShlAssign<&'a u128>
                + ShlAssign<&'a u16>
                + ShlAssign<&'a U256>
                + ShlAssign<&'a u32>
                + ShlAssign<&'a u64>
                + ShlAssign<&'a u8>
                + ShlAssign<&'a usize>
                + ShlAssign<i128>
                + ShlAssign<i16>
                + ShlAssign<i32>
                + ShlAssign<i64>
                + ShlAssign<i8>
                + ShlAssign<isize>
                + ShlAssign<u128>
                + ShlAssign<u16>
                + ShlAssign<U256>
                + ShlAssign<u32>
                + ShlAssign<u64>
                + ShlAssign<u8>
                + ShlAssign<usize>
                + Shr<&'a i128>
                + Shr<&'a i16>
                + Shr<&'a i32>
                + Shr<&'a i64>
                + Shr<&'a i8>
                + Shr<&'a isize>
                + Shr<&'a u128>
                + Shr<&'a u16>
                + Shr<&'a U256>
                + Shr<&'a u32>
                + Shr<&'a u64>
                + Shr<&'a u8>
                + Shr<&'a usize>
                + Shr<i128>
                + Shr<i16>
                + Shr<i32>
                + Shr<i64>
                + Shr<i8>
                + Shr<isize>
                + Shr<u128>
                + Shr<u16>
                + Shr<U256>
                + Shr<u32>
                + Shr<u64>
                + Shr<u8>
                + Shr<usize>
                + ShrAssign<&'a i128>
                + ShrAssign<&'a i16>
                + ShrAssign<&'a i32>
                + ShrAssign<&'a i64>
                + ShrAssign<&'a i8>
                + ShrAssign<&'a isize>
                + ShrAssign<&'a u128>
                + ShrAssign<&'a u16>
                + ShrAssign<&'a U256>
                + ShrAssign<&'a u32>
                + ShrAssign<&'a u64>
                + ShrAssign<&'a u8>
                + ShrAssign<&'a usize>
                + ShrAssign<i128>
                + ShrAssign<i16>
                + ShrAssign<i32>
                + ShrAssign<i64>
                + ShrAssign<i8>
                + ShrAssign<isize>
                + ShrAssign<u128>
                + ShrAssign<u16>
                + ShrAssign<U256>
                + ShrAssign<u32>
                + ShrAssign<u64>
                + ShrAssign<u8>
                + ShrAssign<usize>
                + Sub<&'a u128>
                + Sub<&'a U256>
                + Sub<u128>
                + Sub<U256>
                + SubAssign<&'a u128>
                + SubAssign<&'a U256>
                + SubAssign<u128>
                + SubAssign<U256>,
            for<'a> &'a T: Implements
                + Add<&'a u128>
                + Add<&'a U256>
                + Add<u128>
                + Add<U256>
                + BitAnd<&'a u128>
                + BitAnd<&'a U256>
                + BitAnd<u128>
                + BitAnd<U256>
                + BitOr<&'a u128>
                + BitOr<&'a U256>
                + BitOr<u128>
                + BitOr<U256>
                + BitXor<&'a u128>
                + BitXor<&'a U256>
                + BitXor<u128>
                + BitXor<U256>
                + Div<&'a u128>
                + Div<&'a U256>
                + Div<u128>
                + Div<U256>
                + Mul<&'a u128>
                + Mul<&'a U256>
                + Mul<u128>
                + Mul<U256>
                + Not
                + Rem<&'a u128>
                + Rem<&'a U256>
                + Rem<u128>
                + Rem<U256>
                + Shl<&'a i128>
                + Shl<&'a i16>
                + Shl<&'a i32>
                + Shl<&'a i64>
                + Shl<&'a i8>
                + Shl<&'a isize>
                + Shl<&'a u128>
                + Shl<&'a u16>
                + Shl<&'a U256>
                + Shl<&'a u32>
                + Shl<&'a u64>
                + Shl<&'a u8>
                + Shl<&'a usize>
                + Shl<i128>
                + Shl<i16>
                + Shl<i32>
                + Shl<i64>
                + Shl<i8>
                + Shl<isize>
                + Shl<u128>
                + Shl<u16>
                + Shl<U256>
                + Shl<u32>
                + Shl<u64>
                + Shl<u8>
                + Shl<usize>
                + Shr<&'a i128>
                + Shr<&'a i16>
                + Shr<&'a i32>
                + Shr<&'a i64>
                + Shr<&'a i8>
                + Shr<&'a isize>
                + Shr<&'a u128>
                + Shr<&'a u16>
                + Shr<&'a U256>
                + Shr<&'a u32>
                + Shr<&'a u64>
                + Shr<&'a u8>
                + Shr<&'a usize>
                + Shr<i128>
                + Shr<i16>
                + Shr<i32>
                + Shr<i64>
                + Shr<i8>
                + Shr<isize>
                + Shr<u128>
                + Shr<u16>
                + Shr<U256>
                + Shr<u32>
                + Shr<u64>
                + Shr<u8>
                + Shr<usize>
                + Sub<&'a u128>
                + Sub<&'a U256>
                + Sub<u128>
                + Sub<U256>,
        {
        }

        assert_ops::<U256>();
    }
}
