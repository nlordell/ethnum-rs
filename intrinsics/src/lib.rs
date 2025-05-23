//! This crate contains C intrinsics for 256-bit integer operations.

#![no_std]

use core::mem::MaybeUninit;

/// Opaque type used as parameter to intriniscs.
///
/// Guaranteed to have a memory layout compatible with `ethnum::{I256, I256}`.
#[repr(C, align(8))]
pub struct I256([u8; 32]);

macro_rules! def {
    ($(
        $(#[$a:meta])*
        pub fn $name:ident(
            $($p:ident : $t:ty),*
        ) $(-> $ret:ty)?;
    )*) => {
        #[link(name = "intrinsics", kind = "static")]
        extern "C" {$(
            link! {
                concat!("__ethnum_", stringify!($name));
                pub fn $name(
                    $($p: $t,)*
                ) $(-> $ret)?;
            }
        )*}
    };
}

macro_rules! link {
    ($sym:expr; $fn:item) => {
        #[link_name = $sym]
        $fn
    };
}

// Keep in sync with `src/intrinsics/intrinsics.rs`.
def! {
    pub fn add2(r: &mut I256, a: &I256);
    pub fn add3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    pub fn uaddc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;
    pub fn iaddc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;

    pub fn sub2(r: &mut I256, a: &I256);
    pub fn sub3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    pub fn usubc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;
    pub fn isubc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;

    pub fn mul2(r: &mut I256, a: &I256);
    pub fn mul3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    pub fn umulc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;
    pub fn imulc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;

    pub fn udiv2(r: &mut I256, a: &I256);
    pub fn udiv3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    pub fn urem2(r: &mut I256, a: &I256);
    pub fn urem3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);

    pub fn idiv2(r: &mut I256, a: &I256);
    pub fn idiv3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    pub fn irem2(r: &mut I256, a: &I256);
    pub fn irem3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);

    pub fn shl2(r: &mut I256, a: u32);
    pub fn shl3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);

    pub fn sar2(r: &mut I256, a: u32);
    pub fn sar3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);
    pub fn shr2(r: &mut I256, a: u32);
    pub fn shr3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);

    pub fn rol3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);
    pub fn ror3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);

    pub fn clz(a: &I256) -> u32;
    pub fn ctz(a: &I256) -> u32;
}
