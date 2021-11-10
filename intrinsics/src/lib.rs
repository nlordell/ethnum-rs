//! This crate contains LLVM generated intrinsics for 256-bit unsigned integer
//! operations.

#![no_std]

use core::mem::MaybeUninit;

/// Opaque type used as parameter to intriniscs.
///
/// Guaranteed to have a memory layout compatible with `ethnum::{I256, U256}`.
#[repr(C)]
pub struct I256 {
    _i: [u64; 4],
}

macro_rules! def {
    ($(
        $(#[$a:meta])*
        pub fn $name:ident(
            $($p:ident : $t:ty),*
        ) $(-> $ret:ty)?;
    )*) => {
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

def! {
    pub fn add2(r: &mut I256, a: &I256);
    pub fn add3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    pub fn uaddc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;
    pub fn iaddc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;

    pub fn umul2(r: &mut I256, a: &I256);
    pub fn umul3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    pub fn umulc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;
    pub fn imul2(r: &mut I256, a: &I256);
    pub fn imul3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    //pub fn imulc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;

    pub fn sub2(r: &mut I256, a: &I256);
    pub fn sub3(r: &mut MaybeUninit<I256>, a: &I256, b: &I256);
    pub fn usubc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;
    pub fn isubc(r: &mut MaybeUninit<I256>, a: &I256, b: &I256) -> bool;

    pub fn shl2(r: &mut I256, a: u32);
    pub fn shl3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);

    pub fn sar2(r: &mut I256, a: u32);
    pub fn sar3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);
    pub fn shr2(r: &mut I256, a: u32);
    pub fn shr3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);

    pub fn rol3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);
    pub fn ror3(r: &mut MaybeUninit<I256>, a: &I256, b: u32);

    pub fn ctlz(a: &I256) -> u32;
    pub fn cttz(a: &I256) -> u32;
}
