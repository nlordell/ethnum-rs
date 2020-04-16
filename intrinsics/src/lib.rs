//! This crate contains LLVM generated intrinsics for 256-bit unsigned integer
//! operations.

#![no_std]

use core::mem::MaybeUninit;

pub type U256 = [u128; 2];

macro_rules! def {
    ($(
        $(#[$a:meta])*
        pub fn $name:ident(
            $($p:ident : $t:ty),*
        ) $(-> $ret:ty)?;
    )*) => {
        #[allow(improper_ctypes)]
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
    pub fn add2(r: &mut U256, a: &U256);
    pub fn add3(r: &mut MaybeUninit<U256>, a: &U256, b: &U256);
    pub fn addc(r: &mut MaybeUninit<U256>, a: &U256, b: &U256) -> bool;

    pub fn mul2(r: &mut U256, a: &U256);
    pub fn mul3(r: &mut MaybeUninit<U256>, a: &U256, b: &U256);
    pub fn mulc(r: &mut MaybeUninit<U256>, a: &U256, b: &U256) -> bool;

    pub fn sub2(r: &mut U256, a: &U256);
    pub fn sub3(r: &mut MaybeUninit<U256>, a: &U256, b: &U256);
    pub fn subc(r: &mut MaybeUninit<U256>, a: &U256, b: &U256) -> bool;

    pub fn shl2(r: &mut U256, a: u32);
    pub fn shl3(r: &mut MaybeUninit<U256>, a: &U256, b: u32);

    pub fn shr2(r: &mut U256, a: u32);
    pub fn shr3(r: &mut MaybeUninit<U256>, a: &U256, b: u32);

    pub fn rotate_left(r: &mut MaybeUninit<U256>, a: &U256, b: u32);
    pub fn rotate_right(r: &mut MaybeUninit<U256>, a: &U256, b: u32);

    pub fn ctlz(a: &U256) -> u32;
    pub fn cttz(a: &U256) -> u32;
}
