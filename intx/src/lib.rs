pub mod div128;

#[repr(C)]
pub struct Uint256 {
    words: [u64; 4],
}

pub fn udivmod256(u: &Uint256, v: &Uint256) -> (Uint256, Uint256) {
    let r = unsafe { ffi::intx_udivmod256(u, v) };
    (r.quot, r.rem)
}

mod ffi {
    use super::Uint256;

    #[repr(C)]
    pub struct DivResult256 {
        pub quot: Uint256,
        pub rem: Uint256,
    }

    extern "C" {
        pub fn intx_udivmod256(u: *const Uint256, v: *const Uint256) -> DivResult256;
    }
}
