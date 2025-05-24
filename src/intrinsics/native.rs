//! This module contains native implementations for intrinsics. These are used
//! when generated IR intrinsics are disabled.

mod add;
mod ctz;
mod divmod;
mod divmod_impl;
mod mul;
mod rot;
mod shl;
mod shr;
mod sub;

pub use self::{add::*, ctz::*, divmod::*, divmod_impl::*, mul::*, rot::*, shl::*, shr::*, sub::*};
