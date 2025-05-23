//! This module contains native implementations for intrinsics. These are used
//! when generated IR intrinsics are disabled.

mod add;
mod ctz;
mod divmod;
mod divmod_shared;
mod mul;
mod rot;
mod shl;
mod shr;
mod sub;

pub use self::{
    add::*, ctz::*, divmod::*, divmod_shared::*, mul::*, rot::*, shl::*, shr::*, sub::*,
};
