//! Module contains iterator specific trait implementations.

use crate::U256;
use core::iter::{Product, Sum};
use core::ops::{Add, Mul};

impl Sum for U256 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(U256::ZERO, Add::add)
    }
}

impl Product for U256 {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(U256::ONE, Mul::mul)
    }
}

impl<'a> Sum<&'a U256> for U256 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(U256::ZERO, Add::add)
    }
}

impl<'a> Product<&'a U256> for U256 {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(U256::ONE, Mul::mul)
    }
}

// TODO(nlordell): Implement `core::iter::Step` once it stabilizes.
