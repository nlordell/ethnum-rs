//! Module with comparison implementations for `U256`.
//!
//! `PartialEq` and `PartialOrd` implementations for `u128` are also provided
//! to allow notation such as:
//!
//! ```
//! # use ethnum::U256;
//! assert_eq!(U256::new(42), 42);
//! assert!(U256::ONE > 0 && U256::ZERO == 0);
//! ```

use crate::U256;
use core::cmp::Ordering;

impl Ord for U256 {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.high().cmp(other.high()) {
            Ordering::Equal => self.low().cmp(other.low()),
            ordering => ordering,
        }
    }
}

impl PartialOrd for U256 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq<u128> for U256 {
    #[inline]
    fn eq(&self, other: &u128) -> bool {
        *self.high() == 0 && self.low() == other
    }
}

impl PartialOrd<u128> for U256 {
    #[inline]
    fn partial_cmp(&self, rhs: &u128) -> Option<Ordering> {
        Some(if *self.high() == 0 {
            self.low().cmp(rhs)
        } else {
            Ordering::Greater
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::U256;
    use core::cmp::Ordering;

    #[test]
    fn cmp() {
        // 1e38
        let x = U256::from_words(0, 100000000000000000000000000000000000000);
        // 1e48
        let y = U256::from_words(2938735877, 18960114910927365649471927446130393088);
        assert!(x < y);
        assert_eq!(x.cmp(&y), Ordering::Less);
    }
}
