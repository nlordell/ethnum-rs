//! Module with comparison implementations for `I256`.
//!
//! `PartialEq` and `PartialOrd` implementations for `i128` are also provided
//! to allow notation such as:
//!
//! ```
//! # use ethnum::I256;
//! assert_eq!(I256::new(42), 42);
//! assert_eq!(42, I256::new(42));
//! assert!(I256::ONE > 0 && I256::ZERO == 0);
//! assert!(0 < I256::ONE && 0 == I256::ZERO);
//! ```

use super::I256;
use core::cmp::Ordering;

impl Ord for I256 {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.high().cmp(other.high()) {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => {
                let (a, b) = if self.high().is_positive() {
                    (self, other)
                } else {
                    (other, self)
                };
                (*a.low() as u128).cmp(&(*b.low() as u128))
            }
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl_cmp! {
    impl Cmp for I256 (i128);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cmp() {
        // 1e38
        let x = I256::from_words(0, 100000000000000000000000000000000000000);
        // 1e48
        let y = I256::from_words(2938735877, 18960114910927365649471927446130393088);
        assert!(x < y);
        assert_eq!(x.cmp(&y), Ordering::Less);
        assert!(y > x);
        assert_eq!(y.cmp(&x), Ordering::Greater);

        let x = I256::new(100);
        let y = I256::new(100);
        assert!(x <= y);
        assert_eq!(x.cmp(&y), Ordering::Equal);

        assert!(I256::MAX > I256::MIN);
        assert!(I256::MIN < I256::MAX);
    }
}
