mod conv;
mod reference;

use arbitrary::{Arbitrary, Unstructured};
use ethnum::{AsI256, AsU256, I256, U256};
use std::error::Error;

#[derive(Arbitrary, Debug)]
pub enum Target {
    Signed(Op),
    Unsigned(Op),
}

impl Target {
    /// Gets the target to execute from bytes.
    pub fn load(data: &[u8]) -> Result<Target, Box<dyn Error>> {
        let target = Target::arbitrary_take_rest(Unstructured::new(data))?;
        Ok(target)
    }

    fn is_interesting(&self) -> bool {
        match self {
            // Dividing by 0 always errors (and we have unit tests for it) so no
            // need to fuzz for it.
            Target::Signed(op) | Target::Unsigned(op)
                if matches!(op, Op::Div(_, Num::ZERO) | Op::Rem(_, Num::ZERO)) =>
            {
                false
            }

            // `I256::MIN % -1` reports an overflow (the same is true for
            // primitive tytes `i8::MIN % -1`) but does not overflow in the
            // reference implementation (since the result doesn't overflow).
            Target::Signed(Op::Rem(Num::IMIN, Num::UMAX)) => false,

            _ => true,
        }
    }
}

#[derive(Arbitrary, Debug)]
pub enum Op {
    Add(Num, Num),
    Sub(Num, Num),
    Mul(Num, Num),
    Div(Num, Num),
    Rem(Num, Num),
}

#[derive(Arbitrary, Debug, Eq, PartialEq)]
pub struct Num(u128, u128);

impl Num {
    const ZERO: Self = Self(0, 0);
    const IMIN: Self = Self(i128::MIN as _, 0);
    const UMAX: Self = Self(u128::MAX, u128::MAX);
}

impl AsU256 for Num {
    fn as_u256(self) -> ethnum::U256 {
        U256::from_words(self.0, self.1)
    }
}

impl AsI256 for Num {
    fn as_i256(self) -> ethnum::I256 {
        I256::from_words(self.0 as _, self.1 as _)
    }
}

macro_rules! ops {
    ($op:expr, $as:ident) => {{
        match $op {
            Op::Add(a, b) => assert_op!(a, b, $as, overflowing_add),
            Op::Sub(a, b) => assert_op!(a, b, $as, overflowing_sub),
            Op::Mul(a, b) => assert_op!(a, b, $as, overflowing_mul),
            Op::Div(a, b) => assert_op!(a, b, $as, overflowing_div),
            Op::Rem(a, b) => assert_op!(a, b, $as, overflowing_rem),
        }
    }};
}

macro_rules! assert_op {
    ($a:expr, $b:expr, $as:ident, $name:ident) => {{
        let a = $a.$as();
        let b = $b.$as();
        assert_eq!(a.$name(b), reference::$name(a, b));
    }};
}

/// The AFL fuzzing target funtion.
pub fn fuzz(data: &[u8]) -> Result<(), Box<dyn Error>> {
    let target = Target::load(data)?;
    if target.is_interesting() {
        match target {
            Target::Signed(op) => ops!(op, as_i256),
            Target::Unsigned(op) => ops!(op, as_u256),
        }
    }

    Ok(())
}
