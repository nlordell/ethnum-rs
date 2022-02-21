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
}

#[derive(Arbitrary, Debug)]
pub enum Op {
    Add(Num, Num),
    Sub(Num, Num),
    Mul(Num, Num),
    Div(Num, Num),
    Rem(Num, Num),
}

#[derive(Arbitrary, Debug)]
pub struct Num(u128, u128);

impl Num {
    fn is_zero(&self) -> bool {
        self.0 == 0 && self.1 == 0
    }
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
            Op::Div(a, b) => {
                if !b.is_zero() {
                    assert_op!(a, b, $as, overflowing_div)
                }
            }
            Op::Rem(a, b) => {
                if !b.is_zero() {
                    assert_op!(a, b, $as, overflowing_rem)
                }
            }
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
    match target {
        Target::Signed(op) => ops!(op, as_i256),
        Target::Unsigned(op) => ops!(op, as_u256),
    }

    Ok(())
}
