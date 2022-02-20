//! Reference implementation based on `num` crate.

use crate::conv::{self, Int};

macro_rules! impl_ref {
    ($(
        pub fn $name:ident($a:ident : Int, $b:ident : Int) -> (Int, bool) $body:block
    )*) => {$(
        pub fn $name<T>(a: T, b: T) -> (T, bool)
        where
            T: Int,
        {
            let $a = conv::to_bigint(&a);
            let $b = conv::to_bigint(&b);
            let result = { $body };
            conv::from_bigint(&result)
        }
    )*};
}

impl_ref! {
    pub fn overflowing_add(a: Int, b: Int) -> (Int, bool) {
        a + b
    }
}
