//! Serde serialization implementation for 256-bit integer types.
//!
//! This implementation is very JSON-centric in that it serializes the integer
//! types as `QUANTITIES` as specified in the Ethereum RPC. That is, integers
//! are encoded as `"0x"` prefixed strings without extrenuous leading `0`s. For
//! negative signed integers, the string is prefixed with a `"-"` sign.
//!
//! Note that this module contains alternative serialization schemes that can
//! be used with `#[serde(with = "...")]`.
//!
//! TODO(nlordell): example!

use crate::{int::I256, uint::U256};
use core::{
    fmt::{self, Display, Formatter, Write},
    mem::MaybeUninit,
    ptr, slice, str,
};
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

impl Serialize for I256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut f = FormatBuffer::hex();
        write!(f, "{self:-#x}").expect("unexpected formatting failure");
        serializer.serialize_str(f.as_str())
    }
}

impl Serialize for U256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut f = FormatBuffer::hex();
        write!(f, "{self:#x}").expect("unexpected formatting failure");
        serializer.serialize_str(f.as_str())
    }
}

impl<'de> Deserialize<'de> for I256 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(FormatVisitor(Self::from_str_hex))
    }
}

impl<'de> Deserialize<'de> for U256 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(FormatVisitor(Self::from_str_hex))
    }
}

/// Module for use with `#[serde(with = "ethnum::serde::decimal")]` to specify
/// decimal string serialization for 256-bit integer types.
pub mod decimal {
    use super::*;
    use core::num::ParseIntError;

    #[doc(hidden)]
    pub trait Decimal: Sized {
        fn from_str_decimal(src: &str) -> Result<Self, ParseIntError>;
        fn write_decimal(&self, f: &mut impl Write);
    }

    impl Decimal for I256 {
        fn from_str_decimal(src: &str) -> Result<Self, ParseIntError> {
            Self::from_str_radix(src, 10)
        }
        fn write_decimal(&self, f: &mut impl Write) {
            write!(f, "{self}").expect("unexpected formatting error")
        }
    }

    impl Decimal for U256 {
        fn from_str_decimal(src: &str) -> Result<Self, ParseIntError> {
            Self::from_str_radix(src, 10)
        }
        fn write_decimal(&self, f: &mut impl Write) {
            write!(f, "{self}").expect("unexpected formatting error")
        }
    }

    #[doc(hidden)]
    pub fn serialize<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        T: Decimal,
        S: Serializer,
    {
        let mut f = FormatBuffer::decimal();
        value.write_decimal(&mut f);
        serializer.serialize_str(f.as_str())
    }

    #[doc(hidden)]
    pub fn deserialize<'de, T, D>(deserializer: D) -> Result<T, D::Error>
    where
        T: Decimal,
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(FormatVisitor(T::from_str_decimal))
    }
}

/// Module for use with `#[serde(with = "ethnum::serde::prexied")]` to specify
/// prefixed string serialization for 256-bit integer types.
///
/// This allows serialization to look for an optional `0x` prefix to determine
/// if it is a hexadecimal string or decimal string.
pub mod prefixed {
    use super::*;
    use core::num::ParseIntError;

    #[doc(hidden)]
    pub trait Prefixed: Serialize + Sized {
        fn from_str_prefixed(src: &str) -> Result<Self, ParseIntError>;
    }

    impl Prefixed for I256 {
        fn from_str_prefixed(src: &str) -> Result<Self, ParseIntError> {
            Self::from_str_prefixed(src)
        }
    }

    impl Prefixed for U256 {
        fn from_str_prefixed(src: &str) -> Result<Self, ParseIntError> {
            Self::from_str_prefixed(src)
        }
    }

    #[doc(hidden)]
    pub fn serialize<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        T: Prefixed,
        S: Serializer,
    {
        value.serialize(serializer)
    }

    #[doc(hidden)]
    pub fn deserialize<'de, T, D>(deserializer: D) -> Result<T, D::Error>
    where
        T: Prefixed,
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(FormatVisitor(T::from_str_prefixed))
    }
}

/// Internal visitor struct implementation to facilitate implementing different
/// serialization formats.
struct FormatVisitor<F>(F);

impl<'de, T, E, F> Visitor<'de> for FormatVisitor<F>
where
    E: Display,
    F: FnOnce(&str) -> Result<T, E>,
{
    type Value = T;

    fn expecting(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("a formatted 256-bit integer")
    }

    fn visit_str<E_>(self, v: &str) -> Result<Self::Value, E_>
    where
        E_: de::Error,
    {
        self.0(v).map_err(de::Error::custom)
    }

    fn visit_bytes<E_>(self, v: &[u8]) -> Result<Self::Value, E_>
    where
        E_: de::Error,
    {
        let string = str::from_utf8(v)
            .map_err(|_| de::Error::invalid_value(de::Unexpected::Bytes(v), &self))?;
        self.visit_str(string)
    }
}

/// A stack-allocated buffer that can be used for writing formatted strings.
///
/// This allows us to leverage existing `fmt` implementations on integer types
/// without requiring heap allocations (i.e. writing to a `String` buffer).
struct FormatBuffer<const N: usize> {
    offset: usize,
    buffer: [MaybeUninit<u8>; N],
}

impl<const N: usize> FormatBuffer<N> {
    /// Creates a new formatting buffer.
    fn new() -> Self {
        Self {
            offset: 0,
            buffer: [MaybeUninit::uninit(); N],
        }
    }

    /// Returns a `str` to the currently written data.
    fn as_str(&self) -> &str {
        // SAFETY: We only ever write valid UTF-8 strings to the buffer, so the
        // resulting string will always be valid.
        unsafe {
            let buffer = slice::from_raw_parts(self.buffer[0].as_ptr(), self.offset);
            str::from_utf8_unchecked(buffer)
        }
    }
}

impl FormatBuffer<78> {
    /// Allocates a formatting buffer large enough to hold any possible decimal
    /// encoded 256-bit value.
    fn decimal() -> Self {
        Self::new()
    }
}

impl FormatBuffer<67> {
    /// Allocates a formatting buffer large enough to hold any possible
    /// hexadecimal encoded 256-bit value.
    fn hex() -> Self {
        Self::new()
    }
}

impl<const N: usize> Write for FormatBuffer<N> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let end = self.offset.checked_add(s.len()).ok_or(fmt::Error)?;

        // Make sure there is enough space in the buffer.
        if end > N {
            return Err(fmt::Error);
        }

        // SAFETY: We checked that there is enough space in the buffer to fit
        // the string `s` starting from `offset`, and the pointers cannot be
        // overlapping because of Rust ownership semantics (i.e. `s` cannot
        // overlap with `buffer` because we have a mutable reference to `self`
        // and by extension `buffer`).
        unsafe {
            let buffer = self.buffer[0].as_mut_ptr().add(self.offset);
            ptr::copy_nonoverlapping(s.as_ptr(), buffer, s.len());
        }
        self.offset = end;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{
        boxed::Box,
        fmt::{Display, LowerHex},
        format,
        string::String,
    };
    use serde::{
        de::value::{self, BorrowedStrDeserializer},
        ser::Impossible,
    };

    #[test]
    fn serialize_integers() {
        macro_rules! ser {
            ($method:expr, $value:expr) => {{
                let value = $value;
                ($method)(&value, StringSerializer).unwrap()
            }};
        }

        assert_eq!(
            ser!(I256::serialize, I256::MIN),
            "-0x8000000000000000000000000000000000000000000000000000000000000000",
        );
        assert_eq!(ser!(I256::serialize, I256::new(-1)), "-0x1");
        assert_eq!(ser!(I256::serialize, I256::new(0)), "0x0");
        assert_eq!(ser!(I256::serialize, I256::new(42)), "0x2a");

        assert_eq!(ser!(U256::serialize, U256::new(0)), "0x0");
        assert_eq!(ser!(U256::serialize, U256::new(4919)), "0x1337");
        assert_eq!(
            ser!(U256::serialize, U256::MAX),
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        );

        assert_eq!(
            ser!(decimal::serialize, I256::MIN),
            "-57896044618658097711785492504343953926634992332820282019728792003956564819968",
        );
        assert_eq!(ser!(decimal::serialize, I256::new(-1)), "-1");
        assert_eq!(ser!(decimal::serialize, I256::new(0)), "0");
        assert_eq!(ser!(decimal::serialize, I256::new(42)), "42");

        assert_eq!(ser!(decimal::serialize, U256::new(0)), "0");
        assert_eq!(ser!(decimal::serialize, U256::new(4919)), "4919");
        assert_eq!(
            ser!(decimal::serialize, U256::MAX),
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
        );
    }

    #[test]
    fn deserialize_integers() {
        macro_rules! de {
            ($method:expr, $src:literal) => {{
                let deserializer = BorrowedStrDeserializer::<value::Error>::new($src);
                ($method)(deserializer).unwrap()
            }};
        }

        assert_eq!(
            de!(
                I256::deserialize,
                "-0x8000000000000000000000000000000000000000000000000000000000000000"
            ),
            I256::MIN
        );
        assert_eq!(de!(I256::deserialize, "-0x1337"), I256::new(-4919));
        assert_eq!(de!(I256::deserialize, "0x0"), I256::new(0));
        assert_eq!(de!(I256::deserialize, "0x2a"), I256::new(42));
        assert_eq!(de!(I256::deserialize, "0x2A"), I256::new(42));

        assert_eq!(de!(U256::deserialize, "0x0"), U256::new(0));
        assert_eq!(de!(U256::deserialize, "0x2a"), U256::new(42));
        assert_eq!(de!(U256::deserialize, "0x2A"), U256::new(42));
        assert_eq!(
            de!(
                U256::deserialize,
                "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            ),
            U256::MAX
        );

        assert_eq!(
            de!(
                decimal::deserialize::<I256, _>,
                "-57896044618658097711785492504343953926634992332820282019728792003956564819968"
            ),
            I256::MIN
        );
        assert_eq!(de!(decimal::deserialize::<I256, _>, "-1"), I256::new(-1));
        assert_eq!(de!(decimal::deserialize::<I256, _>, "0"), I256::new(0));
        assert_eq!(de!(decimal::deserialize::<I256, _>, "42"), I256::new(42));

        assert_eq!(de!(decimal::deserialize::<U256, _>, "0"), U256::new(0));
        assert_eq!(de!(decimal::deserialize::<U256, _>, "42"), U256::new(42));
        assert_eq!(
            de!(
                decimal::deserialize::<U256, _>,
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            U256::MAX
        );

        assert_eq!(de!(prefixed::deserialize::<I256, _>, "-1"), I256::new(-1));
        assert_eq!(de!(prefixed::deserialize::<I256, _>, "-0x1"), I256::new(-1));
        assert_eq!(de!(prefixed::deserialize::<I256, _>, "42"), I256::new(42));
        assert_eq!(de!(prefixed::deserialize::<I256, _>, "0x2a"), I256::new(42));
        assert_eq!(de!(prefixed::deserialize::<I256, _>, "0x2A"), I256::new(42));

        assert_eq!(de!(prefixed::deserialize::<U256, _>, "42"), U256::new(42));
        assert_eq!(de!(prefixed::deserialize::<U256, _>, "0x2a"), U256::new(42));
        assert_eq!(de!(prefixed::deserialize::<U256, _>, "0x2A"), U256::new(42));
    }

    #[test]
    fn formatting_buffer() {
        for value in [
            Box::new(I256::MIN) as Box<dyn Display>,
            Box::new(I256::MAX),
            Box::new(U256::MIN),
            Box::new(U256::MAX),
        ] {
            let mut f = FormatBuffer::decimal();
            write!(f, "{value}").unwrap();
            assert_eq!(f.as_str(), format!("{value}"));
        }

        for value in [
            Box::new(I256::MIN) as Box<dyn LowerHex>,
            Box::new(I256::MAX),
            Box::new(U256::MIN),
            Box::new(U256::MAX),
        ] {
            let mut f = FormatBuffer::hex();
            let value = &*value;
            write!(f, "{value:-#x}").unwrap();
            assert_eq!(f.as_str(), format!("{value:-#x}"));
        }
    }

    /// A string serializer used for testing.
    struct StringSerializer;

    impl Serializer for StringSerializer {
        type Ok = String;
        type Error = fmt::Error;
        type SerializeSeq = Impossible<String, fmt::Error>;
        type SerializeTuple = Impossible<String, fmt::Error>;
        type SerializeTupleStruct = Impossible<String, fmt::Error>;
        type SerializeTupleVariant = Impossible<String, fmt::Error>;
        type SerializeMap = Impossible<String, fmt::Error>;
        type SerializeStruct = Impossible<String, fmt::Error>;
        type SerializeStructVariant = Impossible<String, fmt::Error>;
        fn serialize_bool(self, _: bool) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_i8(self, _: i8) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_i16(self, _: i16) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_i32(self, _: i32) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_i64(self, _: i64) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_u8(self, _: u8) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_u16(self, _: u16) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_u32(self, _: u32) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_u64(self, _: u64) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_f32(self, _: f32) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_f64(self, _: f64) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_char(self, _: char) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
            Ok(v.into())
        }
        fn serialize_bytes(self, _: &[u8]) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_some<T: ?Sized>(self, _: &T) -> Result<Self::Ok, Self::Error>
        where
            T: Serialize,
        {
            unimplemented!()
        }
        fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_unit_struct(self, _: &'static str) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_unit_variant(
            self,
            _: &'static str,
            _: u32,
            _: &'static str,
        ) -> Result<Self::Ok, Self::Error> {
            unimplemented!()
        }
        fn serialize_newtype_struct<T: ?Sized>(
            self,
            _: &'static str,
            _: &T,
        ) -> Result<Self::Ok, Self::Error>
        where
            T: Serialize,
        {
            unimplemented!()
        }
        fn serialize_newtype_variant<T: ?Sized>(
            self,
            _: &'static str,
            _: u32,
            _: &'static str,
            _: &T,
        ) -> Result<Self::Ok, Self::Error>
        where
            T: Serialize,
        {
            unimplemented!()
        }
        fn serialize_seq(self, _: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
            unimplemented!()
        }
        fn serialize_tuple(self, _: usize) -> Result<Self::SerializeTuple, Self::Error> {
            unimplemented!()
        }
        fn serialize_tuple_struct(
            self,
            _: &'static str,
            _: usize,
        ) -> Result<Self::SerializeTupleStruct, Self::Error> {
            unimplemented!()
        }
        fn serialize_tuple_variant(
            self,
            _: &'static str,
            _: u32,
            _: &'static str,
            _: usize,
        ) -> Result<Self::SerializeTupleVariant, Self::Error> {
            unimplemented!()
        }
        fn serialize_map(self, _: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
            unimplemented!()
        }
        fn serialize_struct(
            self,
            _: &'static str,
            _: usize,
        ) -> Result<Self::SerializeStruct, Self::Error> {
            unimplemented!()
        }
        fn serialize_struct_variant(
            self,
            _: &'static str,
            _: u32,
            _: &'static str,
            _: usize,
        ) -> Result<Self::SerializeStructVariant, Self::Error> {
            unimplemented!()
        }
        fn collect_str<T>(self, _: &T) -> Result<Self::Ok, Self::Error>
        where
            T: Display + ?Sized,
        {
            todo!()
        }
    }
}
