use crate::U256;
use scale::{
    Compact, CompactAs, Decode, Encode, EncodeAsRef, EncodeLike, Error, HasCompact, Input,
    MaxEncodedLen, Output,
};

impl Encode for U256 {
    fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
        self.to_le_bytes().using_encoded(f)
    }
}

impl Decode for U256 {
    fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
        <[u8; 32]>::decode(input).map(Self::from_le_bytes)
    }
}

impl MaxEncodedLen for U256 {
    fn max_encoded_len() -> usize {
        ::core::mem::size_of::<U256>()
    }
}

impl HasCompact for U256 {
    type Type = CompactU256;
}

#[derive(Eq, PartialEq, Clone, Copy, Ord, PartialOrd)]
pub struct CompactU256(pub U256);

impl From<U256> for CompactU256 {
    fn from(v: U256) -> Self {
        Self(v)
    }
}

impl From<CompactU256> for U256 {
    fn from(v: CompactU256) -> Self {
        v.0
    }
}

#[derive(Eq, PartialEq, Clone, Copy, Ord, PartialOrd)]
pub struct CompactRefU256<'a>(pub &'a U256);

impl<'a> From<&'a U256> for CompactRefU256<'a> {
    fn from(v: &'a U256) -> Self {
        Self(v)
    }
}

impl<'a> EncodeAsRef<'a, U256> for CompactU256 {
    type RefType = CompactRefU256<'a>;
}

impl<'a> EncodeLike for CompactRefU256<'a> {}

impl<'a> Encode for CompactRefU256<'a> {
    fn size_hint(&self) -> usize {
        match (self.0.high(), self.0.low()) {
            (0, 0..=0b0011_1111) => 1,
            (0, 0..=0b0011_1111_1111_1111) => 2,
            (0, 0..=0b0011_1111_1111_1111_1111_1111_1111_1111) => 4,
            _ => (32 - self.0.leading_zeros() / 8) as usize + 1,
        }
    }

    fn encode_to<T: Output + ?Sized>(&self, dest: &mut T) {
        match (self.0.high(), self.0.low()) {
            (0, 0..=0b0011_1111) => dest.push_byte((self.0.as_u8()) << 2),
            (0, 0..=0b0011_1111_1111_1111) => (((self.0.as_u16()) << 2) | 0b01).encode_to(dest),
            (0, 0..=0b0011_1111_1111_1111_1111_1111_1111_1111) => {
                (((self.0.as_u32()) << 2) | 0b10).encode_to(dest)
            }
            _ => {
                let bytes_needed = 32 - self.0.leading_zeros() / 8;
                assert!(
                    bytes_needed >= 4,
                    "Previous match arm matches anyting less than 2^30; qed"
                );
                dest.push_byte(0b11 + ((bytes_needed - 4) << 2) as u8);
                let mut v = *self.0;
                for _ in 0..bytes_needed {
                    dest.push_byte(v.as_u8());
                    v >>= 8;
                }
                assert_eq!(
                    v, 0,
                    "shifted sufficient bits right to lead only leading zeros; qed"
                )
            }
        }
    }
}

impl<'a> MaxEncodedLen for CompactRefU256<'a> {
    fn max_encoded_len() -> usize {
        33
    }
}

/// Prefix another input with a byte.
struct PrefixInput<'a, T> {
    prefix: Option<u8>,
    input: &'a mut T,
}

impl<'a, T: 'a + Input> Input for PrefixInput<'a, T> {
    fn remaining_len(&mut self) -> Result<Option<usize>, Error> {
        let len = if let Some(len) = self.input.remaining_len()? {
            Some(len.saturating_add(self.prefix.iter().count()))
        } else {
            None
        };
        Ok(len)
    }

    fn read(&mut self, buffer: &mut [u8]) -> Result<(), Error> {
        match self.prefix.take() {
            Some(v) if !buffer.is_empty() => {
                buffer[0] = v;
                self.input.read(&mut buffer[1..])
            }
            _ => self.input.read(buffer),
        }
    }
}

impl Decode for CompactU256 {
    fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
        let prefix = input.read_byte()?;
        Ok(Self(match prefix % 4 {
            0 => U256::from(prefix) >> 2,
            1 => {
                let x = u16::decode(&mut PrefixInput {
                    prefix: Some(prefix),
                    input,
                })? >> 2;
                if x > 0b0011_1111 && x <= 0b0011_1111_1111_1111 {
                    U256::from(x)
                } else {
                    return Err(U256_OUT_OF_RANGE.into());
                }
            }
            2 => {
                let x = u32::decode(&mut PrefixInput {
                    prefix: Some(prefix),
                    input,
                })? >> 2;
                if x > 0b0011_1111_1111_1111 && x <= u32::max_value() >> 2 {
                    U256::from(x)
                } else {
                    return Err(U256_OUT_OF_RANGE.into());
                }
            }
            _ => match (prefix >> 2) + 4 {
                4 => {
                    let x = u32::decode(input)?;
                    if x > u32::max_value() >> 2 {
                        x.into()
                    } else {
                        return Err(U256_OUT_OF_RANGE.into());
                    }
                }
                8 => {
                    let x = u64::decode(input)?;
                    if x > u64::max_value() >> 8 {
                        x.into()
                    } else {
                        return Err(U256_OUT_OF_RANGE.into());
                    }
                }
                16 => {
                    let x = u128::decode(input)?;
                    if x > u128::max_value() >> 8 {
                        x.into()
                    } else {
                        return Err(U256_OUT_OF_RANGE.into());
                    }
                }
                32 => {
                    let x = <[u8; 32] as Decode>::decode(input).map(U256::from_le_bytes)?;
                    if x > U256::MAX >> 8 {
                        x
                    } else {
                        return Err(U256_OUT_OF_RANGE.into());
                    }
                }
                x if x > 32 => return Err("unexpected prefix decoding U256".into()),
                bytes_needed => {
                    let mut res = U256::ZERO;
                    for i in 0..bytes_needed {
                        res |= U256::from(input.read_byte()?) << (i * 8);
                    }
                    if res > U256::MAX >> ((32 - bytes_needed + 1) * 8) {
                        res
                    } else {
                        return Err(U256_OUT_OF_RANGE.into());
                    }
                }
            },
        }))
    }
}

const U256_OUT_OF_RANGE: &str = "out of range decoding U256";

impl From<Compact<CompactU256>> for CompactU256 {
    fn from(v: Compact<CompactU256>) -> Self {
        v.0
    }
}

impl CompactAs for CompactU256 {
    type As = U256;

    fn encode_as(&self) -> &Self::As {
        &self.0
    }

    fn decode_from(v: Self::As) -> Result<Self, Error> {
        Ok(Self(v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn encode() {
        for (input, expected_encoded) in [
            (U256::ZERO, vec![0b0000_0000]),
            (U256::ONE, vec![0b0000_0100]),
            (U256::from(u8::MAX), vec![0b1111_1101, 0b0000_0011]),
            (
                U256::from(u16::MAX),
                vec![0b1111_1110, 0b1111_1111, 0b0000_0011, 0b0000_0000],
            ),
            (
                U256::from(u32::MAX),
                vec![0b0000_0011, 0xFF, 0xFF, 0xFF, 0xFF],
            ),
            (
                U256::from(u64::MAX),
                vec![0b0001_0011, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
            ),
            (
                U256::from(u128::MAX),
                vec![
                    0b0011_0011,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                ],
            ),
            (
                U256::MAX,
                vec![
                    0b0111_0011,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                    0xFF,
                ],
            ),
        ] {
            let encoded = CompactRefU256(&input).encode();

            assert_eq!(encoded, expected_encoded);

            assert_eq!(
                CompactU256::decode(&mut encoded.as_slice()).unwrap().0,
                input
            );
        }
    }
}
