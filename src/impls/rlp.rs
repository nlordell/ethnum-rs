use crate::U256;
use rlp::{Decodable, DecoderError, Encodable, Rlp, RlpStream};

impl Encodable for U256 {
    fn rlp_append(&self, s: &mut RlpStream) {
        let buffer = self.to_be_bytes();
        s.encoder()
            .encode_iter(buffer.iter().skip_while(|&&v| v == 0).copied());
    }
}

impl Decodable for U256 {
    fn decode(rlp: &Rlp) -> Result<Self, DecoderError> {
        rlp.decoder().decode_value(|bytes| {
            if !bytes.is_empty() && bytes[0] == 0 {
                Err(DecoderError::RlpInvalidIndirection)
            } else if bytes.len() <= 32 {
                let mut padded = [0u8; 32];
                padded[32 - bytes.len()..].copy_from_slice(bytes);
                Ok(U256::from_be_bytes(padded))
            } else {
                Err(DecoderError::RlpIsTooBig)
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        for (input, expected_encoded) in [
            (0x0_u64, &[0x80_u8] as &[u8]),
            (0x1_u64, &[0x01_u8] as &[u8]),
            (
                0xBAAD_CAFE_u64,
                &[0x84_u8, 0xBA_u8, 0xAD_u8, 0xCA_u8, 0xFE_u8],
            ),
        ] {
            let input = U256::from(input);

            let encoded = rlp::encode(&input);
            assert_eq!(encoded, expected_encoded);

            assert_eq!(rlp::decode::<U256>(&encoded).unwrap(), input);
        }
    }
}
