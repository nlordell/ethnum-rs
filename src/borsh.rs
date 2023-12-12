use crate::{I256, U256};

impl borsh::BorshSerialize for I256 {
    fn serialize<W: borsh::io::Write>(&self, writer: &mut W) -> borsh::io::Result<()> {
        self.0.serialize(writer)
    }
}

impl borsh::BorshSerialize for U256 {
    fn serialize<W: borsh::io::Write>(&self, writer: &mut W) -> borsh::io::Result<()> {
        self.0.serialize(writer)
    }
}

impl borsh::BorshDeserialize for I256 {
    fn deserialize_reader<R: borsh::io::Read>(reader: &mut R) -> borsh::io::Result<Self> {
        let value: [i128; 2] = borsh::BorshDeserialize::deserialize_reader(reader)?;
        Ok(Self(value))
    }
}

impl borsh::BorshDeserialize for U256 {
    fn deserialize_reader<R: borsh::io::Read>(reader: &mut R) -> borsh::io::Result<Self> {
        let value: [u128; 2] = borsh::BorshDeserialize::deserialize_reader(reader)?;
        Ok(Self(value))
    }
}

#[cfg(test)]
mod borsh_tests {
    use crate::I256;

    #[test]
    fn test_borsh_i256() {
        let i = I256::MIN;
        let buffer = borsh::to_vec(&i).expect("failed to serialize value");
        let deser_i: I256 = borsh::from_slice(&buffer).expect("failed to deserialize value");
        assert_eq!(deser_i, i);
    }
}
