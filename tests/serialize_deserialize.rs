#[cfg(feature = "serde")]
#[test]
fn roundtrip() {
    use ethnum::{I256, U256};
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
    struct Test {
        #[serde(with = "ethnum::serde::bytes::le")]
        a: U256,
        #[serde(with = "ethnum::serde::bytes::be")]
        b: U256,
        #[serde(with = "ethnum::serde::bytes::ne")]
        c: U256,
        #[serde(with = "ethnum::serde::bytes::le")]
        d: I256,
        #[serde(with = "ethnum::serde::bytes::be")]
        e: I256,
        #[serde(with = "ethnum::serde::bytes::ne")]
        f: I256,
    }

    let original = Test {
        a: U256::new(1),
        b: U256::new(2),
        c: U256::new(3),
        d: I256::new(4),
        e: I256::new(5),
        f: I256::new(6),
    };
    let serialized = serde_json::to_string(&original).unwrap();
    let deserialized: Test = serde_json::from_str(&serialized).unwrap();
    assert_eq!(original, deserialized);
}
