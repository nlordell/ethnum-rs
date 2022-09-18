# `ethnum-macros`

This crate provides procedural macros for compile-time 256-bit integer literals.

```rust
assert_eq!(ethnum::int!("42") == 42);
```

## Usage

This is typically not used directly, but instead included with `ethnum`:

```toml
[dependencies]
ethnum = { version = "*", features = ["macros"] }
```
