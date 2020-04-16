# `ethnum`

This crate provides an implementation for a 256-bit unsigned integer, the
primitive integer type in Ethereum. This implementation is meant to be as close
as possible to Rust unsigned integer primitives, implementing the same methods
and traits.

## Usage

Add this to your `Cargo.toml`:

```toml
ethnum = "1"
```

The API follows the `uN` primitive types as close as possible.

## Intrinsics

The 256-bit integer uses intrinsics based on two implementations:

### Native Rust Implementation

The integer intrinsics are implemented using standard Rust. The more
complicated operations such as multiplication and division are ported from C
compiler intrinsics for implementing equivalent 128-bit operations on 64-bit
systems (or 64-bit operations on 32-bit systems). In general, these are ported
from the Clang `compiler-rt` support routines.

This is the default implementation used by the crate, and in general is quite
well optimized. When using native the implementation, there are no additional
dependencies for this crate.

### LLVM Generated Implementation

Alternatively, `ethnum` can use LLVM-generated intrinsics for base 256-bit
integer operations. This takes advantage of the fact that LLVM IR supports
arbitrarily sized integer operations (such as `@llvm.uadd.with.overflow.i256`
for overflowing unsigned addition). This will produce more optimized assembly
for things like addition and multiplication.

However, there are a couple downsides to using LLVM-generated intrinsics. First
of all, Clang is required in order to compile the LLVM IR. Additionally, Rust
usually optimizes when compiling and linking Rust code (and not externally
linked code), this means that these intrinsics cannot be inlined adding an extra
function call overhead in some cases which make it perform worse than the native
Rust implementation despite having more optimized assembly. Luckily, Rust
currently has support for linker plugin LTO to enable optimizations during the
link step, enabling optimizations with Clang-compiled LLVM IR.

In order to use LLVM-generated intrinsics, enable the `llvm-intrinsics` feature:

```toml
ethnum = { version = "1", features = ["llvm-intrinsics"] }
```

And, genererally it is a good idea to compile with `linker-plugin-lto` enabled
in order to actually take advantage of the the optimized assembly:

```sh
RUSTFLAGS="-Clinker-plugin-lto -Clinker=clang -Clink-arg=-fuse-ld=lld" cargo build
```
