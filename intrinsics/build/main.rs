//! Generates object for LLVM IR integer intrinsics. This enables the crate to
//! use compiler generated `U256` operations (such as addition, multiplication)
//! instead of native Rust implementation.
//!
//! Note that generating intrinsics requires a Clang toolchain to compile LLVM
//! IR, but has some advantages. Specifically, it detects and enables ThinLTO
//! for the compiled LLVM IR, which allows the linker to perform link-time
//! optimizations such as inlining some of the intrinsics (such as `add*`) which
//! has some **REAL** performance benefits.

#[allow(dead_code)]
mod intrinsics;

use cc::Build;
use std::{env, error::Error, fs, path::PathBuf, process::Command};

fn main() -> Result<(), Box<dyn Error>> {
    let out_dir = PathBuf::from(env::var("OUT_DIR")?);

    let template = {
        let path = out_dir.join("template.ll");
        Command::new(env::var("RUSTC")?)
            .arg("build/intrinsics.rs")
            .arg("-O")
            .args(&["--crate-type", "lib"])
            .args(&["--emit", "llvm-ir"])
            .args(&["--target", &env::var("TARGET")?])
            .arg("-o")
            .arg(&path)
            .status()?;
        fs::read_to_string(path)?
    };

    let intrinsics_ir_path = {
        let source = template
            .replace("i128", "i256")
            .replace(" 127", " 255")
            .replace("dereferenceable(16)", "dereferenceable(32)");
        let path = out_dir.join("intrinsics.ll");
        fs::write(&path, source)?;
        path
    };

    let mut build = Build::new();
    build
        .compiler("clang")
        .file(intrinsics_ir_path)
        .opt_level(3);

    let linker_plugin_lto =
        matches!(env::var("RUSTFLAGS"), Ok(flags) if flags.contains("-Clinker-plugin-lto"));
    if linker_plugin_lto {
        build.flag("-flto=thin");
    }

    build.try_compile("ethnum")?;
    Ok(())
}
