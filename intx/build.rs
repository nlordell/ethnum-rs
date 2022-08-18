use cc::Build;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let mut build = Build::new();
    build
        .compiler("clang")
        .cpp(true)
        .file("src/intx.cpp")
        .flag("-std=c++17")
        .opt_level(3);

    build.try_compile("intx")?;
    Ok(())
}
