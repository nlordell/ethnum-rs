fn main() {
    println!("cargo:rerun-if-changed=src/intrinsics.c");
    println!("cargo:rerun-if-changed=build.rs");

    let mut build = cc::Build::new();
    build.file("src/intrinsics.c");
    build
        .flag_if_supported("-std=c23")
        .flag_if_supported("-fexperimental-max-bitint-width=256");
    build.compile("intrinsics");
}
