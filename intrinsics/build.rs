fn main() {
    println!("cargo:rerun-if-changed=src/intrinsics.c");
    println!("cargo:rerun-if-changed=build.rs");

    let mut build = cc::Build::new();
    build.file("src/intrinsics.c");
    build.compile("intrinsics");
}
