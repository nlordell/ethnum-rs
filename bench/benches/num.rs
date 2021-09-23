use criterion::{black_box, criterion_group, criterion_main, Criterion};
#[cfg(not(feature = "primitive-types"))]
use ethnum::U256;
#[cfg(feature = "primitive-types")]
use primitive_types::U256;

fn arithmetic(c: &mut Criterion) {
    let big = [
        (U256::from(0x00017eb02a11f4a9443abc5058e1c2c2_u128) << 128_u32)
            + U256::from(0x3540ba08c848a6eb3a1e1415b0000000_u128),
        (U256::from(0x0000000000000000024e9ffa7e0bba23_u128) << 128_u32)
            + U256::from(0x451a0df036962a5b327f93054732380a_u128),
    ];
    let sml = [
        U256::from(0x00004187ab979b49ad893d525a13a5aa_u128),
        U256::from(0x0000000000000048db96d82991369928_u128),
    ];

    c.bench_function("U256::add", |b| {
        b.iter(|| black_box(big[0]) + black_box(big[1]))
    });

    c.bench_function("U256::div (lo/lo)", |b| {
        b.iter(|| black_box(sml[0]) / black_box(sml[1]))
    });

    c.bench_function("U256::div (hi/lo)", |b| {
        b.iter(|| black_box(big[0]) / black_box(sml[0]))
    });

    c.bench_function("U256::div (hi/hi)", |b| {
        b.iter(|| black_box(big[0]) / black_box(big[1]))
    });

    c.bench_function("U256::mul", |b| {
        b.iter(|| black_box(sml[0]) * black_box(sml[1]))
    });

    c.bench_function("U256::sub", |b| {
        b.iter(|| black_box(big[0]) - black_box(big[1]))
    });

    c.bench_function("U256::shl", |b| {
        b.iter(|| black_box(big[0]) << black_box(21))
    });

    c.bench_function("U256::shr", |b| {
        b.iter(|| black_box(big[0]) >> black_box(21))
    });

    c.bench_function("U256::ctlz", |b| {
        b.iter(|| black_box(big[0]).leading_zeros())
    });

    c.bench_function("U256::cttz", |b| {
        b.iter(|| black_box(big[0]).trailing_zeros())
    });

    #[cfg(not(feature = "primitive-types"))]
    c.bench_function("U256::rotate_left", |b| {
        b.iter(|| black_box(big[0]).rotate_left(black_box(21)))
    });

    #[cfg(not(feature = "primitive-types"))]
    c.bench_function("U256::rotate_right", |b| {
        b.iter(|| black_box(big[0]).rotate_right(black_box(21)))
    });
}

criterion_group!(num, arithmetic);
criterion_main!(num);
