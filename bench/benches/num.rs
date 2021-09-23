use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::ops::*;

fn arithmetic<U>(c: &mut Criterion)
where
    U: Add + Div + Mul + Sub + Shl<Output = U> + Shr + Copy + From<u128>,
{
    let value = U::from(u128::MAX) << U::from(11);
    let lo = U::from(u128::MAX >> 13);

    c.bench_function("U256::add", |b| {
        b.iter(|| black_box(value) + black_box(value))
    });

    c.bench_function("U256::div (lo/lo)", |b| {
        b.iter(|| black_box(lo) / black_box(lo))
    });

    c.bench_function("U256::div (hi/lo)", |b| {
        b.iter(|| black_box(value) / black_box(lo))
    });

    c.bench_function("U256::div (hi/hi)", |b| {
        b.iter(|| black_box(value) / black_box(value))
    });

    c.bench_function("U256::mul", |b| {
        b.iter(|| black_box(value) * black_box(value))
    });

    c.bench_function("U256::sub", |b| {
        b.iter(|| black_box(value) - black_box(value))
    });

    c.bench_function("U256::shl", |b| {
        b.iter(|| black_box(value) << black_box(U::from(21)))
    });

    c.bench_function("U256::shr", |b| {
        b.iter(|| black_box(value) >> black_box(U::from(21)))
    });
}

#[cfg_attr(feature = "primitive-types", allow(dead_code))]
fn intrinsics(c: &mut Criterion) {
    let value = ethnum::U256::new(u128::MAX) << 11u32;

    c.bench_function("U256::rotate_left", |b| {
        b.iter(|| black_box(value).rotate_left(black_box(21)))
    });

    c.bench_function("U256::rotate_right", |b| {
        b.iter(|| black_box(value).rotate_right(black_box(21)))
    });

    c.bench_function("U256::ctlz", |b| {
        b.iter(|| black_box(value).leading_zeros())
    });

    c.bench_function("U256::cttz", |b| {
        b.iter(|| black_box(value).trailing_zeros())
    });
}

#[cfg(not(feature = "primitive-types"))]
criterion_group!(num, arithmetic::<ethnum::U256>, intrinsics);
#[cfg(feature = "primitive-types")]
criterion_group!(num, arithmetic::<primitive_types::U256>);

criterion_main!(num);
