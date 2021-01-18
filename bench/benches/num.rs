use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::any;
use std::ops::*;

fn arithmetic<U>(c: &mut Criterion)
where
    U: Add + Mul + Sub + Shl<Output = U> + Shr + Copy + From<u128>,
{
    let value = U::from(u128::MAX) << U::from(11);

    c.bench_function(&format!("{}::add", any::type_name::<U>()), |b| {
        b.iter(|| black_box(value) + black_box(value))
    });

    c.bench_function(&format!("{}::mul", any::type_name::<U>()), |b| {
        b.iter(|| black_box(value) * black_box(value))
    });

    c.bench_function(&format!("{}::sub", any::type_name::<U>()), |b| {
        b.iter(|| black_box(value) - black_box(value))
    });

    c.bench_function(&format!("{}::shl", any::type_name::<U>()), |b| {
        b.iter(|| black_box(value) << black_box(U::from(21)))
    });

    c.bench_function(&format!("{}::shr", any::type_name::<U>()), |b| {
        b.iter(|| black_box(value) >> black_box(U::from(21)))
    });
}

fn intrinsics(c: &mut Criterion) {
    let value = ethnum::U256::new(u128::MAX) << 11u32;

    c.bench_function("ethnum::U256::rotate_left", |b| {
        b.iter(|| black_box(value).rotate_left(black_box(21)))
    });

    c.bench_function("ethnum::U256::rotate_right", |b| {
        b.iter(|| black_box(value).rotate_right(black_box(21)))
    });

    c.bench_function("ethnum::U256::ctlz", |b| {
        b.iter(|| black_box(value).leading_zeros())
    });

    c.bench_function("ethnum::U256::cttz", |b| {
        b.iter(|| black_box(value).trailing_zeros())
    });
}

criterion_group!(num, arithmetic::<ethnum::U256>, intrinsics);
criterion_group!(uint, arithmetic::<primitive_types::U256>);
criterion_main!(num, uint);
