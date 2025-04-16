use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
#[cfg(not(any(feature = "primitive-types", feature = "ruint")))]
use ethnum::{I256, U256};
#[cfg(feature = "primitive-types")]
use primitive_types::U256;
#[cfg(feature = "ruint")]
use ruint::aliases::U256;

#[cfg(not(feature = "ruint"))]
type Shift = u32;
#[cfg(feature = "ruint")]
type Shift = usize;

#[inline(always)]
const fn sh(n: Shift) -> Shift {
    n
}

fn arithmetic(c: &mut Criterion) {
    let nums = [
        (U256::from(0x00017eb02a11f4a9443abc5058e1c2c2_u128) << sh(128))
            + U256::from(0x3540ba08c848a6eb3a1e1415b0000000_u128),
        (U256::from(0x0000000007a5c694c4fb15944398653f_u128) << sh(128))
            + U256::from(0x724f5c482676cba8ea4e698d75210fe0_u128),
        (U256::from(0x0000000000000000024e9ffa7e0bba23_u128) << sh(128))
            + U256::from(0x451a0df036962a5b327f93054732380a_u128),
        (U256::from(0x0000000000000000000000000647a49c_u128) << sh(128))
            + U256::from(0xf1055ae531427db60296077b1863d256_u128),
        U256::from(0x000f4187ab979b49ad893d525a13a5aa_u128),
        U256::from(0x000000000edac72a3447ed506fccc42c_u128),
        U256::from(0x00000000000000000b96d82991369928_u128),
        U256::from(0x00000000000000000000000000000cab_u128),
    ];
    let name = |x: U256| {
        let n = x.leading_zeros() / 64;
        match n {
            0 => "####",
            1 => "###",
            2 => "##",
            _ => "#",
        }
    };
    #[cfg(not(any(feature = "primitive-types", feature = "ruint")))]
    let iname = |x: I256| {
        let neg = x.is_negative();
        let n = x.abs().leading_zeros() / 64;
        match (neg, n) {
            (false, 0) => "####",
            (false, 1) => "###",
            (false, 2) => "##",
            (false, _) => "#",
            (true, 0) => "-####",
            (true, 1) => "-###",
            (true, 2) => "-##",
            (true, _) => "-#",
        }
    };

    c.bench_function("U256::add", |b| {
        b.iter(|| black_box(nums[0]) + black_box(nums[1]))
    });

    let q = [nums[0], nums[2], nums[4], nums[6]];
    let d = [nums[1], nums[3], nums[5], nums[7]];
    for (x, y) in q
        .into_iter()
        .enumerate()
        .flat_map(|(i, x)| d[i..].iter().cloned().map(move |y| (x, y)))
    {
        let name = format!("{}/{}", name(x), name(y));
        c.bench_with_input(
            BenchmarkId::new("U256::div", name),
            &(x, y),
            |b, &(x, y)| b.iter(|| black_box(x) / black_box(y)),
        );
    }

    c.bench_function("U256::mul", |b| {
        b.iter(|| black_box(nums[3]) * black_box(nums[5]))
    });

    for (x, y, tag) in [
        (nums[0], nums[1], "overflow"),
        (nums[3], nums[5], "no overflow"),
        (nums[3], nums[4], "overflow"),
        (nums[5], nums[3], "no overflow"),
        (nums[4], nums[3], "overflow"),
        (nums[6], nums[7], "no overflow"),
    ] {
        let name = format!("{}*{} ({})", name(x), name(y), tag);

        #[cfg(not(feature = "primitive-types"))]
        c.bench_with_input(
            BenchmarkId::new("U256::wrapping_mul", &name),
            &(x, y),
            |b, &(x, y)| b.iter(|| black_box(x).wrapping_mul(black_box(y))),
        );

        c.bench_with_input(
            BenchmarkId::new("U256::overflowing_mul", &name),
            &(x, y),
            |b, &(x, y)| b.iter(|| black_box(x).overflowing_mul(black_box(y))),
        );

        #[cfg(not(any(feature = "primitive-types", feature = "ruint")))]
        for (x, y) in [
            (x.as_i256(), y.as_i256()),
            (x.as_i256(), y.as_i256().wrapping_neg()),
            (x.as_i256().wrapping_neg(), y.as_i256()),
            (x.as_i256().wrapping_neg(), y.as_i256().wrapping_neg()),
        ] {
            let name = format!("{}*{} ({})", iname(x), iname(y), tag);

            c.bench_with_input(
                BenchmarkId::new("I256::wrapping_mul", &name),
                &(x, y),
                |b, &(x, y)| b.iter(|| black_box(x).wrapping_mul(black_box(y))),
            );

            c.bench_with_input(
                BenchmarkId::new("I256::overflowing_mul", &name),
                &(x, y),
                |b, &(x, y)| b.iter(|| black_box(x).overflowing_mul(black_box(y))),
            );
        }
    }

    c.bench_function("U256::sub", |b| {
        b.iter(|| black_box(nums[0]) - black_box(nums[1]))
    });

    for (name, shift) in [("short", sh(21)), ("long", sh(176))] {
        c.bench_with_input(BenchmarkId::new("U256::shl", name), &shift, |b, &s| {
            b.iter(|| black_box(nums[0]) << black_box(s))
        });

        c.bench_with_input(BenchmarkId::new("U256::shr", name), &shift, |b, &s| {
            b.iter(|| black_box(nums[0]) >> black_box(s))
        });

        #[cfg(not(feature = "primitive-types"))]
        c.bench_with_input(
            BenchmarkId::new("U256::rotate_left", name),
            &shift,
            |b, &s| b.iter(|| black_box(nums[0]).rotate_left(black_box(s))),
        );

        #[cfg(not(feature = "primitive-types"))]
        c.bench_with_input(
            BenchmarkId::new("U256::rotate_right", name),
            &shift,
            |b, &s| b.iter(|| black_box(nums[0]).rotate_right(black_box(s))),
        );
    }

    for x in [nums[0], nums[2], nums[4], nums[6]] {
        c.bench_with_input(BenchmarkId::new("U256::ctlz", name(x)), &x, |b, &x| {
            b.iter(|| black_box(x).leading_zeros())
        });

        #[cfg(not(any(feature = "primitive-types", feature = "ruint")))]
        c.bench_with_input(
            BenchmarkId::new("U256::cttz", name(x)),
            &x.swap_bytes(),
            |b, &x| b.iter(|| black_box(x).trailing_zeros()),
        );
    }
}

criterion_group!(num, arithmetic);
criterion_main!(num);
