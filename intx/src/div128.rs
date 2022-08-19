const fn reciprocal_table_item(d9: u8) -> u16 {
    (0x7fd00 / (0x100 | (d9 as u32))) as _
}

const fn reciprocal_table_items() -> [u16; 256] {
    let mut table = [0; 256];

    macro_rules! repeat {
        (4; $x:expr) => {
            table[($x) + 0] = reciprocal_table_item(($x) + 0);
            table[($x) + 1] = reciprocal_table_item(($x) + 1);
            table[($x) + 2] = reciprocal_table_item(($x) + 2);
            table[($x) + 3] = reciprocal_table_item(($x) + 3);
        };
        (32; $x:expr) => {
            repeat!(4; ($x) + (4 * 0));
            repeat!(4; ($x) + (4 * 1));
            repeat!(4; ($x) + (4 * 2));
            repeat!(4; ($x) + (4 * 3));
            repeat!(4; ($x) + (4 * 4));
            repeat!(4; ($x) + (4 * 5));
            repeat!(4; ($x) + (4 * 6));
            repeat!(4; ($x) + (4 * 7));
        };
        (256) => {
            repeat!(32; 32 * 0);
            repeat!(32; 32 * 1);
            repeat!(32; 32 * 2);
            repeat!(32; 32 * 3);
            repeat!(32; 32 * 4);
            repeat!(32; 32 * 5);
            repeat!(32; 32 * 6);
            repeat!(32; 32 * 7);
        };
    }
    repeat!(256);

    table
}

/// Reciprocal lookup table.
const RECIPROCAL_TABLE: [u16; 256] = reciprocal_table_items();

/// Full unsigned multiplication 64 x 64 -> 128.
#[inline(always)]
const fn umul(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

#[inline(always)]
const fn u128w(x: u128) -> [u64; 2] {
    //mem::transmute(x)
    [x as _, (x >> 64) as _]
}

#[inline(always)]
const fn u128v(lo: u64, hi: u64) -> u128 {
    (lo as u128) + ((hi as u128) << 64)
}

/// Computes the reciprocal (2^128 - 1) / d - 2^64 for normalized d.
///
/// Based on Algorithm 2 from "Improved division by invariant integers".
#[inline]
fn reciprocal_2by1(d: u64) -> u64 {
    debug_assert!(d & 0x8000000000000000 != 0, "must be normalized");

    let d9 = d >> 55;
    let v0 = RECIPROCAL_TABLE[(d9 - 256) as usize] as u64;
    //let v0 = unsafe { RECIPROCAL_TABLE.get_unchecked((d9 - 256) as usize) } as u64;

    let d40 = (d >> 24) + 1;
    let v1: u64 = ((v0 as u64) << 11)
        .wrapping_sub((v0 * v0).wrapping_mul(d40) >> 40)
        .wrapping_sub(1);

    let v2 = (v1 << 13).wrapping_add(
        v1.wrapping_mul(0x1000000000000000_u64.wrapping_sub(v1.wrapping_mul(d40))) >> 47,
    );

    let d0 = d & 1;
    let d63 = (d >> 1) + d0; // ceil(d/2)
    let e = ((v2 >> 1) & 0_u64.wrapping_sub(d0)).wrapping_sub(v2.wrapping_mul(d63));
    let v3 = (u128w(umul(v2, e))[1] >> 1).wrapping_add(v2 << 31);

    v3.wrapping_sub(u128w(umul(v3, d).wrapping_add(d as _))[1])
        .wrapping_sub(d)
}

#[inline]
fn reciprocal_3by2(d: u128) -> u64 {
    let mut v = reciprocal_2by1(u128w(d)[1]);
    let mut p = u128w(d)[1].wrapping_mul(v);
    p = p.wrapping_add(u128w(d)[0]);
    if p < u128w(d)[0] {
        v = v.wrapping_sub(1);
        if p >= u128w(d)[1] {
            v = v.wrapping_sub(1);
            p = p.wrapping_sub(u128w(d)[1]);
        }
        p = p.wrapping_sub(u128w(d)[1]);
    }

    let t = umul(v, u128w(d)[0]);

    p = p.wrapping_add(u128w(t)[1]);
    if p < u128w(t)[1] {
        v = v.wrapping_sub(1);
        if p >= u128w(d)[1] && (p > u128w(d)[1] || u128w(t)[0] >= u128w(d)[0]) {
            v = v.wrapping_sub(1);
        }
    }
    v
}

pub struct DivResult<Q, R = Q> {
    pub quot: Q,
    pub rem: R,
}

#[inline]
fn udivrem_2by1(u: u128, d: u64, v: u64) -> DivResult<u64> {
    let mut q = umul(v, u128w(u)[1]);
    q = q.wrapping_add(u);

    q = q.wrapping_add(1 << 64);

    let mut r = u128w(u)[0].wrapping_sub(u128w(q)[1].wrapping_mul(d));

    if r > u128w(q)[0] {
        q = q.wrapping_sub(1 << 64);
        r = r.wrapping_add(d);
    }

    if r >= d {
        q = q.wrapping_add(1 << 64);
        r = r.wrapping_sub(d);
    }

    DivResult {
        quot: u128w(q)[1],
        rem: r,
    }
}

#[inline]
fn udivrem_3by2(u2: u64, u1: u64, u0: u64, d: u128, v: u64) -> DivResult<u64, u128> {
    let mut q = umul(v, u2);
    q = q.wrapping_add(u128v(u1, u2));

    let mut r1 = u1.wrapping_sub(u128w(q)[1].wrapping_mul(u128w(d)[1]));

    let t = umul(u128w(d)[0], u128w(q)[1]);

    let mut r = u128v(u0, r1).wrapping_sub(t).wrapping_sub(d);
    r1 = u128w(r)[1];

    q = q.wrapping_add(1 << 64);

    if r1 >= u128w(q)[0] {
        q = q.wrapping_sub(1 << 64);
        r = r.wrapping_add(d);
    }

    if r >= d {
        q = q.wrapping_add(1 << 64);
        r = r.wrapping_sub(d);
    }

    DivResult {
        quot: u128w(q)[1],
        rem: r,
    }
}

#[inline]
pub fn udivrem(x: u128, y: u128) -> DivResult<u128> {
    if u128w(y)[1] == 0 {
        assert!(u128w(y)[0] != 0, "division by 0");

        let lsh = u128w(y)[0].leading_zeros();
        let rsh = (64 - lsh) % 64;
        let rsh_mask = ((lsh == 0) as u64).wrapping_sub(1);

        let yn = u128w(y)[0] << lsh;
        let xn_lo = u128w(x)[0] << lsh;
        let xn_hi = (u128w(x)[1] << lsh) | ((u128w(x)[0] >> rsh) & rsh_mask);
        let xn_ex = (u128w(x)[1] >> rsh) & rsh_mask;

        let v = reciprocal_2by1(yn);
        let res1 = udivrem_2by1(u128v(xn_hi, xn_ex), yn, v);
        let res2 = udivrem_2by1(u128v(xn_lo, res1.rem), yn, v);
        return DivResult {
            quot: u128v(res2.quot, res1.quot),
            rem: (res2.rem >> lsh) as u128,
        };
    }

    if u128w(y)[1] > u128w(x)[1] {
        return DivResult { quot: 0, rem: x };
    }

    let lsh = u128w(y)[1].leading_zeros();
    if lsh == 0 {
        let q = ((u128w(y)[1] < u128w(x)[1]) as u128) | ((u128w(y)[0] <= u128w(x)[0]) as u128);
        return DivResult {
            quot: q,
            rem: x.wrapping_sub(if q != 0 { y } else { 0 }),
        };
    }

    let rsh = 64 - lsh;

    let yn_lo = u128w(y)[0] << lsh;
    let yn_hi = (u128w(y)[1] << lsh) | (u128w(y)[0] >> rsh);
    let xn_lo = u128w(x)[0] << lsh;
    let xn_hi = (u128w(x)[1] << lsh) | (u128w(x)[0] >> rsh);
    let xn_ex = u128w(x)[1] >> rsh;

    let v = reciprocal_3by2(u128v(yn_lo, yn_hi));
    let res = udivrem_3by2(xn_ex, xn_hi, xn_lo, u128v(yn_lo, yn_hi), v);

    DivResult {
        quot: res.quot as _,
        rem: res.rem >> lsh,
    }
}

#[inline]
pub fn div(x: u128, y: u128) -> u128 {
    udivrem(x, y).quot
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initializes_reciprocal_table() {
        for (i, item) in RECIPROCAL_TABLE.into_iter().enumerate() {
            assert_eq!(item, reciprocal_table_item(i as u8));
        }
    }

    #[test]
    fn divides() {
        for (n, d) in [
            (
                0x18e84e52c67571be949e7aa3f3275b79,
                0x13fb2c5a166e1b80d92d0aef6554116d,
            ),
            (0x613dfc90ca4a5c65c2e12a3a360503fd, 0xba82a69adb132d14),
        ] {
            assert_eq!(div(n, d), n / d);
        }
    }
}
