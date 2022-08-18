//! Intx division

#![allow(dead_code, unused_variables)]

use core::num::NonZeroU64;

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

#[derive(Clone, Copy)]
struct Uint<const N: usize>([u64; N]);

impl<const N: usize> Default for Uint<N> {
    fn default() -> Self {
        Self([0; N])
    }
}

impl<const N: usize> Uint<N> {
    fn static_cast<const M: usize>(self) -> Uint<M> {
        todo!()
    }
}

fn as_words<const N: usize>(u: &Uint<N>) -> *const u64 {
    u.0.as_ptr()
}

fn as_words_mut<const N: usize>(u: &mut Uint<N>) -> *mut u64 {
    u.0.as_mut_ptr()
}

struct DivResult<Q, R = Q> {
    quot: Q,
    rem: R,
}

impl<Q, R> DivResult<Q, R> {
    fn new(quot: Q, rem: R) -> Self {
        Self { quot, rem }
    }
}

#[derive(Default)]
struct NormalizedDivArgs<const M: usize, const N: usize> {
    divisor: Uint<N>,
    numerator: Uint<M>,
    num_divisor_words: usize,
    num_numerator_words: usize,
    shift: u32,
}

#[inline(always)]
fn normalize<const M: usize, const N: usize>(
    numerator: &Uint<M>,
    denominator: &Uint<N>,
) -> NormalizedDivArgs<M, N> {
    // This was ported from a function which would require the follwoing
    // signature that is currently not supported in Rust:
    // ```
    // fn(Uint<M>, Uint<N>) -> NormalizedDivArgs<{M + 1}, N>
    // ```
    //
    // To work around this, we expect the caller to call this function with
    // an extra word already. This means that it will **always** be 0.
    debug_assert_eq!(numerator.0[M - 1], 0);

    let num_numerator_words = M - 1;
    let num_denominator_words = N;

    let u = as_words(numerator);
    let v = as_words(denominator);

    let mut na = NormalizedDivArgs::default();
    let un = as_words_mut(&mut na.numerator);
    let vn = as_words_mut(&mut na.divisor);

    let m = &mut na.num_numerator_words;
    *m = num_numerator_words;
    while *m > 0 && unsafe { *u.add(*m - 1) } == 0 {
        *m -= 1;
    }

    let n = &mut na.num_divisor_words;
    *n = num_denominator_words;
    while *n > 0 && unsafe { *v.add(*n - 1) } == 0 {
        *n -= 1;
    }

    na.shift = unsafe { NonZeroU64::new_unchecked(*v.add(*n - 1)) }.leading_zeros();
    if na.shift != 0 {
        for i in (0..num_denominator_words).rev() {
            unsafe { *vn.add(i) = (*v.add(i) << na.shift) | (*v.add(i - 1) >> (64 - na.shift)) };
        }
        unsafe { *vn = *v << na.shift };

        unsafe {
            *un.add(num_numerator_words) = *u.add(num_numerator_words - 1) >> (64 - na.shift)
        };
        for i in (0..num_numerator_words).rev() {
            unsafe { *un.add(i) = (*u.add(i) << na.shift) | (*u.add(i - 1) >> (64 - na.shift)) };
        }
        unsafe { *un = *u << na.shift };
    } else {
        na.numerator = *numerator;
        na.divisor = *denominator;
    }

    // Skip the highest word of numerator if not significant.
    if unsafe { *un.add(*m) != 0 || *un.add(*m - 1) >= *vn.add(*n - 1) } {
        *m += 1;
    }

    na
}

fn udivrem<const M: usize, const N: usize>(
    u: &Uint<M>,
    v: &Uint<N>,
) -> DivResult<Uint<M>, Uint<N>> {
    let na = normalize(u, v);

    if na.num_numerator_words <= na.num_divisor_words {
        return DivResult::new(Uint::default(), u.static_cast());
    }

    /*
    if (na.num_divisor_words == 1)
    {
        const auto r = internal::udivrem_by1(
            as_words(na.numerator), na.num_numerator_words, as_words(na.divisor)[0]);
        return {static_cast<uint<M>>(na.numerator), r >> na.shift};
    }

    if (na.num_divisor_words == 2)
    {
        const auto d = as_words(na.divisor);
        const auto r =
            internal::udivrem_by2(as_words(na.numerator), na.num_numerator_words, {d[0], d[1]});
        return {static_cast<uint<M>>(na.numerator), r >> na.shift};
    }

    auto un = as_words(na.numerator);  // Will be modified.

    uint<M> q;
    internal::udivrem_knuth(
        as_words(q), &un[0], na.num_numerator_words, as_words(na.divisor), na.num_divisor_words);

    uint<N> r;
    auto rw = as_words(r);
    for (int i = 0; i < na.num_divisor_words - 1; ++i)
        rw[i] = na.shift ? (un[i] >> na.shift) | (un[i + 1] << (64 - na.shift)) : un[i];
    rw[na.num_divisor_words - 1] = un[na.num_divisor_words - 1] >> na.shift;

    return {q, r};
    */
    todo!()
}

fn sdivrem<const N: usize>(u: &Uint<N>, v: &Uint<N>) -> DivResult<Uint<N>> {
    /*
    const auto sign_mask = uint<N>{1} << (sizeof(u) * 8 - 1);
    auto u_is_neg = (u & sign_mask) != 0;
    auto v_is_neg = (v & sign_mask) != 0;

    auto u_abs = u_is_neg ? -u : u;
    auto v_abs = v_is_neg ? -v : v;

    auto q_is_neg = u_is_neg ^ v_is_neg;

    auto res = udivrem(u_abs, v_abs);

    return {q_is_neg ? -res.quot : res.quot, u_is_neg ? -res.rem : res.rem};
    */
    todo!()
}

#[cfg(feature = "false")]
mod old {
    /// Reciprocal lookup table.
    const RECIPROCAL_TABLE: [u16; 256] = reciprocal_table_items();

    fn umul(x: u64, y: u64) -> u128 {
        (x as u128) * (y as u128)
    }

    struct DivResult<Q, R = Q> {
        quot: Q,
        rem: R,
    }

    fn uint32_t(x: u64) -> u64 {
        x & 0xffffffff
    }

    /// Computes the reciprocal (2^128 - 1) / d - 2^64 for normalized d.
    ///
    /// Based on Algorithm 2 from "Improved division by invariant integers".
    fn reciprocal_2by1(d: u64) -> u64 {
        debug_assert_ne!(d & 0x8000000000000000, 0); // Must be normalized.

        /*
            let d9 = d >> 55;
            let v0 = unsafe { RECIPROCAL_TABLE.get_unchecked((d9 - 256) as _) } as u32;

            let d40 = (d >> 24) + 1;
            let v1 = (v0 << 11) - uint32_t(uint32_t(v0 * v0) * d40 >> 40) - 1;
        u128
            let v2 = (v1 << 13) + (v1 * (0x1000000000000000 - v1 * d40) >> 47);

            let d0 = d & 1;
            let d63 = (d >> 1) + d0;  // ceil(d/2)
            let e = ((v2 >> 1) & (0 - d0)) - v2 * d63;
            let v3 = (umul(v2, e)[1] >> 1) + (v2 << 31);

            let v4 = v3 - (umul(v3, d) + d)[1] - d;
            return v4;
            */
        todo!()
    }

    fn reciprocal_3by2(d: Uint<128>) -> u64 {
        /*
        let v = reciprocal_2by1(d[1]);
        let p = d[1] * v;
        p += d[0];
        if (p < d[0])
        {
            --v;
            if (p >= d[1])
            {
                --v;
                p -= d[1];
            }
            p -= d[1];
        }

        let t = umul(v, d[0]);

        p += t[1];
        if (p < t[1])
        {
            --v;
            if (p >= d[1])
            {
                if (p > d[1] || t[0] >= d[0]){
                    --v;
                }
            }
        }
        return v;
        */
        todo!()
    }

    #[inline]
    fn udivrem_2by1(u: u128, d: u64, v: u64) -> DivResult<u64> {
        /*
        auto q = umul(v, u[1]);
        q = fast_add(q, u);

        ++q[1];

        auto r = u[0] - q[1] * d;

        if (r > q[0])
        {
            --q[1];
            r += d;
        }

        if (r >= d)
        {
            ++q[1];
            r -= d;
        }

        return {q[1], r};
        */
        todo!()
    }

    #[inline]
    fn udivrem_3by2(u2: u64, u1: u64, u0: u64, d: u128, v: u64) -> DivResult<u64, u128> {
        /*
        auto q = umul(v, u2);
        q = fast_add(q, {u1, u2});

        auto r1 = u1 - q[1] * d[1];

        auto t = umul(d[0], q[1]);

        auto r = uint128{u0, r1} - t - d;
        r1 = r[1];

        ++q[1];

        if (r1 >= q[0])
        {
            --q[1];
            r += d;
        }

        if (r >= d)
        {
            ++q[1];
            r -= d;
        }

        return {q[1], r};
        */
        todo!()
    }

    struct Uint<const N: usize>([u64; N]);

    struct NormalizedDivArgs<const M: usize, const N: usize> {
        divisor: Uint<N>,
        numerator: Uint<M /*+ 64*/>,
        num_divisor_words: usize,
        num_numerator_words: usize,
        shift: u32,
    }

    #[inline(always)]
    fn normalize<const M: usize, const N: usize>(
        numerator: &Uint<M>,
        denominator: &Uint<N>,
    ) -> NormalizedDivArgs<M, N> {
        /*
        static constexpr auto num_numerator_words = uint<M>::num_words;
        static constexpr auto num_denominator_words = uint<N>::num_words;

        auto* u = as_words(numerator);
        auto* v = as_words(denominator);

        normalized_div_args<M, N> na;
        auto* un = as_words(na.numerator);
        auto* vn = as_words(na.divisor);

        auto& m = na.num_numerator_words;
        for (m = num_numerator_words; m > 0 && u[m - 1] == 0; --m)
            ;

        auto& n = na.num_divisor_words;
        for (n = num_denominator_words; n > 0 && v[n - 1] == 0; --n)
            ;

        na.shift = clz_nonzero(v[n - 1]);  // Use clz_nonzero() to avoid clang analyzer's warning.
        if (na.shift)
        {
            for (int i = num_denominator_words - 1; i > 0; --i)
                vn[i] = (v[i] << na.shift) | (v[i - 1] >> (64 - na.shift));
            vn[0] = v[0] << na.shift;

            un[num_numerator_words] = u[num_numerator_words - 1] >> (64 - na.shift);
            for (int i = num_numerator_words - 1; i > 0; --i)
                un[i] = (u[i] << na.shift) | (u[i - 1] >> (64 - na.shift));
            un[0] = u[0] << na.shift;
        }
        else
        {
            na.numerator = numerator;
            na.divisor = denominator;
        }

        // Skip the highest word of numerator if not significant.
        if (un[m] != 0 || un[m - 1] >= vn[n - 1])
            ++m;

        return na;
        */
        todo!()
    }

    /// Divides arbitrary long unsigned integer by 64-bit unsigned integer (1 word).
    /// @param u    The array of a normalized numerator words. It will contain
    ///             the quotient after execution.
    /// @param len  The number of numerator words.
    /// @param d    The normalized divisor.
    /// @return     The remainder.
    #[inline]
    fn udivrem_by1(u: &[u64], d: u64) -> u64 {
        debug_assert!(u.len() >= 2);

        /*
        const auto reciprocal = reciprocal_2by1(d);

        auto rem = u[len - 1];  // Set the top word as remainder.
        u[len - 1] = 0;         // Reset the word being a part of the result quotient.

        auto it = &u[len - 2];
        do
        {
            std::tie(*it, rem) = udivrem_2by1({*it, rem}, d, reciprocal);
        } while (it-- != &u[0]);

        return rem;
        */
        todo!()
    }

    /// Divides arbitrary long unsigned integer by 128-bit unsigned integer (2 words).
    /// @param u    The array of a normalized numerator words. It will contain the
    ///             quotient after execution.
    /// @param len  The number of numerator words.
    /// @param d    The normalized divisor.
    /// @return     The remainder.
    #[inline]
    fn udivrem_by2(u: &[u64], d: u128) -> u128 {
        debug_assert!(u.len() >= 3);

        /*
        const auto reciprocal = reciprocal_3by2(d);

        auto rem = u128{u[len - 2], u[len - 1]};  // Set the 2 top words as remainder.
        u[len - 1] = u[len - 2] = 0;  // Reset these words being a part of the result quotient.

        auto it = &u[len - 3];
        do
        {
            std::tie(*it, rem) = udivrem_3by2(rem[1], rem[0], *it, d, reciprocal);
        } while (it-- != &u[0]);

        return rem;
        */
        todo!()
    }

    /// s = x + y.
    fn add(s: &mut [u64], x: &[u64], y: &[u64]) -> bool {
        debug_assert!(s.len() == x.len() && s.len() == y.len() && s.len() >= 2);

        /*
        bool carry = false;
        for (int i = 0; i < len; ++i)
            std::tie(s[i], carry) = addc(x[i], y[i], carry);
        return carry;
        */
        todo!()
    }

    /// r = x - multiplier * y.
    #[inline]
    fn submul(r: &mut [u64], x: &[u64], y: &[u64], multiplier: u64) -> u64 {
        debug_assert!(r.len() == x.len() && r.len() == y.len() && r.len() >= 2);

        /*
        u64 borrow = 0;
        for (int i = 0; i < len; ++i)
        {
            const auto s = x[i] - borrow;
            const auto p = umul(y[i], multiplier);
            borrow = p[1] + (x[i] < s);
            r[i] = s - p[0];
            borrow += (s < r[i]);
        }
        return borrow;
        */
        todo!()
    }

    #[inline]
    fn udivrem_knuth(q: &mut [u64], u: &[u64], d: &[u64]) {
        debug_assert!(q.len() == u.len());
        debug_assert!(d.len() >= 3);
        debug_assert!(u.len() >= d.len());

        /*
        const auto divisor = u128{d[dlen - 2], d[dlen - 1]};
        const auto reciprocal = reciprocal_3by2(divisor);
        for (int j = ulen - dlen - 1; j >= 0; --j)
        {
            const auto u2 = u[j + dlen];
            const auto u1 = u[j + dlen - 1];
            const auto u0 = u[j + dlen - 2];

            u64 qhat{};
            if (INTX_UNLIKELY((u128{u1, u2}) == divisor))  // Division overflows.
            {
                qhat = ~u64{0};

                u[j + dlen] = u2 - submul(&u[j], &u[j], d, dlen, qhat);
            }
            else
            {
                u128 rhat;
                std::tie(qhat, rhat) = udivrem_3by2(u2, u1, u0, divisor, reciprocal);

                bool carry{};
                const auto overflow = submul(&u[j], &u[j], d, dlen - 2, qhat);
                std::tie(u[j + dlen - 2], carry) = subc(rhat[0], overflow);
                std::tie(u[j + dlen - 1], carry) = subc(rhat[1], carry);

                if (INTX_UNLIKELY(carry))
                {
                    --qhat;
                    u[j + dlen - 1] += divisor[1] + add(&u[j], &u[j], d, dlen - 1);
                }
            }

            q[j] = qhat;  // Store quotient digit.
        }
        */
        todo!()
    }

    fn udivrem<const M: usize, const N: usize>(
        u: &Uint<M>,
        v: &Uint<N>,
    ) -> DivResult<Uint<M>, Uint<N>> {
        /*
        auto na = internal::normalize(u, v);

        if (na.num_numerator_words <= na.num_divisor_words)
            return {0, static_cast<uint<N>>(u)};

        if (na.num_divisor_words == 1)
        {
            const auto r = internal::udivrem_by1(
                as_words(na.numerator), na.num_numerator_words, as_words(na.divisor)[0]);
            return {static_cast<uint<M>>(na.numerator), r >> na.shift};
        }

        if (na.num_divisor_words == 2)
        {
            const auto d = as_words(na.divisor);
            const auto r =
                internal::udivrem_by2(as_words(na.numerator), na.num_numerator_words, {d[0], d[1]});
            return {static_cast<uint<M>>(na.numerator), r >> na.shift};
        }

        auto un = as_words(na.numerator);  // Will be modified.

        uint<M> q;
        internal::udivrem_knuth(
            as_words(q), &un[0], na.num_numerator_words, as_words(na.divisor), na.num_divisor_words);

        uint<N> r;
        auto rw = as_words(r);
        for (int i = 0; i < na.num_divisor_words - 1; ++i)
            rw[i] = na.shift ? (un[i] >> na.shift) | (un[i + 1] << (64 - na.shift)) : un[i];
        rw[na.num_divisor_words - 1] = un[na.num_divisor_words - 1] >> na.shift;

        return {q, r};
        */
        todo!()
    }
}
