// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
use vstd::arithmetic::power2::pow2;
use vstd::bits::low_bits_mask;
use vstd::prelude::*;

#[macro_export]
macro_rules! POW2_VALUE {
    (0) => {
        0x1u64
    };
    (1) => {
        0x2u64
    };
    (2) => {
        0x4u64
    };
    (3) => {
        0x8u64
    };
    (4) => {
        0x10u64
    };
    (5) => {
        0x20u64
    };
    (6) => {
        0x40u64
    };
    (7) => {
        0x80u64
    };
    (8) => {
        0x100u64
    };
    (9) => {
        0x200u64
    };
    (10) => {
        0x400u64
    };
    (11) => {
        0x800u64
    };
    (12) => {
        0x1000u64
    };
    (13) => {
        0x2000u64
    };
    (14) => {
        0x4000u64
    };
    (15) => {
        0x8000u64
    };
    (16) => {
        0x10000u64
    };
    (17) => {
        0x20000u64
    };
    (18) => {
        0x40000u64
    };
    (19) => {
        0x80000u64
    };
    (20) => {
        0x100000u64
    };
    (21) => {
        0x200000u64
    };
    (22) => {
        0x400000u64
    };
    (23) => {
        0x800000u64
    };
    (24) => {
        0x1000000u64
    };
    (25) => {
        0x2000000u64
    };
    (26) => {
        0x4000000u64
    };
    (27) => {
        0x8000000u64
    };
    (28) => {
        0x10000000u64
    };
    (29) => {
        0x20000000u64
    };
    (30) => {
        0x40000000u64
    };
    (31) => {
        0x80000000u64
    };
    (32) => {
        0x100000000u64
    };
    (33) => {
        0x200000000u64
    };
    (34) => {
        0x400000000u64
    };
    (35) => {
        0x800000000u64
    };
    (36) => {
        0x1000000000u64
    };
    (37) => {
        0x2000000000u64
    };
    (38) => {
        0x4000000000u64
    };
    (39) => {
        0x8000000000u64
    };
    (40) => {
        0x10000000000u64
    };
    (41) => {
        0x20000000000u64
    };
    (42) => {
        0x40000000000u64
    };
    (43) => {
        0x80000000000u64
    };
    (44) => {
        0x100000000000u64
    };
    (45) => {
        0x200000000000u64
    };
    (46) => {
        0x400000000000u64
    };
    (47) => {
        0x800000000000u64
    };
    (48) => {
        0x1000000000000u64
    };
    (49) => {
        0x2000000000000u64
    };
    (50) => {
        0x4000000000000u64
    };
    (51) => {
        0x8000000000000u64
    };
    (52) => {
        0x10000000000000u64
    };
    (53) => {
        0x20000000000000u64
    };
    (54) => {
        0x40000000000000u64
    };
    (55) => {
        0x80000000000000u64
    };
    (56) => {
        0x100000000000000u64
    };
    (57) => {
        0x200000000000000u64
    };
    (58) => {
        0x400000000000000u64
    };
    (59) => {
        0x800000000000000u64
    };
    (60) => {
        0x1000000000000000u64
    };
    (61) => {
        0x2000000000000000u64
    };
    (62) => {
        0x4000000000000000u64
    };
    (63) => {
        0x8000000000000000u64
    };
    ($_:expr) => {
        0u64
    };
}

verus! {

#[verifier(inline)]
pub open spec fn bit_value(n: u64) -> u64
    recommends
        n < 64,
{
    seq_macro::seq! { N in 0..64 {
    #(if n == N {
        POW2_VALUE!(N)
    } else)*
    {
        0
    }
}
}
}

} // verus!
verus! {

pub open spec fn is_pow_of_2(val: u64) -> bool {
    seq_macro::seq! {N in 0..64 {#(
            val == 1u64 << N ||
        )* false
    }}
}

#[verifier(inline)]
pub open spec fn pow2_to_bits(val: u64) -> u64 {
    choose|ret: u64| (1u64 << ret) == val && 0 <= ret < 64
}

} // verus!
#[rustfmt::skip]
macro_rules! bit_shl_values {
    ($typ:ty, $styp:ty, $one: expr, $pname: ident) => {
        seq_macro::seq! {N in 0..64 {verus! {
        #[doc = "Proof that shifting 1 by N has a bound."]
        pub broadcast proof fn $pname()
        ensures
        #(
            #![trigger ($one << N)]
        )*
        #(
            N < $styp::BITS ==> ($one << N) == POW2_VALUE!(N),
        )*
        {
            #(assert($one << N == POW2_VALUE!(N)) by(compute_only);)*
        }
        }
}}
    };
}

macro_rules! bit_not_properties {
    ($typ:ty, $styp:ty, $sname: ident, $autopname: ident) => {
        verus! {
        #[doc = "Proof that !a is equal to max - a, and !!a == a"]
        pub broadcast proof fn $autopname(a: $typ)
            ensures
                #[trigger]!a == sub($styp::MAX as $typ, a),
                !(!a) == a,
        {
            assert(!(!a) == a) by(bit_vector);
            assert((!a) == $styp::MAX - a) by(bit_vector);
        }
        }
    };
}

macro_rules! bit_set_clear_mask {
    ($typ:ty, $styp:ty, $pname_or_mask: ident, $pname_and_mask: ident, $pname_or_zero: ident, $pname_and_zero: ident) => {
        verus! {
        #[doc = "Proof that a mask m is set with or operation."]
        #[verifier(bit_vector)]
        pub broadcast proof fn $pname_or_mask(a: $typ, m: $typ)
            ensures
                (#[trigger](a | m)) & m == m,
                (a | m) & (!m) == a & (!m),
                a | m >= a,
                a | m >= m,
                a == (a|m) - m + (a|!m) - !m
        {}

        #[doc = "Proof that a mask m is cleared with and operation."]
        #[verifier(bit_vector)]
        pub broadcast proof fn $pname_and_mask(a: $typ, m: $typ)
            ensures
                (#[trigger](a & m)) & !m == 0,
                (a & m) & m == a & m,
                a & m <= m,
                a & m <= a,
                a == (a & m) + (a & !m),
        {}

        #[doc = "Proof that a mask m is cleared with and operation."]
        #[verifier(bit_vector)]
        pub broadcast proof fn $pname_or_zero(a: $typ, b: $typ)
            ensures
                b == 0 ==> #[trigger](a | b) == a,
                a == 0 ==> #[trigger](a | b) == b,
        {}

        #[doc = "Proof that a mask m is cleared with and operation."]
        #[verifier(bit_vector)]
        pub broadcast proof fn $pname_and_zero(a: $typ, b: $typ)
            ensures
                a == 0 | b == 0 ==> #[trigger](a & b) == 0,
        {}
        }
    };
}

verus! {

pub broadcast proof fn lemma_bit_u64_and_mask_is_mod(x: u64, mask: u64)
    requires
        mask < u64::MAX,
        is_pow_of_2((mask + 1) as u64),
    ensures
        #[trigger] (x & mask) == x as int % (mask + 1),
{
    broadcast use lemma_bit_u64_shl_values;
    broadcast use vstd::bits::lemma_u64_pow2_no_overflow;

    let align = mask + 1;
    let bit = pow2_to_bits(align as u64) as nat;
    assert(1u64 << bit == pow2(bit)) by {
        broadcast use vstd::bits::lemma_u64_shl_is_mul;

    }
    assert(mask == low_bits_mask(bit));
    assert(x & (low_bits_mask(bit) as u64) == x as nat % (pow2(bit))) by {
        broadcast use vstd::bits::lemma_u64_low_bits_mask_is_mod;

    }
}

} // verus!
macro_rules! bit_and_mask_is_mod {
    ($typ:ty, $pname: ident) => {
        verus! {
        pub broadcast proof fn $pname(x: $typ, mask: $typ)
        requires
            mask < $typ::MAX,
            is_pow_of_2((mask + 1) as u64),
        ensures
            #[trigger] (x & mask) == (x as int) % (mask + 1),
        {
            lemma_bit_u64_and_mask_is_mod(x as u64, mask as u64);
        }
        }
    };
}

bit_shl_values! {u64, u64, 1u64, lemma_bit_u64_shl_values}
bit_not_properties! {u64, u64, spec_bit_u64_not_properties, lemma_bit_u64_not_is_sub}
bit_set_clear_mask! {u64, u64, lemma_bit_u64_or_mask, lemma_bit_u64_and_mask, lemma_bit_u64_or_zero, lemma_bit_u64_and_zero}

bit_shl_values! {usize, u64, 1usize, lemma_bit_usize_shl_values}
bit_not_properties! {usize, u64, spec_bit_usize_not_properties, lemma_bit_usize_not_is_sub}
bit_set_clear_mask! {usize, u64, lemma_bit_usize_or_mask, lemma_bit_usize_and_mask, lemma_bit_usize_or_zero, lemma_bit_usize_and_zero}
bit_and_mask_is_mod! {usize, lemma_bit_usize_and_mask_is_mod}

bit_shl_values! {u32, u32, 1usize, lemma_bit_u32_shl_values}
bit_not_properties! {u32, u32, spec_bit_u32_not_properties, lemma_bit_u32_not_is_sub}
bit_set_clear_mask! {u32, u32, lemma_bit_u32_or_mask, lemma_bit_u32_and_mask, lemma_bit_u32_or_zero, lemma_bit_u32_and_zero}
bit_and_mask_is_mod! {u32, lemma_bit_u32_and_mask_is_mod}
verus! {

pub broadcast proof fn lemma_pow2_eq_bit_value(n: nat)
    requires
        n < u64::BITS,
    ensures
        bit_value(n as u64) == #[trigger] pow2(n),
    decreases n,
{
    vstd::arithmetic::power2::lemma2_to64();
    if n > 0 {
        vstd::arithmetic::power2::lemma_pow2_unfold(n);
    }
    if n > 32 {
        lemma_pow2_eq_bit_value((n - 1) as nat);
    }
}

pub broadcast proof fn lemma_bit_usize_shr_is_div(v: usize, n: usize)
    requires
        n < usize::BITS,
    ensures
        (#[trigger] (v >> n)) == v as int / bit_value(n as u64) as int,
{
    vstd::bits::lemma_u64_shr_is_div(v as u64, n as u64);
    lemma_pow2_eq_bit_value(n as nat);
}

pub broadcast proof fn lemma_bit_u64_shr_is_div(v: u64, n: u64)
    requires
        n < u64::BITS,
    ensures
        (#[trigger] (v >> n)) == v as int / bit_value(n as u64) as int,
{
    vstd::bits::lemma_u64_shr_is_div(v as u64, n as u64);
    lemma_pow2_eq_bit_value(n as nat);
}

#[verifier(bit_vector)]
pub proof fn lemma_u64_or_shl(x: u64, y: u64, n: u64)
requires
    n < 64,
ensures
    (x | y) << n == (x << n) | (y << n)
{}

#[verifier(bit_vector)]
pub proof fn lemma_u64_or_shr(x: u64, y: u64, n: u64)
requires
    n < 64,
ensures
    (x | y) >> n == (x >> n) | (y >> n)
{}

#[verifier(bit_vector)]
pub proof fn lemma_u64_and_is_distributive_or(x: u64, y: u64, mask: u64)
ensures
    (x | y) & mask == (x & mask) | (y & mask),
{}

#[verifier(bit_vector)]
pub proof fn lemma_u64_and_bitmask_lower(x: u64, n: u64)
requires
    n < 64,
    x < (1u64<<n),
ensures
    x & ((1u64<<n) - 1) as u64 == x,
{}

#[verifier(bit_vector)]
pub proof fn lemma_u64_and_bitmask_higher(x: u64, n: u64, m: u64)
requires
    n <= m < 64,
ensures
    (x << m) & ((1u64<<n) - 1) as u64 == 0,
{}

pub proof fn lemma_u64_or_low_high_bitmask_lower(x: u64, y: u64, n: u64, m: u64)
requires
    n <= m < 64,
    x <= (1u64<<n) - 1,
ensures
    (x | y << m) & ((1u64<<n) - 1) as u64  == x,
{
    let mask = ((1u64<<n) - 1) as u64;
    let tmpy = y << m;
    let ret  = (x | tmpy) & mask as u64;
    lemma_u64_and_is_distributive_or(x, y << m, mask as u64);
    assert(ret == (x & mask) | (tmpy & mask));
    lemma_u64_and_bitmask_higher(y, n, m);
    assert((tmpy & mask) == 0);
    lemma_u64_and_bitmask_lower(x, n);
    assert(x | 0 == x) by(bit_vector);
}

#[verifier(bit_vector)]
pub proof fn lemma_u64_shl_add(x: u64, n: u64, m: u64)
requires
    n + m < 64,
ensures
    (x << n) << m == (x << (n + m)),
    (x << m) << n == (x << (m + n)),
{
}

#[verifier(bit_vector)]
pub proof fn lemma_u64_shr_add_one(x: u64, n: u64)
requires
    n < 63, 
ensures
    (x >> n) >> 1 == (x >> (n + 1)),
{
}

pub proof fn lemma_u64_shr_add(x: u64, n: u64, m: u64)
requires
    n + m < 64, 
ensures
    (x >> n) >> m == (x >> (n + m)),
decreases
    m
{
    if m > 0 {
        lemma_u64_shr_add(x, n, (m - 1) as u64);
        lemma_u64_shr_add_one(x >> n, (m - 1) as u64);
        lemma_u64_shr_add_one(x, (n + m - 1) as u64);
        assert((x >> n) >> m == (x >> (n + m - 1)) >> 1);
    } else {
        assert((x >> n) >> 0 == x >> n) by(bit_vector);
    }
}

#[verifier(bit_vector)]
pub proof fn lemma_u64_shlr_same(x: u64, n: u64)
requires
    x <= 0xffff_ffff_ffff_ffffu64 >> n,
ensures
    (x << n) >> n == x,
{
}

pub proof fn lemma_u64_shl_shr(x: u64, n: u64, m: u64)
requires
    x <= u64::MAX >> n,
    n < 64,
    m < 64,
    n <= m,
ensures
    n < m ==> (x << n) >> m == (x >> (m - n)),
    n == m ==> (x << n) >> m == x,
decreases
    m
{
    
    if m == 0 || n == 0 {
        assert((x << n) >> 0 == x << n) by(bit_vector);
        assert(x << 0 == x) by(bit_vector);
        assert(x >> 0 == x) by(bit_vector);
    } else if n == m {
        lemma_u64_shlr_same(x, n);
    } else {
        let mm = (m - 1) as u64;
        lemma_u64_shl_shr(x, n, mm);
        lemma_u64_shr_add_one(x << n, mm);
        if n < m {
            let diff = (mm - n) as u64;
            lemma_u64_shr_add_one(x, diff);
        }
    }
}


} // verus!
macro_rules! bit_xor_neighbor {
    ($typ:ty, $pname: ident) => {
        verus!{
        #[verifier::bit_vector]
        pub proof fn $pname(pfn: $typ, order: $typ)
        requires
            pfn & sub((1u8 as $typ) << order, 1) == 0,
        ensures
            ((pfn & sub((1u8 as $typ) << add(order, 1), 1)) == 0) ==>  (pfn ^ ((1u8 as $typ) << order)) == add(pfn, ((1u8 as $typ) << order)),
            ((pfn & sub((1u8 as $typ) << add(order, 1), 1)) != 0) ==>  (pfn ^ ((1u8 as $typ) << order)) == sub(pfn, ((1u8 as $typ) << order)),
        {}
        }
    };
}

bit_xor_neighbor! {usize, lemma_bit_usize_xor_neighbor}
