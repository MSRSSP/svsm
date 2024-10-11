// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
use vstd::prelude::*;

verus! {

#[verifier(inline)]
pub open spec fn spec_bit(n: u64) -> u64
    recommends
        n < 64,
{
    if n == 0 {
        0x1
    } else if n == 1 {
        0x2
    } else if n == 2 {
        0x4
    } else if n == 3 {
        0x8
    } else if n == 4 {
        0x10
    } else if n == 5 {
        0x20
    } else if n == 6 {
        0x40
    } else if n == 7 {
        0x80
    } else if n == 8 {
        0x100
    } else if n == 9 {
        0x200
    } else if n == 10 {
        0x400
    } else if n == 11 {
        0x800
    } else if n == 12 {
        0x1000
    } else if n == 13 {
        0x2000
    } else if n == 14 {
        0x4000
    } else if n == 15 {
        0x8000
    } else if n == 16 {
        0x10000
    } else if n == 17 {
        0x20000
    } else if n == 18 {
        0x40000
    } else if n == 19 {
        0x80000
    } else if n == 20 {
        0x100000
    } else if n == 21 {
        0x200000
    } else if n == 22 {
        0x400000
    } else if n == 23 {
        0x800000
    } else if n == 24 {
        0x1000000
    } else if n == 25 {
        0x2000000
    } else if n == 26 {
        0x4000000
    } else if n == 27 {
        0x8000000
    } else if n == 28 {
        0x10000000
    } else if n == 29 {
        0x20000000
    } else if n == 30 {
        0x40000000
    } else if n == 31 {
        0x80000000
    } else if n == 32 {
        0x100000000
    } else if n == 33 {
        0x200000000
    } else if n == 34 {
        0x400000000
    } else if n == 35 {
        0x800000000
    } else if n == 36 {
        0x1000000000
    } else if n == 37 {
        0x2000000000
    } else if n == 38 {
        0x4000000000
    } else if n == 39 {
        0x8000000000
    } else if n == 40 {
        0x10000000000
    } else if n == 41 {
        0x20000000000
    } else if n == 42 {
        0x40000000000
    } else if n == 43 {
        0x80000000000
    } else if n == 44 {
        0x100000000000
    } else if n == 45 {
        0x200000000000
    } else if n == 46 {
        0x400000000000
    } else if n == 47 {
        0x800000000000
    } else if n == 48 {
        0x1000000000000
    } else if n == 49 {
        0x2000000000000
    } else if n == 50 {
        0x4000000000000
    } else if n == 51 {
        0x8000000000000
    } else if n == 52 {
        0x10000000000000
    } else if n == 53 {
        0x20000000000000
    } else if n == 54 {
        0x40000000000000
    } else if n == 55 {
        0x80000000000000
    } else if n == 56 {
        0x100000000000000
    } else if n == 57 {
        0x200000000000000
    } else if n == 58 {
        0x400000000000000
    } else if n == 59 {
        0x800000000000000
    } else if n == 60 {
        0x1000000000000000
    } else if n == 61 {
        0x2000000000000000
    } else if n == 62 {
        0x4000000000000000
    } else if n == 63 {
        0x8000000000000000
    } else {
        0
    }
}

} // verus!
macro_rules! bit_shl_bound {
    ($typ:ty, $one: expr, $pname: ident) => {
        verus! {
        #[doc = "Proof that shifting 1 by N has a bound."]
        pub broadcast proof fn $pname(offset: $typ)
        requires 0 <= offset < $typ::BITS
        ensures
            #[trigger]($one << offset) == spec_bit(offset),
        {
            assert($one << offset == spec_bit(offset)) by(bit_vector);
        }
        }
    };
}

macro_rules! bit_not_properties {
    ($typ:ty, $sname: ident, $autopname: ident) => {
        verus! {
        #[doc = "Proof that !a is equal to max - a, and !!a == a"]
        pub proof fn $autopname(a: $typ)
            ensures
                !(!a) == a,
                !a == sub($typ::MAX, a)
        {
            assert(!(!a) == a) by(bit_vector);
            // usize::MAX could not be used in bit_vector.
            // Thus, check the max and replace with u64/u32::MAX
            assert(usize::MAX == u64::MAX);
            assert(usize::MAX != u32::MAX);
            assert((!a) == $typ::MAX - a) by(bit_vector);
        }
        }
    };
}

macro_rules! bit_set_clear_mask {
    ($typ:ty, $pname: ident) => {
        verus! {
        #[doc = "Proof that a mask m is set with or operation and is cleared with and operation."]
        #[verifier(bit_vector)]
        pub proof fn $pname(a: $typ, m: $typ)
            ensures
                (a & (!m)) & m == 0,
                (a & m) & m == a & m,
                (a | m) & m == m,
                (a | (!m)) & m == a & m,
        {}
        }
    };
}

// use u64/u32 proofs if the type is usize, since usize::MAX or usize:BITS are not supported by bit_vector.
bit_shl_bound! {u64, 1u64, lemma_bit_u64_shl_bound}
bit_not_properties! {u64, spec_bit_usize_not_properties, lemma_bit_u64_not_is_sub}
bit_set_clear_mask! {u64, lemma_bit_u64_set_clear_mask}
