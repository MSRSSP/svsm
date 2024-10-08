// SPDX-License-Identifier: MIT
//
// Copyright (c) 2022-2023 Microsoft
//
// Author: Ziqiao Zhou<ziqiaozhou@microsoft.com>
use vstd::prelude::*;

macro_rules! bit_shl_properties {
    ($typ:ty, $size:expr, $max: expr, $pname: ident) => {
        verus! {
        pub proof fn $pname(offset: $typ) -> (ret: $typ)
        requires 0 <= offset < $size
        ensures
            ret == (1 as $typ) << offset,
            1 <= ret <= $max,
        {
            assert(((1 as $typ) << offset) >= 1) by(bit_vector)
            requires  0 <= offset < $size;
            assert(((1 as $typ) << offset) <= $max) by(bit_vector)
            requires  0 <= offset < $size;
            (1 as $typ) << offset
        }
        }
    };
}

macro_rules! bit_or_properties {
    ($typ:ty, $max:expr, $sname: ident, $pname: ident, $autopname: ident) => {
        verus! {
        #[verifier(inline)]
        pub open spec fn $sname(a: $typ, b: $typ, ret: $typ) -> bool {
            &&& ret == (a | b)
            &&& ret == (b | a)
            &&& 0 <= ret <= $max
            &&& ret & b == b
            &&& ret >= a
            &&& ret >= b
            &&& ret & !b == a & !b
            &&& ret <= a + b
        }

        #[verifier(bit_vector)]
        pub proof fn $pname(a: $typ, b: $typ)
            ensures
                $sname(a, b, (a|b))
        {}

        pub proof fn $autopname()
            ensures
                forall|a: $typ, b: $typ| $sname(a, b, #[trigger](a|b)),
        {
            assert forall|a: $typ, b: $typ| $sname(a, b, #[trigger](a|b)) by {
                $pname(a, b);
            }
        }
        }
    };
}

macro_rules! bit_not_properties {
    ($typ:ty, $max:expr, $sname: ident, $autopname: ident) => {
        verus! {
        #[verifier(inline)]
        pub open spec fn $sname(a: $typ, ret: $typ) -> bool {
            &&& ret == (!a)
            &&& ret & a == 0
            &&& ret == sub($max, a)
            &&& 0 <= ret <= $max
            &&& !ret == a
        }

        #[verifier(bit_vector)]
        pub proof fn $autopname()
            ensures
                forall|a: $typ| $sname(a, #[trigger](!a)),
                !(0 as $typ) == $max,
        {}
        }
    };
}

bit_shl_properties! {usize, 64, 1usize << 63usize, proof_usize_bitshl_bound}
bit_or_properties! {usize, 0xffff_ffff_ffff_ffff, spec_usize_bitor_properties, proof_usize_bitor_properties, proof_usize_bitor_auto}
bit_not_properties! {usize, 0xffff_ffff_ffff_ffff, spec_usize_bitnot_properties, proof_usize_bitnot_auto}
