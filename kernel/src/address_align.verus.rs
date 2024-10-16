// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
verus! {

use verismo::convert::{FromSpec, from_spec, axiom_from_spec};

pub open spec fn align_requires(align: InnerAddr) -> bool {
    &&& verismo::bits::is_pow_of_2(align as u64)
}

pub closed spec fn _align_up_requires(bits: InnerAddr, align: InnerAddr) -> bool {
    &&& align_requires(align)
    &&& bits + (align - 1) <= InnerAddr::MAX
}

pub closed spec fn align_up_requires(bits: InnerAddr, align: InnerAddr) -> bool {
    &&& _align_up_requires(bits, align)
}

pub open spec fn align_up_spec(val: InnerAddr, align: InnerAddr) -> InnerAddr {
    let r = val % align;
    &&& if r == 0 {
        val
    } else {
        (val - r + align) as InnerAddr
    }
}

pub open spec fn align_up_ensures(val: InnerAddr, align: InnerAddr, ret: InnerAddr) -> bool {
    let r = val % align;
    &&& ret % align == 0
    &&& ret >= val
    &&& ret == align_up_spec(val, align)
}

pub open spec fn align_down_spec(val: InnerAddr, align: InnerAddr) -> int {
    val - val % align
}

pub open spec fn is_aligned_spec(val: InnerAddr, align: InnerAddr) -> bool {
    val % align == 0
}

} // verus!
verus! {

impl<T> FromSpec<*mut T> for VirtAddr {
    closed spec fn from_spec(v: *mut T) -> Self {
        VirtAddr(sign_extend_spec(v as InnerAddr))
    }
}

impl<T> FromSpec<*const T> for VirtAddr {
    closed spec fn from_spec(v: *const T) -> Self {
        VirtAddr(sign_extend_spec(v as InnerAddr))
    }
}

impl FromSpec<InnerAddr> for VirtAddr {
    closed spec fn from_spec(v: InnerAddr) -> Self {
        VirtAddr(sign_extend_spec(v))
    }
}

impl FromSpec<VirtAddr> for InnerAddr {
    open spec fn from_spec(v: VirtAddr) -> Self {
        v@
    }
}

impl FromSpec<VirtAddr> for u64 {
    open spec fn from_spec(v: VirtAddr) -> Self {
        v@ as u64
    }
}

broadcast group align_up_proof {
    verismo::bits::lemma_bit_usize_shl_values,
    verismo::bits::lemma_bit_u64_shl_values,
    vstd::bits::lemma_u64_pow2_no_overflow,
    verismo::bits::lemma_bit_usize_and_mask,
    verismo::bits::lemma_bit_usize_and_mask_is_mod,
}

pub proof fn proof_align_up(x: usize, align: usize)
    requires
        align_up_requires(x, align),
    ensures
        add(x, sub(align, 1)) & !sub(align, 1) == align_up_spec(x, align),
{
    broadcast use align_up_proof;

    let mask = (align - 1) as usize;
    let y = (x + mask) as usize;
    assert(y & !mask == sub(y, y & mask));

    if x % align == 0 {
        assert((x + (align - 1)) % (align as int) == align - 1) by (nonlinear_arith)
            requires
                x % align == 0,
                align > 0,
        ;
    } else {
        assert((x + (align - 1)) % (align as int) == (x % align - 1) as int) by (nonlinear_arith)
            requires
                x % align != 0,
                align > 0,
        ;
    }
}

pub proof fn lemma_align_down(x: usize, align: usize)
    requires
        align_requires(align),
    ensures
        x & !((align - 1) as usize) == align_down_spec(x, align),
{
    let mask: usize = sub(align, 1);
    assert(x == (x & !mask) + (x & mask));
}

broadcast group address_proof {
    crate::types::group_types_proof,
    axiom_from_spec,
    verismo::bits::lemma_bit_usize_shl_values,
    verismo::bits::lemma_bit_usize_and_mask_is_mod,
}

} // verus!
