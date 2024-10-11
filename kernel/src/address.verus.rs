// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
use vmath::bits::{
    lemma_bit_u64_not_is_sub, lemma_bit_u64_set_clear_mask, lemma_bit_u64_shl_bound,
};

verus! {

spec fn sign_extend_ensures(addr: InnerAddr, ret: InnerAddr, sign_bit: usize) -> bool {
    let sign_mask: InnerAddr = (1 as InnerAddr) << sign_bit;
    let lower_mask: InnerAddr = (sign_mask - 1 as InnerAddr) as InnerAddr;
    let upper_mask: InnerAddr = !lower_mask;
    let is_signed = (addr & sign_mask == sign_mask);

    &&& (ret & lower_mask == addr & lower_mask)
    &&& is_signed ==> (ret & upper_mask) == upper_mask
    &&& !is_signed ==> (ret & upper_mask) == 0
    &&& !is_signed ==> ret == (addr & lower_mask)
}

} // verus!
