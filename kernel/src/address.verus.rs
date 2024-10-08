// SPDX-License-Identifier: MIT
//
// Copyright (c) 2022-2023 Microsoft
//
// Author: Ziqiao Zhou<ziqiaozhou@microsoft.com>
verus! {

spec fn sign_extend_ensures(addr: InnerAddr, ret: InnerAddr, sign_bit: usize) -> bool {
    let mask: InnerAddr = (1 as InnerAddr) << sign_bit;
    let lower_mask: InnerAddr = (mask - 1 as InnerAddr) as InnerAddr;
    let upper_mask: InnerAddr = !lower_mask;
    if addr & mask == mask {
        &&& (ret & lower_mask == addr & lower_mask)
        &&& (ret & upper_mask == upper_mask)
    } else {
        ret == (addr & lower_mask)
    }
}

} // verus!
