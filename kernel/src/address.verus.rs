// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
use vmath::bits::{
    lemma_bit_u64_not_is_sub, lemma_bit_u64_set_clear_mask, lemma_bit_u64_shl_bound,
};

verus! {

#[verifier(inline)]
/// Ensures that ret is a new canonical virtual address, throwing out bits 48..64.
spec fn sign_extend_ensures(addr: InnerAddr, ret: InnerAddr) -> bool {
    let sign_mask: InnerAddr = (1usize as InnerAddr) << 47;
    let lower_mask: InnerAddr = sub(sign_mask, (1usize as InnerAddr));
    let upper_mask: InnerAddr = !lower_mask;
    let is_signed = (addr & sign_mask == sign_mask);

    &&& (ret & lower_mask == addr & lower_mask)
    &&& is_signed ==> (ret & upper_mask) == upper_mask
    &&& !is_signed ==> (ret & upper_mask) == 0
    &&& !is_signed ==> ret == (addr & lower_mask)
}

} // verus!
#[inline]
#[ensures(|ret: InnerAddr| [sign_extend_ensures(addr, ret)])]
// Different proof blocks without calling helper proofs.
const fn sign_extend_different_proof(addr: InnerAddr) -> InnerAddr {
    let mask = 1usize << SIGN_BIT;

    if (addr & mask) == mask {
        proof! {
            lemma_bit_u64_shl_bound(SIGN_BIT as u64);
            assert(sign_extend_ensures(addr, addr | !sub(mask, 1))) by (bit_vector)
            requires mask == (1usize << 47), (addr & mask) == mask;
        }
        addr | !((1usize << SIGN_BIT) - 1)
    } else {
        proof! {
            lemma_bit_u64_shl_bound(SIGN_BIT as u64);
            assert(sign_extend_ensures(addr, addr & sub(mask, 1)))
            by (bit_vector) requires mask == 1usize << 47, (addr & mask) != mask;
        }
        addr & ((1usize << SIGN_BIT) - 1)
    }
}

// A different implementation of sign_extend2.
// The expected results is the same but impl and proof could be different.
#[verus_verify]
#[ensures(|ret: InnerAddr| [sign_extend_ensures(addr, ret)])]
const fn sign_extend_different_impl(addr: InnerAddr) -> InnerAddr {
    let left_bits = InnerAddr::BITS as usize - SIGN_BIT - 1;

    proof! {
        assert(sign_extend_ensures(addr, ((addr << 16) as i64 >> 16) as InnerAddr))
        by (bit_vector);
    }
    ((addr << left_bits) as i64 >> left_bits) as InnerAddr
}
