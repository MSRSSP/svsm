// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
verus! {

#[verifier(inline)]
/// Ensures that ret is a new canonical virtual address, throwing out bits 48..64.
spec fn sign_extend_ensures(addr: InnerAddr, ret: InnerAddr) -> bool {
    let sign_mask = (1usize as InnerAddr) << 47;
    let lower_mask = sub(sign_mask, (1usize as InnerAddr));
    let upper_mask = !lower_mask;
    let is_signed = (addr & sign_mask == sign_mask);
    let upper = ret & upper_mask;

    &&& (ret & lower_mask == addr & lower_mask)
    &&& is_signed ==> upper == upper_mask
    &&& !is_signed ==> upper == 0
}

impl VirtAddr {
    /// A valid virtual address have a canonical form where the upper bits are either all zeroes or all ones
    #[verifier::type_invariant]
    pub closed spec fn is_canonical_vaddr(&self) -> bool {
        let vaddr = self.0;
        let upper_mask = !sub(1usize << 47, 1);
        let upper = vaddr & upper_mask;
        (upper == upper_mask) || (upper == 0)
    }

    pub closed spec fn spec_bits(&self) -> InnerAddr {
        self.0
    }
}

broadcast proof fn zero_is_canonical_vaddr(x: VirtAddr)
    ensures
        (x.spec_bits() == 0) ==> #[trigger] x.is_canonical_vaddr(),
{
    assert(sign_extend_ensures(0, 0)) by (bit_vector);
}

broadcast group address_properties {
    zero_is_canonical_vaddr,
}

broadcast group sign_extend_proof {
    verismo::bits::lemma_bit_usize_not_is_sub,
    verismo::bits::lemma_bit_usize_shl_bound,
    verismo::bits::lemma_bit_usize_set_mask,
    verismo::bits::lemma_bit_usize_clear_mask,
}

} // verus!
/// A different implementation of sign_extend2.
/// The expected results is the same but impl and proof could be different.
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
