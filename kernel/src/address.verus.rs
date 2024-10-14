// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
verus! {

#[verifier(inline)]
pub open spec fn vaddr_lower_mask() -> InnerAddr {
    0x7FFF_FFFF_FFFFu64 as InnerAddr
}

#[verifier(inline)]
spec fn check_signed(addr: InnerAddr) -> bool {
    addr & (1usize << 47) == 1usize << 47
}

#[verifier(inline)]
pub open spec fn vaddr_upper_mask() -> InnerAddr {
    !vaddr_lower_mask()
}

#[verifier(inline)]
pub open spec fn vaddr_lower_bits(addr: InnerAddr) -> InnerAddr {
    addr & vaddr_lower_mask()
}

#[verifier(inline)]
spec fn vaddr_upper_bits(addr: InnerAddr) -> InnerAddr {
    addr & vaddr_upper_mask()
}

#[verifier(inline)]
spec fn vaddr_is_signed(addr: InnerAddr) -> bool {
    addr & vaddr_upper_mask() == vaddr_upper_mask()
}

#[verifier(inline)]
pub open spec fn vaddr_is_valid(addr: InnerAddr) -> bool {
    addr & vaddr_upper_mask() == 0
}

/// Ensures that ret is a new canonical virtual address, throwing out bits 48..64.
#[verifier(inline)]
spec fn sign_extend_ensures(addr: InnerAddr, ret: InnerAddr) -> bool {
    let upper = vaddr_upper_bits(ret);
    let lower = vaddr_lower_bits(ret);
    &&& (lower == vaddr_lower_bits(addr))
    &&& check_signed(addr) ==> (vaddr_is_signed(ret) && (ret == lower + vaddr_upper_mask()))
    &&& !check_signed(addr) ==> (vaddr_is_valid(ret) && (ret == lower))
}

pub closed spec fn new_vaddr_ensures(addr: InnerAddr, ret: InnerAddr) -> bool {
    sign_extend_ensures(addr, ret)
}

proof fn lemma_inner_addr_as_vaddr(bits: InnerAddr)
    ensures
        vaddr_is_signed(bits) == (bits >= vaddr_upper_mask()),
        vaddr_is_valid(bits) == (bits <= vaddr_lower_mask()),
        vaddr_is_valid(bits) ==> vaddr_lower_bits(bits) == bits,
        vaddr_is_signed(bits) ==> vaddr_upper_bits(bits) + vaddr_lower_bits(bits) == bits,
        vaddr_upper_mask() > vaddr_lower_mask(),
        vaddr_is_signed(bits) ==> check_signed(bits),
{
    broadcast use sign_extend_proof;

    assert(vaddr_is_signed(bits) == (bits >= vaddr_upper_mask())) by (bit_vector);
    assert(vaddr_is_signed(bits) ==> check_signed(bits)) by (bit_vector);
    assert(vaddr_is_valid(bits) == (bits <= vaddr_lower_mask())) by (bit_vector);
}

broadcast group sign_extend_proof {
    verismo::bits::lemma_bit_usize_not_is_sub,
    verismo::bits::lemma_bit_usize_shl_values,
    verismo::bits::lemma_bit_usize_or_mask,
    verismo::bits::lemma_bit_usize_and_mask,
}

broadcast group vaddr_properties {
    sign_extend_proof,
    VirtAddr::lemma_range,
}

pub trait SpecInnerAddr {
    spec fn spec_bits(&self) -> InnerAddr;
}

impl SpecInnerAddr for VirtAddr {
    closed spec fn spec_bits(&self) -> InnerAddr {
        self.0
    }
}

impl VirtAddr {
    /* Specifications for the struct */
    /// A valid virtual address have a canonical form where the upper bits are either all zeroes or all ones
    #[verifier::type_invariant]
    pub closed spec fn is_canonical_vaddr(&self) -> bool {
        vaddr_is_valid(self.spec_bits()) || vaddr_is_signed(self.spec_bits())
    }

    pub closed spec fn spec_lower_bits(&self) -> InnerAddr {
        vaddr_lower_bits(self.spec_bits())
    }

    pub closed spec fn valid_access(&self) -> bool {
        vaddr_is_valid(self.spec_bits())
    }

    /* Specifications for methods */
    // requires that adding offset will not cause not overflow.
    // If the address is valid, it should not exceed max valid address;
    // If the address is invalid, it will not exceed usize::max;
    pub open spec fn const_add_requires(&self, offset: usize) -> bool {
        &&& self.is_canonical_vaddr()
        &&& self.valid_access() ==> self.spec_bits() + offset <= vaddr_lower_mask()
        &&& self.spec_bits() + offset < usize::MAX
    }

    #[inline]
    pub open spec fn const_add_ensures(&self, offset: usize, ret: VirtAddr) -> bool {
        &&& ret.is_canonical_vaddr()
        &&& ret.valid_access() == self.valid_access()
        &&& self.valid_access() ==> (ret.spec_bits() == self.spec_bits() + offset)
    }

    /// The two address must be both valid or both invalid.
    pub open spec fn sub_requires(&self, other: Self) -> bool {
        &&& self.is_canonical_vaddr()
        &&& other.is_canonical_vaddr()
        &&& self.spec_bits() >= other.spec_bits()
    }

    pub open spec fn sub_ensures(&self, other: Self, ret: InnerAddr) -> bool {
        (self.valid_access() == other.valid_access()) ==> (ret == self.spec_bits()
            - other.spec_bits())
    }

    pub open spec fn sub_usize_requires(&self, other: usize) -> bool {
        &&& self.is_canonical_vaddr()
        &&& self.spec_bits() >= other
        &&& other <= self.spec_lower_bits()
    }

    pub open spec fn sub_usize_ensures(&self, other: usize, ret: Self) -> bool {
        ret.const_add_ensures(other, *self)
    }

    /* Proofs for the struct */
    // Proves that a valid virtual address falls into [0, 0x00007FFFFFFFFFFF]
    broadcast proof fn lemma_range(vaddr: VirtAddr)
        requires
            #[trigger] vaddr.is_canonical_vaddr(),
        ensures
            vaddr.valid_access() == (vaddr.spec_bits() <= vaddr_lower_mask()),
            !vaddr.valid_access() == (vaddr.spec_bits() >= vaddr_upper_mask()),
            vaddr.valid_access() ==> vaddr.spec_bits() == vaddr.spec_lower_bits(),
            !vaddr.valid_access() ==> vaddr.spec_bits() == vaddr.spec_lower_bits()
                + vaddr_upper_mask(),
    {
        lemma_inner_addr_as_vaddr(vaddr.spec_bits());
    }
}

impl SpecInnerAddr for PhysAddr {
    closed spec fn spec_bits(&self) -> InnerAddr {
        self.0
    }
}

} // verus!
/// A different implementation of sign_extend2.
/// The expected results is the same but impl and proof could be different.
#[cfg(verus_keep_ghost)]
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
