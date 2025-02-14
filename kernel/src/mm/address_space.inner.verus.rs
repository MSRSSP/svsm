// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// This module defines specification helper functions to verify the correct use of memory.
//
// Trusted Assumptions:
// - hw_spec::SpecMemMapTr is correct
// Proofs:
// - LinearMap satisfy all properties in hw_spec::SpecMemMapTr  


verus! {
#[allow(missing_debug_implementations)]
pub ghost struct LinearMap {
    pub start_virt: VirtAddr,
    pub start_phys: int,
    pub size: nat,
}

impl LinearMap {
    pub open spec fn spec_new(virt_start: VirtAddr, virt_end: VirtAddr, phys_start: PhysAddr) -> LinearMap {
        LinearMap { start_virt: virt_start, start_phys: phys_start@ as int, size: (virt_end.offset() - virt_start.offset()) as nat}
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.start_virt.is_canonical()
        &&& self.start_virt.offset() + self.size <= crate::address::VADDR_RANGE_SIZE
    }

    pub closed spec fn try_get_virt(&self, pfn: usize) -> Option<VirtAddr> {
        let phy = self.start_phys + pfn * crate::types::PAGE_SIZE;
        self.to_vaddr(phy)
    }

    pub proof fn lemma_get_virt(&self, pfn: usize) -> (ret: VirtAddr)
        requires
            self.wf(),
            pfn < self.size / crate::types::PAGE_SIZE as nat,
        ensures
            ret == self.try_get_virt(pfn).unwrap(),
            self.try_get_virt(pfn).is_some(),
            ret.is_canonical(),
            ret.offset() == self.start_virt.offset() + (pfn * crate::types::PAGE_SIZE),
    {
        broadcast use crate::types::lemma_page_size;

        reveal(<LinearMap as SpecMemMapTr>::to_vaddr);
        VirtAddr::lemma_wf((self.start_virt.offset() + (pfn * crate::types::PAGE_SIZE)) as usize);
        self.try_get_virt(pfn).unwrap()
    }
}

impl SpecMemMapTr for LinearMap {
    type VAddr = VirtAddr;

    type PAddr = int;

    #[verifier(opaque)]
    open spec fn to_vaddrs(&self, paddr: int) -> Set<VirtAddr> {
        let s = self.to_vaddr(paddr);
        if s.is_some() {
            set!{s.unwrap()}
        } else {
            Set::empty()
        }
    }

    #[verifier(opaque)]
    open spec fn to_vaddr(&self, paddr: int) -> Option<VirtAddr> {
        let offset = paddr - self.start_phys;
        if 0 <= offset < self.size && (self.start_virt.offset() + offset < VADDR_RANGE_SIZE)
            && self.start_virt.is_canonical() {
            let inner = (self.start_virt.offset() + offset) as usize;
            Some(VirtAddr::from_spec(inner))
        } else {
            None
        }
    }

    #[verifier(opaque)]
    open spec fn to_paddr(&self, vaddr: VirtAddr) -> Option<int> {
        let offset = vaddr.offset() - self.start_virt.offset();
        if 0 <= offset < self.size && (self.start_virt.offset() + offset < VADDR_RANGE_SIZE)
            && self.start_virt.is_canonical() && vaddr.is_canonical() {
            Some(self.start_phys + offset)
        } else {
            None
        }
    }

    open spec fn is_one_to_one_mapping(&self) -> bool {
        true
    }

    proof fn proof_one_to_one_mapping(&self, paddr: Self::PAddr) {
        reveal(<LinearMap as SpecMemMapTr>::to_vaddr);
        reveal(<LinearMap as SpecMemMapTr>::to_vaddrs);
        reveal(<LinearMap as SpecMemMapTr>::to_paddr);
        let offset = paddr - self.start_phys;
        let inner = (self.start_virt.offset() + offset) as usize;
        VirtAddr::lemma_wf(inner);
    }

    proof fn proof_correct_mapping_vaddr(&self, addr: Self::VAddr) {
        reveal(<LinearMap as SpecMemMapTr>::to_vaddr);
        reveal(<LinearMap as SpecMemMapTr>::to_vaddrs);
        reveal(<LinearMap as SpecMemMapTr>::to_paddr);
        let offset = self.to_paddr(addr).unwrap() - self.start_phys;
        let inner = (self.start_virt.offset() + offset) as usize;
        addr.property_canonical();
    }

    proof fn proof_correct_mapping_paddr(&self, paddr: Self::PAddr) {
        reveal(<LinearMap as SpecMemMapTr>::to_vaddr);
        reveal(<LinearMap as SpecMemMapTr>::to_vaddrs);
        reveal(<LinearMap as SpecMemMapTr>::to_paddr);
        VirtAddr::lemma_wf((self.start_virt.offset() + paddr - self.start_phys) as usize);
    }

    proof fn proof_correct_mapping_addrs(&self, paddr: Self::PAddr, vaddr: Self::VAddr) {
        reveal(<LinearMap as SpecMemMapTr>::to_vaddr);
        reveal(<LinearMap as SpecMemMapTr>::to_vaddrs);
        reveal(<LinearMap as SpecMemMapTr>::to_paddr);
        VirtAddr::lemma_wf((self.start_virt.offset() + paddr - self.start_phys) as usize);
    }
}

} // verus!
