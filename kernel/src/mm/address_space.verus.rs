use crate::address::VADDR_RANGE_SIZE;
use verify_external::convert::FromSpec;
use vstd::prelude::*;
verus! {

use verify_external::hw_spec::SpecMemMapTr;

#[allow(missing_debug_implementations)]
pub struct LinearMap {
    pub start_virt: VirtAddr,
    pub start_phys: int,
    pub size: nat,
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
