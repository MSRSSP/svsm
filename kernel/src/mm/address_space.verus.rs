use crate::address::VADDR_RANGE_SIZE;
use verify_external::convert::FromSpec;
use vstd::prelude::*;
verus! {

use verify_external::hw_spec::SpecMemMapTr;

pub struct LinearMap {
    pub start_virt: VirtAddr,
    pub start_phys: int,
    pub size: nat,
}

impl SpecMemMapTr for LinearMap {
    type VAddr = VirtAddr;

    type PAddr = int;

    open spec fn to_vaddrs(&self, paddr: int) -> Set<VirtAddr> {
        let s = self.to_vaddr(paddr);
        if s.is_some() {
            set!{s.unwrap()}
        } else {
            Set::empty()
        }
    }

    open spec fn to_vaddr(&self, paddr: int) -> Option<VirtAddr> {
        let offset = paddr - self.start_phys;
        if 0 <= offset < self.size && self.start_virt.offset() + offset < VADDR_RANGE_SIZE {
            let inner = (self.start_virt@ + offset) as usize;
            Some(VirtAddr::from_spec(inner))
        } else {
            None
        }
    }

    open spec fn to_paddr(&self, vaddr: VirtAddr) -> Option<int> {
        let offset = vaddr.offset() - self.start_virt.offset();
        if 0 <= offset < self.size {
            Some(self.start_phys + offset)
        } else {
            None
        }
    }

    open spec fn is_one_to_one_mapping(&self) -> bool {
        true
    }
}

} // verus!
