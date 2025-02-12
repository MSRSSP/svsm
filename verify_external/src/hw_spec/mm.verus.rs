use vstd::prelude::*;
use vstd::set_lib::set_int_range;

verus! {

pub trait SpecVAddrImpl {
    spec fn spec_int_addr(&self) -> Option<int>;

    /// To a set of integer adddresses
    spec fn region_to_dom(&self, size: nat) -> Set<int>
        recommends
            self.spec_valid_size(size),
    ;

    spec fn spec_valid_size(&self, size: nat) -> bool;

    spec fn spec_valid_size_for_ptr(&self, size: nat) -> bool;

    /// Unique when casting to int address
    proof fn lemma_unique(v1: &Self, v2: &Self)
        ensures
            (v1.spec_int_addr() == v2.spec_int_addr()) == (v1 === v2),
    ;

    /// valid size = 1
    proof fn lemma_valid_size(&self, size: nat)
        ensures
            self.spec_valid_size_for_ptr(1) ==> self.spec_int_addr().is_some(),
            self.spec_valid_size_for_ptr(size) ==> self.spec_valid_size(size),
    ;

    /// If a size is valid, then smaller size must be valid
    proof fn lemma_valid_small_size(&self, size1: nat, size2: nat)
        requires
            size2 >= size1,
        ensures
            self.spec_valid_size_for_ptr(size2) ==> self.spec_valid_size_for_ptr(size1),
            self.region_to_dom(size1).subset_of(self.region_to_dom(size2)),
    ;

    // When valid, the region_to_dom() must be a continuous dom
    proof fn lemma_region_to_dom(&self, size: nat)
        requires
            self.spec_valid_size_for_ptr(size),
        ensures
            self.spec_int_addr().is_some(),
            self.region_to_dom(size) =~= set_int_range(
                self.spec_int_addr().unwrap(),
                self.spec_int_addr().unwrap() + size,
            ),
    ;
}

// Define a trait describing the memory mapping groundtruth
pub trait SpecMemMapTr {
    type VAddr;

    type PAddr;

    spec fn to_paddr(&self, vaddr: Self::VAddr) -> Option<Self::PAddr>;

    spec fn to_vaddr(&self, paddr: Self::PAddr) -> Option<Self::VAddr>;

    open spec fn is_one_to_one_mapping(&self) -> bool {
        true
    }

    open spec fn to_vaddrs(&self, paddr: Self::PAddr) -> Set<Self::VAddr> {
        let s = self.to_vaddr(paddr);
        if s.is_some() {
            set!{s.unwrap()}
        } else {
            Set::empty()
        }
    }

    open spec fn get_paddr(&self, vaddr: Self::VAddr) -> Self::PAddr
        recommends
            self.to_paddr(vaddr).is_some(),
    {
        self.to_paddr(vaddr).unwrap()
    }

    open spec fn get_vaddr(&self, paddr: Self::PAddr) -> Self::VAddr
        recommends
            self.is_one_to_one_mapping(),
            self.to_vaddr(paddr).is_some(),
    {
        self.to_vaddr(paddr).unwrap()
    }

    proof fn proof_one_to_one_mapping(&self, addr: Self::PAddr)
        requires
            self.is_one_to_one_mapping(),
        ensures
            self.to_vaddrs(addr).len() <= 1,
            self.to_vaddr(addr).is_some() ==> self.to_paddr(self.get_vaddr(addr)).is_some(),
    ;

    proof fn proof_correct_mapping_vaddr(&self, addr: Self::VAddr)
        requires
            self.to_paddr(addr).is_some(),
        ensures
            self.to_vaddrs(self.get_paddr(addr)).contains(addr),
    ;

    proof fn proof_correct_mapping_paddr(&self, addr: Self::PAddr)
        ensures
            (self.to_vaddrs(addr).len() > 0) == self.to_vaddr(addr).is_some(),
            self.to_vaddr(addr).is_some() ==> self.to_vaddrs(addr).contains(self.get_vaddr(addr)),
            self.to_vaddrs(addr).len() > 0 ==> self.to_vaddrs(addr).contains(self.get_vaddr(addr)),
    ;

    proof fn proof_correct_mapping_addrs(&self, addr: Self::PAddr, vaddr: Self::VAddr)
        requires
            self.to_vaddrs(addr).contains(vaddr),
        ensures
            self.to_paddr(vaddr) === Some(addr),
    ;
}

} // verus!
