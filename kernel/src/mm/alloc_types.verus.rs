// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// Proves the encode/decode functions used in alloc.rs.
verus! {

trait SpecDecoderProof<T>: core::marker::Sized {
    spec fn spec_decode(mem: T) -> Option<Self> {
        if exists|x: Self| #[trigger] x.spec_encode() === Some(mem) {
            Some(choose|x: Self| #[trigger] x.spec_encode() === Some(mem))
        } else {
            None
        }
    }

    spec fn spec_encode(&self) -> Option<T>; 
    /*{
        if exists|x: T| #[trigger] Self::spec_decode(x) === Some(*self) {
            Some(choose|x: T| #[trigger] Self::spec_decode(x) === Some(*self))
        } else {
            None
        }
    }*/

    spec fn spec_encode_req(&self) -> bool {
        true
    }

    proof fn proof_encode_decode(&self)
        requires
            self.spec_encode().is_some(),
        ensures
            Self::spec_decode(self.spec_encode().unwrap()) === Some(*self),
    ;
}

impl SpecDecoderProof<PageStorageType> for PageType {
    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType(*self as u64))
    }

    #[verifier::spinoff_prover]
    proof fn proof_encode_decode(&self) {
    }
}

impl FreeInfo {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        &&& self.next_page < MAX_PAGE_COUNT
        &&& self.order < MAX_ORDER
    }
}

impl SpecDecoderProof<PageStorageType> for FreeInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        if PageType::spec_decode(mem) == Some(PageType::Free) {
            let order = ((mem.0 >> 4) & 0xff) as usize;
            let next_page = (mem.0 >> 12) as usize;
            Some(FreeInfo { next_page, order })
        } else {
            None
        }
    }

    spec fn spec_encode_req(&self) -> bool {
        self.inv()
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType(((self.order as u64 & 0xff) << 4) | ((self.next_page as u64) << 12) | PageType::Free as u64))
    }

    #[verifier(external_body)]
    proof fn proof_encode_decode(
        &self,
    );
    /*{
        assert forall |v1: u64, v2: u64|
            v1 <= 0xff && v2 <= (usize::MAX << 12)
        implies
            (((v1 << 4) | (v2 << 12)) >> 4) & 0xff == v1 &&
            (((v1 << 4) | (v2 << 12)) >> 12) == v2
        by {}
        let order = self.order as u64;
        let next_page = self.next_page as u64;
        let val1 = ((order & 0xff) << 4);
        let val2 =  (next_page << 12);
        let val = val1 | val2;
        let order = (val >> 4) & 0xff;
        let next_page = (val >> 12);
    }*/

}

impl SpecDecoderProof<PageStorageType> for AllocatedInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        if PageType::spec_decode(mem) == Some(PageType::Allocated) {
            let order = ((mem.0 >> 4) & 0xff) as usize;
            Some(AllocatedInfo { order })
        } else {
            None
        }
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType(((self.order as u64 & 0xff) << 4) | PageType::Allocated as u64))
    }

    #[verifier(external_body)]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::Allocated),
    {
        //PageType::Allocated.proof_encode_decode()
    }
}

impl SpecDecoderProof<PageStorageType> for SlabPageInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        if PageType::spec_decode(mem) == Some(PageType::SlabPage) {
            let item_size = ((mem.0 >> 4) & 0xffff);
            Some(SlabPageInfo { item_size })
        } else {
            None
        }
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType(((self.item_size & 0xffff) << 4) | PageType::SlabPage as u64))
    }

    #[verifier(external_body)]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::SlabPage),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for CompoundInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        if PageType::spec_decode(mem) == Some(PageType::Compound) {
            let order = ((mem.0 >> 4) & 0xff) as usize;
            Some(CompoundInfo { order })
        } else {
            None
        }
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType(((self.order as u64 & 0xffu64) << 4) | PageType::Compound as u64))
    }

    #[verifier(external_body)]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::Compound),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for FileInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        if PageType::spec_decode(mem) == Some(PageType::File) {
            let ref_count = (mem.0 >> 4);
            Some(FileInfo { ref_count })
        } else {
            None
        }
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType((self.ref_count << 4) | PageType::File as u64))
    }

    #[verifier(external_body)]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::File),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for ReservedInfo {
    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType(PageType::Reserved as u64))
    }

    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        if PageType::spec_decode(mem) == Some(PageType::Reserved) {
            Some(ReservedInfo)
        } else {
            None
        }
    }

    #[verifier(external_body)]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::Reserved),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for PageInfo {
    closed spec fn spec_encode(&self) -> Option<PageStorageType> {
        match self {
            Self::Free(fi) => fi.spec_encode(),
            Self::Allocated(ai) => ai.spec_encode(),
            Self::Slab(si) => si.spec_encode(),
            Self::Compound(ci) => ci.spec_encode(),
            Self::File(fi) => fi.spec_encode(),
            Self::Reserved(ri) => ri.spec_encode(),
        }
    }

    uninterp spec fn spec_decode(v: PageStorageType) -> Option<PageInfo>; /*{
        let mem_type = PageType::spec_decode(PageStorageType(v.0 & 0xF));
        if mem_type.is_none() {
            None
        } else {
            match mem_type.unwrap() {
                PageType::Free => if let Some(fi) = FreeInfo::spec_decode(v) {
                    Some(PageInfo::Free(fi))
                } else {
                    None
                }
                PageType::Allocated => if let Some(fi) = AllocatedInfo::spec_decode(v) {
                    Some(PageInfo::Allocated(fi))
                } else {
                    None
                }
                PageType::SlabPage => if let Some(fi) = SlabPageInfo::spec_decode(v) {
                    Some(PageInfo::Slab(fi))
                } else {
                    None
                }
                PageType::Compound => if let Some(fi) = CompoundInfo::spec_decode(v) {
                    Some(PageInfo::Compound(fi))
                } else {
                    None
                }
                PageType::File => if let Some(fi) = FileInfo::spec_decode(v) {
                    Some(PageInfo::File(fi))
                } else {
                    None
                }
                PageType::Reserved => if let Some(fi) = ReservedInfo::spec_decode(v) {
                    Some(PageInfo::Reserved(fi))
                } else {
                    None
                }
            }
        }
    }*/

    #[verifier(external_body)]
    proof fn proof_encode_decode(&self) {
    }
}

impl PageStorageType {
    pub closed spec fn view(&self) -> u64 {
        self.0
    }

    pub closed spec fn spec_new(v: u64) -> Self {
        PageStorageType(v)
    }
}

} // verus!
