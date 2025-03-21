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
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        match mem.0 {
            0 => Some(PageType::Free),
            1 => Some(PageType::Allocated),
            2 => Some(PageType::SlabPage),
            3 => Some(PageType::Compound),
            4 => Some(PageType::File),
            15 => Some(PageType::Reserved),
            _ => None,
        }
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        let val = match self {
            PageType::Free => 0,
            PageType::Allocated => 1,
            PageType::SlabPage => 2,
            PageType::Compound => 3,
            PageType::File => 4,
            PageType::Reserved => 15,
        };
        Some(PageStorageType(val))
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
        Some(PageStorageType(((self.order as u64 & 0xff) << 4) | ((self.next_page as u64) << 12)))
    }

    #[verifier(external_body)]
    proof fn proof_encode_decode(
        &self,
    );/*
    {
        assert forall |v1: u64, v2: u64|
            v1 <= 0xff && v2 <= (usize::MAX << 12)
        implies
            (((v1 << 4) | (v2 << 12)) >> 4) == v1 &&
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
        Some(PageStorageType(((self.order as u64 & 0xff) << 4) | 0x1))
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
        Some(PageStorageType(((self.item_size & 0xffff) << 4) | 0x2))
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
        Some(PageStorageType(((self.order as u64 & 0xffu64) << 4) | 0x3))
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
        Some(PageStorageType((self.ref_count << 4) | 0x4))
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
        Some(PageStorageType(5))
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

    closed spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        let typ = PageType::spec_decode(mem);
        match typ {
            Some(typ) => Some(
                match typ {
                    PageType::Free => Self::Free(FreeInfo::spec_decode(mem).unwrap()),
                    PageType::Allocated => Self::Allocated(
                        AllocatedInfo::spec_decode(mem).unwrap(),
                    ),
                    PageType::SlabPage => Self::Slab(SlabPageInfo::spec_decode(mem).unwrap()),
                    PageType::Compound => Self::Compound(CompoundInfo::spec_decode(mem).unwrap()),
                    PageType::File => Self::File(FileInfo::spec_decode(mem).unwrap()),
                    PageType::Reserved => Self::Reserved(ReservedInfo::spec_decode(mem).unwrap()),
                },
            ),
            _ => { None },
        }
    }

    #[verifier(external_body)]
    proof fn proof_encode_decode(&self) {
        /*match self {
            Self::Free(fi) => fi.proof_encode_decode(),
            Self::Allocated(ai) => ai.proof_encode_decode(),
            Self::Slab(si) => si.proof_encode_decode(),
            Self::Compound(ci) => ci.proof_encode_decode(),
            Self::File(fi) => fi.proof_encode_decode(),
            Self::Reserved(ri) => ri.proof_encode_decode(),
        }*/
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
