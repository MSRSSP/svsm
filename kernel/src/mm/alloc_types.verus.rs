// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// Proves the encode/decode functions used in alloc.rs.
verus! {

trait SpecDecoderProof<T>: core::marker::Sized {
    spec fn spec_decode(mem: T) -> Option<Self>;

    #[verifier(inline)]
    spec fn spec_encode(&self) -> Option<T> {
        if exists|x: T| #[trigger] Self::spec_decode(x) === Some(*self) {
            Some(choose|x: T| #[trigger] Self::spec_decode(x) === Some(*self))
        } else {
            None
        }
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

    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::Free),
    {
    }
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

    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::Allocated),
    {
        PageType::Allocated.proof_encode_decode()
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

    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::File),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for ReservedInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        if PageType::spec_decode(mem) == Some(PageType::Reserved) {
            Some(ReservedInfo)
        } else {
            None
        }
    }

    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::Reserved),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for PageInfo {
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

    proof fn proof_encode_decode(&self) {
        match self {
            Self::Free(fi) => fi.proof_encode_decode(),
            Self::Allocated(ai) => ai.proof_encode_decode(),
            Self::Slab(si) => si.proof_encode_decode(),
            Self::Compound(ci) => ci.proof_encode_decode(),
            Self::File(fi) => fi.proof_encode_decode(),
            Self::Reserved(ri) => ri.proof_encode_decode(),
        }
    }
}

} // verus!
