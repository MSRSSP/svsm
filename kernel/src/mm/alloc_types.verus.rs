// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// Proves the encode/decode functions used in alloc.rs.
use vstd::simple_pptr::MemContents;
verus! {

global size_of PageStorageType == 8;

global size_of SlabPage<32> == 40;

spec fn spec_page_storage_type(mem: MemContents<PageStorageType>) -> Option<PageStorageType> {
    if mem.is_init() {
        Some(mem.value())
    } else {
        None
    }
}

#[verifier(opaque)]
spec fn spec_page_info(mem: MemContents<PageStorageType>) -> Option<PageInfo> {
    let mem = spec_page_storage_type(mem);
    if mem.is_some() {
        PageInfo::spec_decode(mem.unwrap())
    } else {
        None
    }
}

spec fn spec_free_info(perm: MemContents<PageStorageType>) -> Option<FreeInfo> {
    let p_info = spec_page_info(perm);
    if p_info.is_some() {
        let pi = p_info.unwrap();
        pi.spec_get_free()
    } else {
        None
    }
}

impl PageType {
    spec fn spec_is_deallocatable(&self) -> bool {
        match *self {
            PageType::Free => false,
            PageType::Allocated => true,
            PageType::SlabPage => true,
            PageType::Compound => true,
            PageType::File => true,
            PageType::Reserved => false,
        }
    }
}

impl PageInfo {
    pub closed spec fn spec_order(&self) -> usize {
        match *self {
            PageInfo::Compound(CompoundInfo { order }) => order,
            PageInfo::Allocated(AllocatedInfo { order }) => order,
            PageInfo::Free(FreeInfo { order, .. }) => order,
            _ => 0,
        }
    }

    pub closed spec fn spec_type(&self) -> PageType {
        match *self {
            PageInfo::Free(_) => PageType::Free,
            PageInfo::Allocated(_) => PageType::Allocated,
            PageInfo::Slab(_) => PageType::SlabPage,
            PageInfo::Compound(_) => PageType::Compound,
            PageInfo::File(_) => PageType::File,
            PageInfo::Reserved(_) => PageType::Reserved,
        }
    }

    pub closed spec fn spec_get_free(&self) -> Option<FreeInfo> {
        match *self {
            PageInfo::Free(info) => { Some(info) },
            _ => { None },
        }
    }
}

trait SpecDecoderProof<T>: core::marker::Sized {
    spec fn spec_decode(mem: T) -> Option<Self> {
        if exists|x: Self| #[trigger] x.spec_encode() === Some(mem) {
            Some(choose|x: Self| #[trigger] x.spec_encode() === Some(mem))
        } else {
            None
        }
    }

    spec fn spec_encode(&self) -> Option<T>;

    proof fn proof_encode_decode(&self)
        requires
            self.spec_encode().is_some(),
        ensures
            Self::spec_decode(self.spec_encode().unwrap()) === Some(*self),
    ;
}

impl PageType {
    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType(*self as u64))
    }

    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        let val = mem.0 & 0xf;
        match val {
            v if v == Self::Free as u64 => Some(Self::Free),
            v if v == Self::Allocated as u64 => Some(Self::Allocated),
            v if v == Self::SlabPage as u64 => Some(Self::SlabPage),
            v if v == Self::Compound as u64 => Some(Self::Compound),
            v if v == Self::File as u64 => Some(Self::File),
            v if v == Self::Reserved as u64 => Some(Self::Reserved),
            _ => None,
        }
    }

    #[verifier::spinoff_prover]
    proof fn proof_encode_decode(&self) {
    }
}

#[allow(private_interfaces)]
pub type FreeInfoSpec = FreeInfo;

impl AllocatedInfo {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.order < MAX_ORDER
    }
}

impl CompoundInfo {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.order < MAX_ORDER
    }
}

impl FileInfo {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.ref_count <= (u64::MAX >> PageStorageType::TYPE_SHIFT)
    }
}

impl SlabPageInfo {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.item_size <= (u64::MAX >> PageStorageType::TYPE_SHIFT)
    }
}

impl FreeInfoSpec {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        &&& self.next_page < MAX_PAGE_COUNT
        &&& self.order < MAX_ORDER
    }
}

impl PageInfo {
    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        match *self {
            PageInfo::Free(ref info) => info.inv(),
            PageInfo::Allocated(ref info) => info.inv(),
            PageInfo::Slab(ref info) => info.inv(),
            PageInfo::Compound(ref info) => info.inv(),
            PageInfo::File(ref info) => info.inv(),
            PageInfo::Reserved(ref _info) => true,
        }
    }
}

proof fn lemma_free_encode_decode(info: FreeInfoSpec)
    requires
        info.inv(),
    ensures
        FreeInfoSpec::spec_decode_impl(info.spec_encode_impl()) == info,
{
    let order = info.order as u64;
    let next_page = info.next_page as u64;
    let mem = PageType::Free as u64;
    let masked_order = order & PageStorageType::ORDER_MASK;
    assert(masked_order == order) by (bit_vector)
        requires
            order < 6,
            masked_order == order & 0xff,
    ;

    let ret = mem | (masked_order << PageStorageType::TYPE_SHIFT) | (next_page
        << PageStorageType::NEXT_SHIFT);
    assert((ret >> 4) & 0xff == masked_order) by (bit_vector)
        requires
            ret == (mem | (masked_order << 4) | (next_page << 12)),
            mem < 15,
            masked_order < 6,
    ;
    assert((ret >> 12) == next_page as u64) by (bit_vector)
        requires
            ret == mem | (masked_order << 4) | (next_page << 12),
            mem < 15,
            masked_order < 6,
            next_page - 1 < 0xffff_ffff_ffff_ffffu64 >> 12,
    ;
}

impl SpecDecoderProof<PageStorageType> for FreeInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        Some(Self::spec_decode_impl(mem))
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        if self.inv() {
            Some(self.spec_encode_impl())
        } else {
            None
        }
    }

    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::Free),
    {
        let info = *self;
        let order = info.order as u64;
        let next_page = info.next_page as u64;
        let tymem = PageType::Free as u64;
        let mem = PageType::Free as u64;
        let masked_order = order & PageStorageType::ORDER_MASK;
        assert(masked_order == order) by (bit_vector)
            requires
                order < 6,
                masked_order == order & 0xff,
        ;
        let encode_order = masked_order << PageStorageType::TYPE_SHIFT;
        let encode_next = next_page << PageStorageType::NEXT_SHIFT;

        let ret = mem | (masked_order << PageStorageType::TYPE_SHIFT) | (next_page
            << PageStorageType::NEXT_SHIFT);
        assert((ret >> 4) & 0xff == masked_order) by (bit_vector)
            requires
                ret == (mem | (masked_order << 4) | (next_page << 12)),
                mem < 15,
                masked_order < 6,
        ;
        assert((ret >> 12) == next_page as u64) by (bit_vector)
            requires
                ret == mem | (masked_order << 4) | (next_page << 12),
                mem < 15,
                masked_order < 6,
                next_page - 1 < 0xffff_ffff_ffff_ffffu64 >> 12,
        ;
        broadcast use lemma_bit_u64_or_zero, lemma_bit_u64_and_zero;

        lemma_u64_and_bitmask_lower(tymem, PageStorageType::TYPE_SHIFT);
        lemma_u64_and_bitmask_higher(
            masked_order,
            PageStorageType::TYPE_SHIFT,
            PageStorageType::TYPE_SHIFT,
        );
        lemma_u64_and_bitmask_higher(
            next_page,
            PageStorageType::TYPE_SHIFT,
            PageStorageType::NEXT_SHIFT,
        );
        lemma_u64_and_is_distributive_or(tymem, encode_order, PageStorageType::TYPE_MASK);
        lemma_u64_and_is_distributive_or(
            tymem | encode_order,
            encode_next,
            PageStorageType::TYPE_MASK,
        );
    }
}

impl SpecDecoderProof<PageStorageType> for AllocatedInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        Some(Self::spec_decode_impl(mem))
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(self.spec_encode_impl())
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
        Some(Self::spec_decode_impl(mem))
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(self.spec_encode_impl())
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
        Some(Self::spec_decode_impl(mem))
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(self.spec_encode_impl())
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
        Some(Self::spec_decode_impl(mem))
    }

    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(self.spec_encode_impl())
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
        Some(self.spec_encode_impl())
    }

    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        Some(Self::spec_decode_impl(mem))
    }

    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode().unwrap()) === Some(PageType::Reserved),
    {
        PageType::Reserved.proof_encode_decode();
        lemma_u64_and_bitmask_lower(PageType::Reserved as u64, PageStorageType::TYPE_SHIFT);
    }
}

impl SpecDecoderProof<PageStorageType> for PageType {
    spec fn spec_encode(&self) -> Option<PageStorageType> {
        Some(PageStorageType(*self as u64))
    }

    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
        let val = mem.0 & 0xf;
        match val {
            v if v == Self::Free as u64 => Some(Self::Free),
            v if v == Self::Allocated as u64 => Some(Self::Allocated),
            v if v == Self::SlabPage as u64 => Some(Self::SlabPage),
            v if v == Self::Compound as u64 => Some(Self::Compound),
            v if v == Self::File as u64 => Some(Self::File),
            v if v == Self::Reserved as u64 => Some(Self::Reserved),
            _ => None,
        }
    }

    proof fn proof_encode_decode(&self) {
        let mem = self.spec_encode().unwrap();
        let val = mem.0;
        assert(val & 0xf == val) by (bit_vector)
            requires
                val < 16,
        ;
        assert(PageType::spec_decode(mem) == Some(*self));
    }
}

proof fn lemma_or_and(a: u64, n: u64, b: u64)
    requires
        a < (1u64 << n),
        n < 64,
        b <= (u64::MAX >> n),
    ensures
        (a | (b << n)) >> n == b,
        (a | (b << n)) & sub((1u64 << n), 1) == a,
{
    lemma_u64_shl_shr(b, n, n);
    let upper_b = (b << n);
    assert((b << n) >> n == b);
    let ab_or = a | (b << n);
    lemma_u64_or_shr(a, b << n, n);
    let a2 = (a >> n);
    assert(a2 == 0) by (bit_vector)
        requires
            a < (1u64 << n),
            a2 == (a >> n),
            n < 64,
    ;
    assert(a2 | b == b) by (bit_vector)
        requires
            a2 == 0,
    ;
    lemma_u64_or_low_high_bitmask_lower(a, b, n, n);
}

impl SpecDecoderProof<PageStorageType> for PageInfo {
    closed spec fn spec_encode(&self) -> Option<PageStorageType> {
        if self.inv() {
            match self {
                Self::Free(fi) => fi.spec_encode(),
                Self::Allocated(ai) => ai.spec_encode(),
                Self::Slab(si) => si.spec_encode(),
                Self::Compound(ci) => ci.spec_encode(),
                Self::File(fi) => fi.spec_encode(),
                Self::Reserved(ri) => ri.spec_encode(),
            }
        } else {
            None
        }
    }

    spec fn spec_decode(v: PageStorageType) -> Option<PageInfo> {
        let mem_type = PageType::spec_decode(v);
        if mem_type.is_none() {
            None
        } else {
            match mem_type.unwrap() {
                PageType::Free => Some(PageInfo::Free(FreeInfo::spec_decode_impl(v))),
                PageType::Allocated => Some(
                    PageInfo::Allocated(AllocatedInfo::spec_decode_impl(v)),
                ),
                PageType::SlabPage => Some(PageInfo::Slab(SlabPageInfo::spec_decode_impl(v))),
                PageType::Compound => Some(PageInfo::Compound(CompoundInfo::spec_decode_impl(v))),
                PageType::File => Some(PageInfo::File(FileInfo::spec_decode_impl(v))),
                PageType::Reserved => Some(PageInfo::Reserved(ReservedInfo::spec_decode_impl(v))),
            }
        }
    }

    proof fn proof_encode_decode(&self) {
        let info = *self;
        let ty_mem = info.spec_type() as u64;
        let mem = info.spec_encode().unwrap();
        info.spec_type().proof_encode_decode();
        let memval = mem.0;
        match info {
            PageInfo::Free(finfo) => {
                finfo.proof_encode_decode();
            },
            PageInfo::Reserved(rinfo) => {
                rinfo.proof_encode_decode();
            },
            PageInfo::Allocated(ainfo) => {
                ainfo.proof_encode_decode();
            },
            PageInfo::Slab(sinfo) => {
                sinfo.proof_encode_decode();
            },
            PageInfo::Compound(cinfo) => {
                cinfo.proof_encode_decode();
            },
            PageInfo::File(finfo) => {
                finfo.proof_encode_decode();
            },
        }
    }
}

impl View for PageStorageType {
    type V = u64;

    closed spec fn view(&self) -> u64 {
        self.0
    }
}

} // verus!
