verus! {

use vstd::arithmetic::div_mod::{lemma_mod_self_0, lemma_small_mod, lemma_add_mod_noop};

#[verifier::spinoff_prover]
broadcast proof fn lemma_wf_next_page_info(mr: MemoryRegion, order: int)
    requires
        mr.wf_mem_state(),
        0 <= order < MAX_ORDER,
    ensures
        #![trigger mr.next_page[order]]
        mr.next_page[order] > 0 ==> mr@.wf_next(order),
        mr.next_page[order] == 0 || mr.next_page[order] < mr.page_count,
        (mr@.next_page(order) == 0) == (mr.free_pages[order] == 0),
        (mr@.next_next_page(order) == 0) ==> (mr.free_pages[order] <= 1),
        mr.free_pages[order] == mr@.next[order].len(),
{
    let perms = mr@;
    let i = perms.next[order].len() - 1;
    if i < 0 {
        assert(mr@.next_page(order) == 0);
    } else {
        assert(perms.wf_item(order, i));
        assert(perms.next_page(order) > 0);
    }
    assert(mr.free_pages[order] == perms.free_page_counts()[order]);
    assert(perms.free_page_counts()[order] == perms.next[order].len());
    if i > 0 {
        assert(perms.wf_item(order, i - 1));
        assert(mr@.next_next_page(order) > 0);
    } else {
        assert(perms.next[order].len() <= 1);
        assert(mr@.next_next_page(order) == 0);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_ens_has_free_pages_pages(mr: MemoryRegion, order: int)
    requires
        mr.spec_alloc_fails(order),
        0 <= order < MAX_ORDER - 1,
    ensures
        !mr.spec_alloc_fails(order + 1) ==> !mr.spec_alloc_fails(order),
        (mr.spec_alloc_fails(order + 1) && mr.next_page[order] == 0) ==> mr.spec_alloc_fails(order),
{
}

#[verifier::spinoff_prover]
broadcast proof fn lemma_wf_perms<VAddr: SpecVAddrImpl, const N: usize>(
    perms: MemoryRegionTracked<VAddr, N>,
)
    requires
        perms.wf(),
    ensures
        #[trigger] perms.wf_perms(),
{
    reveal(MemoryRegionTracked::wf_perms);
    assert forall|order, i|
        0 <= order < N && 0 <= i < perms.next[order].len() implies #[trigger] perms.wf_item_perm(
        order,
        i,
    ) by { assert(perms.wf_item(order, i)) }
}

#[verifier::spinoff_prover]
proof fn lemma_unique_pfn_same_order<VAddr: SpecVAddrImpl, const N: usize>(
    perms: MemoryRegionTracked<VAddr, N>,
    order: int,
    n: int,
)
    requires
        perms.wf(),
        0 <= order < N,
        0 < n <= perms.next[order].len(),
    ensures
        forall|i1, i2| 0 <= i1 < i2 < n ==> perms.next[order][i1] != perms.next[order][i2],
    decreases n,
{
    if n == 2 {
        let i1 = n - 2;
        let i2 = n - 1;
        let pfn1 = perms.next[order][i1];
        let pfn2 = perms.next[order][i2];
        let pi1 = perms.get_free_info(pfn1 as int);
        let pi2 = perms.get_free_info(pfn2 as int);
        assert(perms.wf_item(order, i1));
        assert(perms.wf_item(order, i2));
        assert(pi2.unwrap().next_page == pfn1);
    } else if n > 2 {
        lemma_unique_pfn_same_order(perms, order, n - 1);
        assert forall|i1, i2| 0 <= i1 < i2 < n implies perms.next[order][i1]
            != perms.next[order][i2] by {
            let pfn1 = perms.next[order][i1];
            let pfn2 = perms.next[order][i2];
            let pfn1_next = perms.next[order][i1 - 1];
            let pfn2_next = perms.next[order][i2 - 1];
            let pi1 = perms.get_free_info(pfn1 as int);
            let pi2 = perms.get_free_info(pfn2 as int);
            assert(perms.wf_item(order, i1));
            assert(perms.wf_item(order, i2));
            assert(perms.wf_item(order, i2 - 1));
            if i2 == n - 1 {
                assert(pi2.unwrap().next_page == pfn2_next);
                if i1 > 0 {
                    assert(pi1.unwrap().next_page == pfn1_next);
                } else {
                    assert(pi1.unwrap().next_page == 0);
                }
                if pfn1 == pfn2 {
                    assert(pfn1_next == pfn2_next);
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_unique_pfn_start<VAddr: SpecVAddrImpl, const N: usize>(
    perms: MemoryRegionTracked<VAddr, N>,
    o1: int,
    i1: int,
    o2: int,
    i2: int,
)
    requires
        perms.wf(),
        !((o1, i1) === (o2, i2)),
        0 <= o1 < N,
        0 <= o2 < N,
        0 <= i1 < perms.next[o1].len(),
        0 <= i2 < perms.next[o2].len(),
    ensures
        perms.next[o1][i1] != perms.next[o2][i2],
{
    let pfn1 = perms.next[o1][i1];
    let pfn2 = perms.next[o2][i2];
    assert(perms.wf_item(o1, i1));
    assert(perms.wf_item(o2, i2));
    let pi1 = perms.get_free_info(pfn1 as int);
    let pi2 = perms.get_free_info(pfn2 as int);
    if o1 != o2 {
        assert(pi1.unwrap().order == o1);
        assert(pi2.unwrap().order == o2);
        assert(pfn1 != pfn2);
    } else {
        lemma_unique_pfn_same_order(perms, o1, perms.next[o1].len() as int);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_unique_pfn<VAddr: SpecVAddrImpl, const N: usize>(
    perms: MemoryRegionTracked<VAddr, N>,
    o1: int,
    i1: int,
    o2: int,
    i2: int,
)
    requires
        perms.wf(),
        !((o1, i1) === (o2, i2)),
        0 <= o1 < N,
        0 <= o2 < N,
        0 <= i1 < perms.next[o1].len(),
        0 <= i2 < perms.next[o2].len(),
    ensures
        (perms.next[o1][i1] + (1usize << o1 as usize) <= perms.next[o2][i2]) || (perms.next[o2][i2]
            + (1usize << o2 as usize) <= perms.next[o1][i1]),
{
    lemma_unique_pfn_start(perms, o1, i1, o2, i2);
    let n1 = (1usize << o1 as usize);
    let n2 = (1usize << o2 as usize);
    let pfn1 = perms.next[o1][i1];
    let pfn2 = perms.next[o2][i2];
    assert(perms.wf_item(o1, i1));
    assert(perms.wf_item(o2, i2));
    let next_pfn1 = if i1 > 0 {
        perms.next[o1][i1 - 1]
    } else {
        0usize
    };
    let next_pfn2 = if i2 > 0 {
        perms.next[o2][i2 - 1]
    } else {
        0usize
    };
    assert(perms.marked_free(pfn1 as int, o1 as usize, next_pfn1));
    assert(perms.marked_free(pfn2 as int, o2 as usize, next_pfn2));
    let c1 = Some(PageInfo::Compound(CompoundInfo { order: o1 as usize }));
    let c2 = Some(PageInfo::Compound(CompoundInfo { order: o2 as usize }));
    assert(perms.spec_page_info(pfn1 as int) !== c2);
    assert(perms.spec_page_info(pfn2 as int) !== c1);
}

#[verifier::spinoff_prover]
proof fn lemma_valid_pfn_order_split(mr: &MemoryRegion, pfn: usize, order: usize)
    requires
        #[trigger] mr.valid_pfn_order(pfn, order),
        0 < order < MAX_ORDER,
    ensures
        mr.valid_pfn_order(pfn, (order - 1) as usize),
        (pfn + (1usize << (order - 1) as usize)) % (1usize << (order - 1) as usize) as int == 0,
{
    broadcast use lemma_bit_usize_shl_values;

    let n = 1usize << order;
    let lower_n = 1usize << (order - 1) as usize;
    assert(1usize << order == 2 * (1usize << (order - 1) as usize)) by (bit_vector)
        requires
            0 < order < 64,
    ;
    if mr.valid_pfn_order(pfn, order) && order > 0 {
        verify_proof::nonlinear::lemma_modulus_product_divisibility(pfn as int, lower_n as int, 2);
    }
    lemma_add_mod_noop(pfn as int, lower_n as int, lower_n as int);
    lemma_mod_self_0(lower_n as int);
    lemma_small_mod(0, lower_n as nat);
    assert((pfn + lower_n) % lower_n as int == 0);
}

#[verifier::spinoff_prover]
proof fn lemma_valid_pfn_order_merge(mr: MemoryRegion, pfn: usize, order: usize)
    requires
        #[trigger] mr.valid_pfn_order(pfn, order),
    ensures
        ((pfn % (1usize << (order + 1) as usize) == 0) && (pfn + (1usize << (order + 1) as usize)
            <= mr.page_count)) ==> (pfn + (1usize << order)) % (1usize << order) as int == 0,
        (pfn % (1usize << (order + 1) as usize) != 0) && (order + 1) < MAX_ORDER ==> (pfn - (1usize
            << order)) % (1usize << (order + 1) as usize) as int == 0,
{
    broadcast use lemma_bit_usize_shl_values;

    let n = 1usize << order;
    let m = 1usize << (order + 1) as usize;
    assert(2 * (1usize << order) == 1usize << (order + 1) as usize) by (bit_vector)
        requires
            order < 63,
    ;
    assert(m == n + n);

    verify_proof::nonlinear::lemma_modulus_add_sub_m(pfn as int, n as int);
    assert((pfn + n) % n as int == 0);
    if pfn % m != 0 {
        assert((pfn - n) % m as int == 0);
        assert(pfn - n >= 0);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_compound_neighbor(pfn: usize, order: usize, ret_pfn: usize)
    requires
        pfn % (1usize << order) == 0,
        pfn + (1usize << order) <= usize::MAX,
        ret_pfn == pfn ^ (1usize << order),
        0 <= order < 63,
    ensures
        (ret_pfn == pfn - (1usize << order)) ==> ret_pfn % (1usize << (order + 1)) == 0,
        MemoryRegion::ens_find_neighbor(pfn, order, ret_pfn),
{
    broadcast use lemma_bit_usize_shl_values;

    assert(pfn % (1usize << order) == 0);
    let n = 1usize << (order + 1);
    assert(1usize << (order + 1) == 2 * (1usize << order));
    lemma_bit_usize_and_mask_is_mod(pfn, ((1usize << order) - 1) as usize);
    lemma_bit_usize_and_mask_is_mod(pfn, ((1usize << (order + 1) as usize) - 1) as usize);
    lemma_bit_usize_xor_neighbor(pfn, order);
    lemma_modulus_add_sub_m(pfn as int, (1usize << order) as int);
    if ret_pfn == pfn - (1usize << order) {
        let x = pfn;
        let m = 1usize << order;
        if x as int % (2 * m) == 0 {
            assert(x & (2 * m - 1) as usize == 0);
            assert(x & (n - 1) as usize == 0);
            assert(x ^ m == sub(x, m));
        }
        assert(x as int % (2 * m) != 0);
        assert(((x - m) % (2 * m) == 0 && (x >= m || x <= -m)))
    }
}

} // verus!
verus! {

trait SpecDecoderProof<PageStorageType>: core::marker::Sized {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    proof fn proof_encode_decode(&self)
        ensures
            Self::spec_decode(self.spec_encode()).is_some(),
            Self::spec_decode(self.spec_encode()).unwrap() === *self,
    ;
}

impl SpecDecoderProof<PageStorageType> for PageType {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType {
        let val = match self {
            PageType::Free => 0,
            PageType::Allocated => 1,
            PageType::SlabPage => 2,
            PageType::Compound => 3,
            PageType::File => 4,
            PageType::Reserved => (1u64 << 4) - 1,
        };
        PageStorageType(val as u64)
    }

    #[verifier::external_body]
    proof fn proof_encode_decode(&self) {
    }
}

impl SpecDecoderProof<PageStorageType> for FreeInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::Free),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for AllocatedInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::Allocated),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for SlabPageInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::SlabPage),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for CompoundInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::Compound),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for FileInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::File),
    {
    }
}

impl SpecDecoderProof<PageStorageType> for ReservedInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::Reserved),
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

    closed spec fn spec_encode(&self) -> PageStorageType {
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
