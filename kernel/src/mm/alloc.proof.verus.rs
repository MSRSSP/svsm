verus! {

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

proof fn lemma_ens_has_free_pages_pages(mr: MemoryRegion, order: int)
    requires
        mr.spec_alloc_fails(order),
        0 <= order < MAX_ORDER - 1,
    ensures
        !mr.spec_alloc_fails(order + 1) ==> !mr.spec_alloc_fails(order),
        (mr.spec_alloc_fails(order + 1) && mr.next_page[order] == 0) ==> mr.spec_alloc_fails(order),
{
}

broadcast proof fn lemma_wf_perms<VAddr: SpecVAddrImpl, const N: usize>(
    perms: MemoryRegionTracked<VAddr, N>,
)
    requires
        perms.wf(),
    ensures
        #[trigger] perms.wf_perms(),
{
    assert forall|order, i|
        0 <= order < N && 0 <= i < perms.next[order].len() implies #[trigger] perms.wf_item_perm(
        order,
        i,
    ) by { assert(perms.wf_item(order, i)) }
}

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

} // verus!
