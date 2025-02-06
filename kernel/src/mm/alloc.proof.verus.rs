verus! {

broadcast proof fn lemma_wf_next_page_info(mr: MemoryRegion, order: int)
    requires
        mr.wf_after_init(),
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

} // verus!
