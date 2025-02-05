verus! {

broadcast proof fn lemma_wf_next_page_info(mr: MemoryRegion, order: int)
    requires
        mr.wf_after_init(),
        0 <= order < MAX_ORDER,
    ensures
        #![trigger mr.next_page[order]]
        mr.next_page[order] > 0 ==> mr@.wf_next(order),
        mr.next_page[order] == 0 || mr.next_page[order] < mr.page_count,
{
    let perms = mr@;
    let i = perms.next[order].len() - 1;
    if mr.next_page[order] > 0 {
        assert(perms.next_page(order) > 0);
        assert(perms.wf_item(order, i));
    }
}

} // verus!
