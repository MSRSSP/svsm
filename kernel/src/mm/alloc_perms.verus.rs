verus! {

tracked struct MemoryRegionPerms {
    free: MRFreePerms,
    info: Option<PageInfoDb>,
    info_ptr_exposed: IsExposed,
}

// Increment a thin pointer.
// It does not make sense to increment a fat pointer.
pub closed spec fn spec_ptr_add<T>(base_ptr: *const T, idx: usize) -> *const T
    recommends
        base_ptr@.metadata == vstd::raw_ptr::Metadata::Thin,
{
    let vstd::raw_ptr::PtrData { addr, provenance, metadata } = base_ptr@;
    vstd::raw_ptr::ptr_from_data(
        vstd::raw_ptr::PtrData {
            addr: (addr + idx * size_of::<T>()) as usize,
            provenance,
            metadata,
        },
    )
}

impl MemoryRegionPerms {
    /** Attributes from free && info_ptr_exposed **/
    spec fn npages(&self) -> usize {
        self.free.pg_params().page_count
    }

    spec fn map(&self) -> LinearMap {
        self.free.map()
    }

    spec fn reserved_count(&self) -> nat {
        self.free.pg_params().reserved_pfn_count()
    }

    spec fn base_info_ptr(&self) -> *const PageStorageType {
        vstd::raw_ptr::ptr_from_data(
            vstd::raw_ptr::PtrData {
                addr: self.free.map().start_virt@,
                provenance: self.info_ptr_exposed@,
                metadata: vstd::raw_ptr::Metadata::Thin,
            },
        )
    }

    spec fn page_info_ptr(&self, pfn: usize) -> *const PageStorageType {
        spec_ptr_add(self.base_info_ptr(), pfn)
    }

    #[verifier::inline]
    spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        &&& self.free.pg_params().valid_pfn_order(pfn, order)
        &&& pfn < MAX_PAGE_COUNT
    }

    spec fn wf_next(&self, order: usize, i: int) -> bool {
        let list = self.free.next_lists()[order as int];
        let pfn = list[i];
        self.info.unwrap()@[pfn].page_info() == Some(
            PageInfo::Free(
                FreeInfo {
                    order: order,
                    next_page: if i > 0 {
                        list[i - 1]
                    } else {
                        0
                    },
                },
            ),
        )
    }

    spec fn info_requires(&self, info: PageInfoDb) -> bool {
        &&& self.npages() == info.npages()
        &&& info.base_ptr() == self.base_info_ptr()
        &&& info.start_idx() == 0
        &&& info@.dom() =~= Set::new(|idx| 0 <= idx < self.npages())
        &&& forall|pfn: usize|
            #![trigger info@[pfn]]
            0 <= pfn < self.npages() && info@[pfn].is_free()
                ==> self.free.next_lists()[info@[pfn].order() as int].contains(pfn)
                && info.restrict(
                pfn,
            ).writable()/*&&& forall|pfn: usize| #![trigger info@[pfn]]
            self.reserved_count() <= pfn < info.npages() && info@[pfn].page_info()
                == Some(PageInfo::Reserved(ReservedInfo)) && info.restrict(
                pfn,
            ).writable()*/
        &&& forall|order: usize, i: int|
            #![trigger self.free.next_lists()[order as int][i]]
            0 <= order < MAX_ORDER && 0 <= i < self.free.next_lists()[order as int].len() as int
                ==> self.wf_next(order, i)
    }

    /** Invariants for page info **/
    spec fn wf_info(&self) -> bool {
        let info = self.info.unwrap();
        &&& self.info.is_some()
        &&& self.npages() == info.npages()
        &&& info.base_ptr() == self.base_info_ptr()
        &&& info.start_idx() == 0
        &&& info@.dom() =~= Set::new(|idx| 0 <= idx < self.npages())
        &&& forall|order|
            0 <= order < MAX_ORDER ==> #[trigger] info.nr_page(order)
                >= self.free.nr_free()[order as int]
        &&& forall|pfn: usize|
            0 <= pfn < self.npages() && info@[pfn].is_free()
                ==> self.free.next_lists()[info@[pfn].order() as int].contains(pfn)
                && #[trigger] info.restrict(pfn).writable()
        &&& forall|pfn: usize|
            self.reserved_count() <= pfn < info.npages() ==> #[trigger] info@[pfn].page_info()
                == Some(PageInfo::Reserved(ReservedInfo)) && #[trigger] info.restrict(
                pfn,
            ).writable()
        &&& forall|order: usize, i: int|
            #![trigger self.free.next_lists()[order as int][i]]
            0 <= order < MAX_ORDER && 0 <= i < self.free.next_lists()[order as int].len() as int
                ==> self.wf_next(order, i)
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        let info = self.info.unwrap();
        self.info.is_some() ==> self.wf_info()
    }

    proof fn tracked_update_info(tracked &mut self, tracked info: PageInfoDb)
        requires
            old(self).info_requires(info),
        ensures
            self.info == Some(info),
    {
        self.info = Some(info);
    }
}

impl MemoryRegion {
    pub closed spec fn wf2(&self) -> bool {
        let info = self.view2().info.unwrap();
        &&& self.view2().info.is_some()
        &&& forall|order|
            0 <= order < MAX_ORDER ==> info.nr_page(order) == #[trigger] self.nr_pages[order as int]
        &&& self.view2().free.nr_free() =~= self.free_pages@
    }
}

} // verus!
