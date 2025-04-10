verus! {

tracked struct MemoryRegionPerms {
    free: MRFreePerms,
    info: Option<PageInfoDb>,
    info_ptr_exposed: IsExposed,
}

// Increment a thin pointer.
// It does not make sense to increment a fat pointer.
#[verifier(opaque)]
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

    /** Invariants for page info **/
    spec fn wf_info(&self) -> bool {
        let info = self.info.unwrap();
        &&& self.info.is_some()
        &&& self.npages() == info.npages()
        &&& info.base_ptr() == self.base_info_ptr()
        &&& info.start_idx() == 0
        &&& info@.dom() =~= Set::new(|idx| 0 <= idx < self.npages())
        &&& forall|order|
            0 <= order < MAX_ORDER ==> #[trigger]info.nr_page(order) >= self.free.nr_free()[order as int]
        &&& forall|pfn: usize|
            0 <= pfn < self.npages() && info@[pfn].is_free()
                ==> self.free.next_lists()[info@[pfn].order() as int].contains(pfn)
                && #[trigger] info.restrict(pfn).writable()
        &&& forall|pfn: usize|
            self.reserved_count() <= pfn < info.npages() && #[trigger] info@[pfn].page_info()
                == Some(PageInfo::Reserved(ReservedInfo)) && #[trigger] info.restrict(
                pfn,
            ).writable()
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        let info = self.info.unwrap();
        self.info.is_some() ==> self.wf_info()
    }
}

} // verus!
