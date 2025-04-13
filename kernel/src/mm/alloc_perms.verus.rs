verus! {

// A ghost global layout for global allocator
// Add more global variables here as needed
// It could be a real global variable or a global invariant.
// We put FracPerm to ensure that the content will not be modified by accident.
// For example, allocator must update this ghost variable if it needs to
// change the base_ptr of the allocator.
//
// Since the allocated memory will have GlobalInv and so the allocator cannot
// obtain full ownership if the allocator does not free all memory before updating
// the base_ptr.
#[allow(missing_debug_implementations)]
pub struct MemRegionMappingView {
    pub map: LinearMap,
    pub provenance: Provenance,
}

pub uninterp spec fn alloc_inv_ptr() -> *const Tracked<MemRegionMappingView>;

#[allow(missing_debug_implementations)]
pub struct MemRegionMapping(FracTypedPerm<Tracked<MemRegionMappingView>>);

impl MemRegionMapping {
    #[verifier::type_invariant]
    pub closed spec fn wf(&self) -> bool {
        &&& self.0.ptr() == alloc_inv_ptr()
        &&& self.0.valid()
        &&& self@.map.wf()
    }

    pub closed spec fn view(&self) -> MemRegionMappingView {
        self.0.value()@
    }

    pub closed spec fn shares(&self) -> nat {
        self.0.shares()
    }

    pub closed spec fn pg_params(&self) -> PageCountParam<MAX_ORDER> {
        PageCountParam { page_count: (self@.map.size / PAGE_SIZE as nat) as usize }
    }

    spec fn base_ptr(&self) -> *const PageStorageType {
        vstd::raw_ptr::ptr_from_data(
            vstd::raw_ptr::PtrData {
                addr: self@.map.start_virt@,
                provenance: self@.provenance,
                metadata: vstd::raw_ptr::Metadata::Thin,
            },
        )
    }

    pub proof fn is_same(tracked &self, tracked other: &MemRegionMapping)
        ensures
            self@ == other@,
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.0.is_same(&other.0);
    }

    #[verifier::spinoff_prover]
    pub proof fn tracked_merge_pages(
        tracked &self,
        tracked p1: &mut RawPerm,
        tracked p2: RawPerm,
        pfn1: usize,
        pfn2: usize,
        order: usize,
    )
        requires
            0 <= order < 64,
            pfn1 == pfn2 + (1usize << order) || pfn2 == pfn1 + (1usize << order),
            p2.wf_pfn_order(*self, pfn2, order),
            old(p1).wf_pfn_order(*self, pfn1, order),
        ensures
            p1.wf_pfn_order(
                *self,
                if pfn1 < pfn2 {
                    pfn1
                } else {
                    pfn2
                },
                (order + 1) as usize,
            ),
    {
        use_type_invariant(self);
        broadcast use lemma_bit_usize_shl_values;

        let map = self@.map;
        reveal(<VirtAddr as SpecVAddrImpl>::region_to_dom);
        map.lemma_get_virt(pfn1);
        map.lemma_get_virt(pfn2);
        let size = 1usize << order;
        let tracked mut owned_p1 = RawPerm::empty(p1.provenance());
        tracked_swap(&mut owned_p1, p1);
        let tracked p = if pfn1 < pfn2 {
            assert(pfn2 == pfn1 + size);
            owned_p1.join(p2)
        } else {
            assert(pfn1 == pfn2 + size);
            p2.join(owned_p1)
        };
        *p1 = p;
    }
}

impl MemRegionMapping {
    spec fn valid_perm_by_vaddr(&self, perm: RawPerm, vaddr: VirtAddr, order: usize) -> bool {
        let size = ((1usize << order) * PAGE_SIZE) as nat;
        &&& perm.dom() =~= vaddr.region_to_dom(size)
        &&& perm.provenance() === self@.provenance
    }

    closed spec fn valid_perm_by_pfn(&self, perm: RawPerm, pfn: usize, order: usize) -> bool {
        let vaddr = self@.map.try_get_virt(pfn);
        &&& vaddr.is_some()
        &&& self.valid_perm_by_vaddr(perm, vaddr.unwrap(), order)
    }
}

spec fn spec_map_page_info_addr(map: LinearMap, pfn: usize) -> VirtAddr {
    let reserved_unit_size = size_of::<PageStorageType>();
    let start = map.start_virt;
    VirtAddr::from_spec((start@ + (pfn * reserved_unit_size)) as usize)
}

spec fn spec_map_page_info_ptr(map: LinearMap, pfn: usize) -> *const PageStorageType {
    let addr = spec_map_page_info_addr(map, pfn)@;
    vstd::raw_ptr::ptr_from_data(
        vstd::raw_ptr::PtrData {
            addr,
            provenance: allocator_provenance(),
            metadata: vstd::raw_ptr::Metadata::Thin,
        },
    )
}

pub trait MemPermWithVAddrOrder<VAddr: SpecVAddrImpl> {
    spec fn wf_vaddr_order(&self, map: MemRegionMapping, vaddr: VAddr, order: usize) -> bool;
}

pub trait MemPermWithPfnOrder {
    spec fn wf_pfn_order(&self, map: MemRegionMapping, pfn: usize, order: usize) -> bool;
}

impl<VAddr: SpecVAddrImpl> MemPermWithVAddrOrder<VAddr> for RawPerm {
    open spec fn wf_vaddr_order(&self, map: MemRegionMapping, vaddr: VAddr, order: usize) -> bool {
        let size = ((1usize << order) * PAGE_SIZE) as nat;
        &&& self.dom() =~= vaddr.region_to_dom(size)
        &&& self.provenance() === map@.provenance
    }
}

impl MemPermWithPfnOrder for RawPerm {
    open spec fn wf_pfn_order(&self, map: MemRegionMapping, pfn: usize, order: usize) -> bool {
        let vaddr = map@.map.try_get_virt(pfn);
        &&& vaddr.is_some()
        &&& pfn < map@.map.size / PAGE_SIZE as nat
        &&& self.wf_vaddr_order(map, vaddr.unwrap(), order)
    }
}

tracked struct MemoryRegionPerms {
    free: MRFreePerms,  // free mem perms + readonly share of pginfo
    info: PageInfoDb,  // readonly share of pginfo for all pfns.
    info_ptr_exposed: IsExposed,
    mr_map: MemRegionMapping,
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

#[allow(missing_debug_implementations)]
pub struct AllocatedPagesPerm {
    perm: PgUnitPerm<DeallocUnit>,
    map: MemRegionMapping,
}

impl AllocatedPagesPerm {
    spec fn pfn(&self) -> usize {
        self.perm.info.unit_start()
    }

    spec fn vaddr(&self) -> VirtAddr {
        self.map@.map.try_get_virt(self.pfn()).unwrap()
    }

    spec fn size(&self) -> nat {
        (self.perm.info.npages() * PAGE_SIZE as nat)
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        let order = self.perm.info.order();
        let pfn = self.pfn();
        &&& self.map.shares() == self.size()
        &&& self.map.base_ptr() == self.perm.info.base_ptr()
        &&& self.map.valid_perm_by_pfn(self.perm.mem, pfn, order)
        &&& self.map.valid_perm_by_pfn(self.perm.mem, pfn, order)
        &&& self.perm.page_type().spec_is_deallocatable()
    }
}

#[allow(missing_debug_implementations)]
pub struct AllocatorUnit {}

#[allow(missing_debug_implementations)]
pub struct DeallocUnit {}

#[allow(missing_debug_implementations)]
pub struct WritableUnit {}

pub trait UnitType {
    spec fn wf_share_total(shares: nat, total: nat) -> bool;
}

impl UnitType for DeallocUnit {
    closed spec fn wf_share_total(shares: nat, total: nat) -> bool {
        &&& shares == DEALLOC_PGINFO_SHARES
        &&& total == MAX_PGINFO_SHARES
        &&& 0 < shares < total
    }
}

impl UnitType for AllocatorUnit {
    closed spec fn wf_share_total(shares: nat, total: nat) -> bool {
        &&& shares == total - DEALLOC_PGINFO_SHARES
        &&& total == MAX_PGINFO_SHARES
        &&& 0 < shares < total
    }
}

impl UnitType for WritableUnit {
    closed spec fn wf_share_total(shares: nat, total: nat) -> bool {
        0 < shares == total
    }
}

#[allow(missing_debug_implementations)]
pub struct PgUnitPerm<T: UnitType> {
    mem: RawPerm,
    info: PageInfoDb,
    ghost typ: T,
}

#[allow(missing_debug_implementations)]
pub tracked struct UnitDeallocPerm(PgUnitPerm<DeallocUnit>);

impl UnitDeallocPerm {
    pub closed spec fn view(&self) -> PgUnitPerm<DeallocUnit> {
        self.0
    }
}

impl<T: UnitType> PgUnitPerm<T> {
    #[verifier::type_invariant]
    pub closed spec fn wf(&self) -> bool {
        &&& self.info.npages() > 0 ==> self.info.is_unit()
        &&& self.info.npages() > 0 ==> T::wf_share_total(
            self.info.id().shares,
            self.info.id().total,
        )
    }

    spec fn page_type(&self) -> PageType {
        let pageinfo = self.info.unit_head().page_info().unwrap();
        pageinfo.spec_type()
    }

    pub closed spec fn from_mr(&self, map: MemRegionMapping, pfn: usize, order: usize) -> bool {
        self.wf_pfn_order(map, pfn, order)
    }

    pub closed spec fn wf_pfn_order(
        &self,
        map: MemRegionMapping,
        pfn: usize,
        order: usize,
    ) -> bool {
        &&& self.mem.wf_pfn_order(map, pfn, order)
        &&& self.info.unit_start() == pfn
        &&& self.info.order() == order
        &&& self.info.base_ptr() == map.base_ptr()
        &&& self.info.npages() > 0
    }

    pub proof fn empty(id: PageInfoUnique) -> (tracked ret: Self) {
        PgUnitPerm {
            mem: RawPerm::empty(id.ptr_data.provenance),
            info: PageInfoDb::tracked_empty(id),
            typ: arbitrary(),
        }
    }

    proof fn tracked_take(tracked &mut self) -> (tracked ret: (RawPerm, PageInfoDb))
        ensures
            ret == (old(self).mem, old(self).info),
            ret.1.npages() > 0 ==> ret.1.is_unit(),
            T::wf_share_total(ret.1.id().shares, ret.1.id().total),
    {
        use_type_invariant(&*self);
        let tracked mut tmp = PgUnitPerm::empty(self.info.id);
        tracked_swap(self, &mut tmp);
        (tmp.mem, tmp.info)
    }
}

impl MemoryRegionPerms {
    /** Attributes from free && info_ptr_exposed **/
    spec fn npages(&self) -> usize {
        self.mr_map.pg_params().page_count
    }

    spec fn map(&self) -> LinearMap {
        self.mr_map@.map
    }

    spec fn reserved_count(&self) -> nat {
        self.mr_map.pg_params().reserved_pfn_count()
    }

    spec fn base_ptr(&self) -> *const PageStorageType {
        self.mr_map.base_ptr()
    }

    spec fn wf_base_ptr(&self) -> bool {
        &&& self.mr_map == self.free.mr_map()
        &&& self.info_ptr_exposed@ == self.mr_map@.provenance
        &&& self.info.base_ptr() == self.base_ptr()
    }

    spec fn page_info_ptr(&self, pfn: usize) -> *const PageStorageType {
        spec_ptr_add(self.base_ptr(), pfn)
    }

    #[verifier(inline)]
    spec fn get_info(&self, pfn: usize) -> Option<PageInfo> {
        self.info@[pfn].page_info()
    }

    #[verifier(inline)]
    spec fn get_free_info(&self, pfn: usize) -> Option<FreeInfo> {
        self.info@[pfn].page_info().unwrap().spec_get_free()
    }

    spec fn get_page_storage_type(&self, pfn: usize) -> Option<PageStorageType> {
        self.info@[pfn].page_storage()
    }

    spec fn wf_next(&self, order: usize, i: int) -> bool {
        let list = self.free.next_lists()[order as int];
        let pfn = list[i];
        self.info@[pfn].page_info() == Some(
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

    spec fn strict_wf_info_free(&self) -> bool {
        let info = self.info;
        &&& forall|order|   //#![trigger self.free.nr_free()[order as int]]

            0 <= order < MAX_ORDER ==> #[trigger] info.nr_page(order)
                >= self.free.nr_free()[order as int]
        &&& forall|pfn: usize|
            0 <= pfn < self.npages() && (#[trigger] info@[pfn]).is_free()
                ==> self.free.next_lists()[info@[pfn].order() as int].contains(pfn)
    }

    /** Invariants for page info **/
    spec fn wf_info(&self) -> bool {
        let info = self.info;
        &&& info.is_readonly_allocator_shares()
        &&& self.npages() == info.npages()
        &&& info@.dom() =~= Set::new(
            |idx| 0 <= idx < self.npages(),
        )/*&&& forall|order: usize, i: int|
            //#![trigger self.free.next_lists()[order as int][i]]
            0 <= order < MAX_ORDER && 0 <= i < self.free.next_lists()[order as int].len() as int
                ==> self.wf_next(order, i)*/
        /*&&& forall|pfn: usize|
            self.reserved_count() <= pfn < info.npages() ==> #[trigger] info@[pfn].page_info()
                == Some(PageInfo::Reserved(ReservedInfo))*/

    }

    spec fn wf(&self) -> bool {
        &&& self.wf_info()
        &&& self.wf_base_ptr()
    }
}

impl MemoryRegion {
    pub closed spec fn wf(&self) -> bool {
        let info = self.view2().info;
        &&& self.wf_perms()
        &&& self.wf_basic2()
    }

    pub closed spec fn wf_perms(&self) -> bool {
        let info = self@.info;
        &&& self@.wf()
        &&& forall|order|   //#![trigger info.nr_page(order)]

            0 <= order < MAX_ORDER ==> info.nr_page(order) == (
            #[trigger] self.nr_pages[order as int])
        &&& self.view2().free.nr_free() =~= self.free_pages@
        &&& info.dom() =~= Set::new(|idx| 0 <= idx < self.page_count)
        &&& self.page_count == self@.npages()
    }

    pub closed spec fn wf_basic2(&self) -> bool {
        &&& self.page_count <= MAX_PAGE_COUNT
    }
}

} // verus!
