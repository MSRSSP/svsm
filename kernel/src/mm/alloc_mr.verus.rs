verus! {

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
    spec fn wf_vaddr_order(&self, vaddr: VAddr, order: usize) -> bool;
}

pub trait MemPermWithPfnOrder {
    spec fn wf_pfn_order(&self, map: LinearMap, pfn: usize, order: usize) -> bool;
}

impl<VAddr: SpecVAddrImpl> MemPermWithVAddrOrder<VAddr> for RawPerm {
    open spec fn wf_vaddr_order(&self, vaddr: VAddr, order: usize) -> bool {
        let size = ((1usize << order) * PAGE_SIZE) as nat;
        &&& self.dom() =~= vaddr.region_to_dom(size)
        &&& self.provenance() === allocator_provenance()
    }
}

impl MemPermWithPfnOrder for RawPerm {
    open spec fn wf_pfn_order(&self, map: LinearMap, pfn: usize, order: usize) -> bool {
        let vaddr = map.try_get_virt(pfn);
        &&& vaddr.is_some()
        &&& pfn < map.size / PAGE_SIZE as nat
        &&& self.wf_vaddr_order(vaddr.unwrap(), order)
    }
}

ghost struct VirtInfo<VAddr> {
    vaddr: VAddr,
    info_vaddr: VAddr,
}

tracked struct MemoryRegionTracked<const N: usize> {
    tracked avail: Map<(int, int), RawPerm>,  //(order, idx) -> perm
    tracked reserved: Map<int, FracTypedPerm<PageStorageType>>,  //pfn -> pginfo
    ghost next: Seq<Seq<usize>>,  // order -> next page list
    ghost map: LinearMap,  // pfn -> virt address
    tracked is_exposed: IsExposed,
}

ghost struct FreePerms<const N: usize> {
    avail: Map<(int, int), RawPerm>,  //(order, idx) -> perm
    next: Seq<Seq<usize>>,  // order -> next page list
    map: LinearMap,  // pfn -> virt address
    page_count: PageCountParam<N>,
}

impl<const N: usize> FreePerms<N> {
    pub closed spec fn wf_at(&self, order: int, i: int) -> bool {
        let pfn = self.next[order][i];
        let perm = self.avail[(order, i)];
        &&& pfn >= self.page_count.reserved_pfn_count()
        &&& self.page_count.valid_pfn_order(pfn, order as usize)
        &&& perm.wf_pfn_order(self.map, pfn, order as usize)
    }

    spec fn wf(&self) -> bool {
        &&& forall|order, i|
            0 <= order < N && 0 <= i < self.next[order].len() ==> #[trigger] self.wf_at(order, i)
    }
}

struct DeallocPerm {
    ghost vaddr: VirtAddr,
    ghost pfn: usize,
    ghost order: usize,
    ghost typ: PageType,
    tracked reserved: Map<usize, FracTypedPerm<PageStorageType>>,
}

impl DeallocPerm {
    #[verifier(inline)]
    spec fn spec_page_info(&self, pfn: usize) -> Option<PageInfo> {
        spec_page_info(self.reserved[pfn].opt_value())
    }

    spec fn wf(&self) -> bool {
        &&& forall|pfn: usize|
            self.pfn < pfn < (1usize << self.order) + self.pfn ==> {
                &&& self.reserved.contains_key(pfn)
                &&& (#[trigger] self.spec_page_info(pfn)) == Some(
                    PageInfo::Compound(CompoundInfo { order: self.order }),
                )
            }
        &&& self.reserved.contains_key(self.pfn)
        &&& (#[trigger] self.spec_page_info(self.pfn)).is_some()
        &&& self.spec_page_info(self.pfn).unwrap().spec_order() == self.order
        &&& self.spec_page_info(self.pfn).unwrap().spec_type().spec_is_deallocatable()
    }
}

struct PermWithDealloc {
    perm: RawPerm,
    dealloc: DeallocPerm,
}

#[allow(missing_debug_implementations)]
struct ReservedPerms<const N: usize> {
    reserved: Map<int, FracTypedPerm<PageStorageType>>,
    page_count: PageCountParam<N>,
}

#[allow(missing_debug_implementations)]
pub struct PageCountParam<const N: usize> {
    pub page_count: usize,
}

impl<const N: usize> PageCountParam<N> {
    #[verifier(opaque)]
    pub open spec fn reserved_pfn_count(&self) -> nat {
        (spec_align_up(self.page_count * 8 as int, PAGE_SIZE as int) / PAGE_SIZE as int) as nat
    }

    pub open spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        let n = 1usize << order;
        &&& self.reserved_pfn_count() <= pfn < self.page_count
        &&& pfn + n <= self.page_count
        &&& n > 0
        &&& pfn % n == 0
        &&& order < N
    }

    proof fn lemma_reserved_pfn_count(&self)
        ensures
            self.reserved_pfn_count() == self.page_count / 512 || self.reserved_pfn_count() == 1 + (
            self.page_count / 512),
            self.page_count > 0 ==> self.reserved_pfn_count() > 0,
    {
        broadcast use lemma_page_size;

        reveal(PageCountParam::reserved_pfn_count);

        let x = self.page_count * 8 as int;
        assert(PAGE_SIZE == 0x1000);
        let count = spec_align_up(x, PAGE_SIZE as int);
        verify_proof::nonlinear::lemma_align_up_properties(x, PAGE_SIZE as int, count);
        assert(self.page_count * 8 / 0x1000 == self.page_count / 512);
    }
}

pub spec const MAX_PGINFO_SHARES: nat = 2;

pub spec const ALLOCATOR_PGINFO_SHARES: nat = 1;

pub spec const DEALLOC_PGINFO_SHARES: nat = 1;

impl<const N: usize> ReservedPerms<N> {
    #[verifier(inline)]
    spec fn pg_params(&self) -> PageCountParam<N> {
        self.page_count
    }

    spec fn page_count(&self) -> usize {
        self.pg_params().page_count
    }

    spec fn reserved_count(&self) -> nat {
        self.pg_params().reserved_pfn_count()
    }

    #[verifier(inline)]
    spec fn spec_page_info(&self, pfn: usize) -> Option<PageInfo> {
        spec_page_info(self.reserved[pfn as int].opt_value())
    }

    spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        self.pg_params().valid_pfn_order(pfn, order)
    }

    #[verifier(inline)]
    spec fn pfn_filter(&self, order: usize) -> spec_fn(int) -> bool {
        |pfn: int| self.spec_page_info(pfn as usize).unwrap().spec_order() == order
    }

    #[verifier(opaque)]
    spec fn pfn_dom(&self, order: usize) -> Set<int> {
        set_int_range(0, self.page_count() as int).filter(self.pfn_filter(order))
    }

    spec fn marked_compound(&self, pfn: usize, order: usize) -> bool {
        let n = 1usize << order;
        &&& order < N
        &&& self.valid_pfn_order(pfn, order)
        &&& forall|i|
            #![trigger self.spec_page_info(i)]
            pfn < i < pfn + n ==> self.spec_page_info(i) == Some(
                PageInfo::Compound(CompoundInfo { order }),
            )
    }

    spec fn marked_order(&self, pfn: usize, order: usize) -> bool {
        let pi = self.spec_page_info(pfn);
        &&& pi.is_some()
        &&& order < N
        &&& self.valid_pfn_order(pfn, order)
        &&& pi.unwrap().spec_order() == order
        &&& match pi.unwrap() {
            PageInfo::Reserved(_) => false,
            PageInfo::Compound(ci) => false,
            PageInfo::Slab(_) | PageInfo::File(_) => true,
            PageInfo::Allocated(_) => { self.marked_allocated(pfn, order) },
            PageInfo::Free(FreeInfo { next_page, .. }) => { self.marked_free(pfn, order, next_page)
            },
        }
    }

    spec fn marked_free_order(&self, pfn: usize, order: usize) -> bool {
        let pi = self.spec_page_info(pfn);
        &&& pi.unwrap().spec_order() == order
        &&& pi.unwrap().spec_get_free().is_some()
        &&& self.marked_compound(pfn, order)
    }

    spec fn marked_allocated(&self, pfn: usize, order: usize) -> bool {
        let pi = self.spec_page_info(pfn);
        &&& pi.unwrap().spec_order() == order
        &&& pi === Some(PageInfo::Allocated(AllocatedInfo { order }))
        &&& self.marked_compound(pfn, order)
    }

    spec fn marked_free(&self, pfn: usize, order: usize, next_pfn: usize) -> bool {
        let pi = self.spec_page_info(pfn);
        &&& pi === Some(PageInfo::Free(FreeInfo { next_page: next_pfn, order }))
        &&& self.marked_free_order(pfn, order)
    }

    spec fn marked_not_free(&self, pfn: usize, order: usize) -> bool {
        &&& self.marked_order(pfn, order)
        &&& !self.marked_free_order(pfn, order)
    }

    spec fn wf_page_info_at(&self, pfn: usize) -> bool {
        let pinfo = self.spec_page_info(pfn).unwrap();
        match pinfo {
            PageInfo::Reserved(_) => false,
            PageInfo::Allocated(ai) => { self.marked_compound(pfn, ai.order) },
            PageInfo::Free(fi) => { self.marked_compound(pfn, fi.order) },
            PageInfo::Slab(_) | PageInfo::File(_) => true,
            PageInfo::Compound(ci) => {
                let start = find_pfn_head(pfn, ci.order);
                &&& (self.marked_allocated(start, ci.order) || self.marked_free_order(
                    start,
                    ci.order,
                ))
                &&& ci.order > 0
            },
        }
    }

    #[verifier(opaque)]
    spec fn wf_page_info(&self) -> bool {
        forall|pfn: usize|
            #![trigger self.spec_page_info(pfn)]
            #![trigger self.reserved[pfn as int]]
            self.reserved_count() <= pfn < self.page_count() ==> self.wf_page_info_at(pfn)
    }

    spec fn wf_reserved_basic(&self) -> bool {
        forall|pfn: usize|
            #![trigger self.spec_page_info(pfn)]
            #![trigger self.reserved[pfn as int].is_init()]
            0 <= pfn < self.reserved_count() ==> #[trigger] self.spec_page_info(pfn) === Some(
                PageInfo::Reserved(ReservedInfo),
            )
    }

    spec fn wf_dom(&self) -> bool {
        &&& self.wf_strict_frac()
        &&& self.reserved.dom() === set_int_range(0, self.page_count() as int)
        &&& forall|pfn: usize|
            0 <= pfn < self.page_count() ==> #[trigger] (self.spec_page_info(pfn).is_some())
    }

    spec fn wf_ptr(&self, map: LinearMap) -> bool {
        &&& forall|pfn: usize|
            0 <= pfn < self.page_count() ==> self.reserved[pfn as int].ptr()
                == #[trigger] spec_map_page_info_ptr(map, pfn) && self.reserved[pfn as int].valid()
        &&& forall|pfn: usize|
            0 <= pfn < self.page_count() ==> #[trigger] self.reserved[pfn as int].valid()
    }

    spec fn wf(&self) -> bool {
        &&& self.wf_dom()
        &&& self.wf_reserved_basic()
        &&& self.wf_page_info()
        &&& self.page_count() <= MAX_PAGE_COUNT
    }

    spec fn spec_head_info(&self, pfn: usize) -> Option<PageInfo> {
        if self.spec_page_info(pfn).is_some() {
            self.spec_page_info(find_pfn_head(pfn, self.spec_page_info(pfn).unwrap().spec_order()))
        } else {
            None
        }
    }

    spec fn wf_strict_frac(&self) -> bool {
        &&& forall|pfn: usize|
            0 <= pfn < self.page_count() ==> #[trigger] self.reserved[pfn as int].total()
                == MAX_PGINFO_SHARES
        &&& forall|pfn: usize|
            0 <= pfn < self.reserved_count() ==> #[trigger] self.reserved[pfn as int].shares()
                == MAX_PGINFO_SHARES
        &&& MAX_PGINFO_SHARES == ALLOCATOR_PGINFO_SHARES + DEALLOC_PGINFO_SHARES
    }

    spec fn ens_allocate_pfn(&self, new: Self, pfn: usize, prev_pfn: usize, order: usize) -> bool {
        &&& new.marked_order(pfn, order)
        &&& new.reserved =~= self.reserved.union_prefer_right(
            Map::new(|k| k == pfn || k == prev_pfn, |k| new.reserved[k]),
        )
        &&& prev_pfn > 0 ==> new.marked_free_order(prev_pfn, order) && pfn_pages_is_writable(
            self.reserved,
            prev_pfn,
            1usize << order,
        )
    }
}

spec fn find_pfn_head(pfn: usize, order: usize) -> usize {
    crate::utils::util::spec_align_down(pfn as int, (1usize << order) as int) as usize
}

spec fn pfn_pages_is_writable<T>(
    reserved: Map<int, FracTypedPerm<T>>,
    pfn: usize,
    size: usize,
) -> bool {
    forall|p| pfn <= p < pfn + size ==> (#[trigger] reserved[p]).writable()
}

impl<const N: usize> MemoryRegionTracked<N> {
    #[verifier(inline)]
    spec fn pg_params(&self) -> PageCountParam<N> {
        PageCountParam { page_count: self.page_count() as usize }
    }

    #[verifier(inline)]
    spec fn pfn_pages_is_writable(&self, pfn: usize, size: usize) -> bool {
        pfn_pages_is_writable(self.reserved, pfn, size)
    }

    #[verifier(inline)]
    spec fn pfn_order_is_writable(&self, pfn: usize, order: usize) -> bool {
        self.pfn_pages_is_writable(pfn, 1usize << order)
    }

    #[verifier(inline)]
    spec fn reserved(&self) -> ReservedPerms<N> {
        ReservedPerms { page_count: self.pg_params(), reserved: self.reserved }
    }

    spec fn free_perms(&self) -> FreePerms<N> {
        FreePerms {
            page_count: self.pg_params(),
            avail: self.avail,
            next: self.next,
            map: self.map,
        }
    }

    spec fn free_pfn_len(&self, order: int) -> nat {
        self.next[order].len()
    }

    #[verifier(opaque)]
    spec fn free_dom(&self) -> Set<int> {
        self.full_pfn_dom().filter(
            |pfn: int|
                exists|o: usize, idx: int|
                    #![trigger self.next[o as int][idx]]
                    self.free_dom_at(o, idx).contains(pfn) && 0 <= idx < self.next[o as int].len()
                        && 0 <= o < N,
        )
    }

    #[verifier(opaque)]
    spec fn free_order_dom_rec(&self, order: usize, len: nat) -> Set<int> {
        self.full_pfn_dom().filter(
            |pfn: int|
                (exists|idx: int|
                    0 <= idx < len && (#[trigger] self.free_dom_at(order, idx)).contains(pfn)),
        )
    }

    spec fn free_order_dom(&self, order: usize) -> Set<int> {
        self.free_order_dom_rec(order, self.next[order as int].len())
    }

    spec fn free_dom_at(&self, order: usize, idx: int) -> Set<int> {
        set_int_range(
            self.next[order as int][idx] as int,
            self.next[order as int][idx] + (1usize << order),
        )
    }

    #[verifier(inline)]
    spec fn reserved_pfn_count(&self) -> nat {
        self.pg_params().reserved_pfn_count()
    }

    #[verifier(inline)]
    spec fn spec_page_info_addr(&self, pfn: usize) -> VirtAddr {
        spec_map_page_info_addr(self.map, pfn)
    }

    spec fn spec_page_info_ptr(&self, pfn: usize) -> *const PageStorageType {
        let addr = self.spec_page_info_addr(pfn)@;
        vstd::raw_ptr::ptr_from_data(
            vstd::raw_ptr::PtrData {
                addr,
                provenance: self.is_exposed@,
                metadata: vstd::raw_ptr::Metadata::Thin,
            },
        )
    }

    pub closed spec fn pfn_range_is_allocated(&self, pfn: usize, order: usize) -> bool {
        let next = self.next;
        forall|o: usize, i|
            #![trigger next[o as int][i]]
            0 <= o < N && 0 <= i < next[o as int].len() ==> order_disjoint(
                next[o as int][i],
                o,
                pfn,
                order,
            )
    }

    #[verifier(inline)]
    spec fn free_dom_disjoint(&self, pfn: usize, order: usize) -> bool {
        self.free_dom().disjoint(order_set(pfn, order))
    }

    spec fn next_page(&self, i: int) -> int {
        if self.next[i].len() == 0 {
            0
        } else {
            self.next[i].last() as int
        }
    }

    spec fn next_pages(&self) -> Seq<usize> {
        Seq::new(N as nat, |i| self.next_page(i) as usize)
    }

    spec fn free_page_counts(&self) -> Seq<nat> {
        Seq::new(N as nat, |i| self.next[i].len())
    }

    closed spec fn next_next_page(&self, i: int) -> int {
        let len = self.next[i].len();
        if len < 2 {
            0
        } else {
            self.next[i][len - 2] as int
        }
    }

    pub closed spec fn page_count(&self) -> nat {
        self.map.size / PAGE_SIZE as nat
    }

    pub closed spec fn max_free_page_count(&self) -> nat {
        (self.page_count() - self.reserved_pfn_count()) as nat
    }

    #[verifier(inline)]
    spec fn contained_by_order_idx(&self, pfn: usize, order: usize, o: int, i: int) -> bool {
        &&& self.next[o][i] <= pfn
        &&& (pfn + (1usize << order)) <= self.next[o][i] + (1usize << o)
        &&& order <= o < MAX_ORDER
        &&& 0 <= i < self.next[o].len()
    }

    spec fn contains_range(&self, pfn: usize, order: usize) -> bool {
        exists|o, i| self.contained_by_order_idx(pfn, order, o, i)
    }

    spec fn choose_order_idx(&self, pfn: usize, order: usize) -> (int, int) {
        choose|o, i| self.contained_by_order_idx(pfn, order, o, i)
    }

    #[verifier(inline)]
    spec fn full_pfn_dom(&self) -> Set<int> {
        set_int_range(self.reserved_pfn_count() as int, self.page_count() as int)
    }

    spec fn inv_remove_pfn(&self, new: Self) -> bool {
        forall|o, i|
            0 <= o < new.next.len() && 0 <= i < new.next[o].len() ==> self.next[o].contains(
                #[trigger] new.next[o][i],
            )
    }

    spec fn wf_params(&self) -> bool {
        let avail = self.avail;
        let next = self.next;
        &&& self.map.wf()
        &&& self.page_count() <= MAX_PAGE_COUNT
        &&& next.len() == N
        &&& self.is_exposed@ == allocator_provenance()
        &&& avail.dom() =~= Set::new(
            |k: (int, int)| 0 <= k.0 < N && 0 <= k.1 < self.next[k.0].len(),
        )
    }

    #[verifier(inline)]
    spec fn spec_page_storage_type(&self, pfn: int) -> Option<PageStorageType> {
        spec_page_storage_type(self.reserved[pfn].opt_value())
    }

    #[verifier(inline)]
    spec fn spec_page_info(&self, pfn: int) -> Option<PageInfo> {
        self.reserved().spec_page_info(pfn as usize)
    }

    #[verifier(inline)]
    spec fn spec_get_free_info(&self, pfn: int) -> Option<FreeInfo> {
        spec_free_info(self.reserved[pfn].opt_value())
    }

    pub closed spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        self.pg_params().valid_pfn_order(pfn, order)
    }

    #[verifier(inline)]
    spec fn wf_freep(&self, order: int, i: int) -> bool {
        self.free_perms().wf_at(order, i)
    }

    pub closed spec fn wf_at(&self, order: int, i: int) -> bool {
        let next = self.next[order];
        let pfn = next[i];
        let next_pfn = if i > 0 {
            next[i - 1]
        } else {
            0
        };
        &&& self.wf_freep(order, i)
        &&& self.marked_free(pfn, order as usize, next_pfn)
        &&& self.pfn_order_is_writable(pfn, order as usize)
    }

    spec fn wf_next(&self, order: int) -> bool {
        let i = self.next[order].len() - 1;
        i >= 0 ==> self.wf_at(order, i)
    }

    spec fn ens_allocate_pfn(&self, new: Self, pfn: usize, order: usize) -> bool {
        let target_next = new.next[order as int];
        let old_next = self.next[order as int];
        let idx = old_next.index_of(pfn);
        let size = 1usize << order;
        let prev_pfn = if idx < old_next.len() - 1 {
            old_next[idx + 1]
        } else {
            0
        };
        &&& self.inv_remove_pfn(new)
        &&& old_next.contains(pfn)
        &&& old_next[idx] == pfn
        &&& new.next === self.next.update(order as int, new.next[order as int])
        &&& idx === old_next.len() - 1 ==> new.reserved() === self.reserved()
        &&& self.reserved().ens_allocate_pfn(new.reserved(), pfn, prev_pfn, order)
    }

    spec fn wf_reserved(&self) -> bool {
        &&& self.reserved().wf_dom()
        &&& self.reserved().wf_ptr(self.map)
        &&& self.reserved().wf_reserved_basic()
    }

    spec fn wf_page_info_at(&self, pfn: usize) -> bool {
        self.reserved().wf_page_info_at(pfn)
    }

    spec fn wf_info_content(&self) -> bool {
        self.reserved().wf_page_info()
    }

    spec fn no_duplicates(&self) -> bool {
        &&& forall|order, i, j|
            0 <= order < N && 0 <= i < j < self.next[order].len() ==> #[trigger] self.next[order][i]
                != #[trigger] self.next[order][j]
    }

    spec fn wf_info(&self) -> bool {
        let next = self.next;
        &&& forall|order, i|
            0 <= order < N && 0 <= i < next[order].len() ==> #[trigger] self.wf_at(order, i)
        &&& self.wf_info_content()
        &&& self.no_duplicates()
    }

    spec fn wf_perms(&self) -> bool {
        let next = self.next;
        &&& self.wf_params()
        &&& self.free_perms().wf()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_params()
        &&& self.wf_info()
        &&& self.wf_reserved()
    }

    spec fn marked_compound(&self, pfn: usize, order: usize) -> bool {
        self.reserved().marked_compound(pfn, order)
    }

    #[verifier(inline)]
    spec fn marked_free(&self, pfn: usize, order: usize, next_pfn: usize) -> bool {
        self.reserved().marked_free(pfn, order, next_pfn)
    }

    #[verifier(inline)]
    spec fn marked_free_order(&self, pfn: usize, order: usize) -> bool {
        self.reserved().marked_free_order(pfn, order)
    }

    #[verifier(inline)]
    spec fn marked_allocated(&self, pfn: usize, order: usize) -> bool {
        self.reserved().marked_allocated(pfn, order)
    }

    #[verifier(inline)]
    spec fn marked_order(&self, pfn: usize, order: usize) -> bool {
        self.reserved().marked_order(pfn, order)
    }

    #[verifier(inline)]
    spec fn marked_not_free(&self, pfn: usize, order: usize) -> bool {
        self.reserved().marked_not_free(pfn, order)
    }
}

} // verus!
