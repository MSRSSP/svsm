verus! {

use vstd::set_lib::set_int_range;
use vstd::simple_pptr::PointsTo;
use vstd::raw_ptr::PointsToRaw;
use verify_proof::tracked_exec_arbirary;
use verify_external::convert::FromSpec;
use verify_proof::bits::lemma_bit_usize_shl_values;
use vstd::*;

include!("alloc.proof.verus.rs");

pub broadcast group alloc_proof {
    crate::address::sign_extend_proof,
    crate::types::lemma_page_size,
    vstd::arithmetic::mul::lemma_mul_left_inequality,
}

broadcast use alloc_proof;

global size_of PageStorageType == 8;

pub type RawMemPerm = PointsToRaw;

pub type TypedMemPerm<T> = PointsTo<T>;

type ReservedMapType = Map<int, TypedMemPerm<PageStorageType>>;

struct RangedMap<T> {
    pub map: Map<int, T>,
    pub ghost size: int,
}

impl<T> RangedMap<T> {
    #[verifier::type_invariant]
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        &&& self.size >= 0
        &&& forall|i| 0 <= i < self.size ==> self.map.dom().contains(i)
    }

    pub closed spec fn last(&self) -> T {
        self.to_seq().last()
    }

    pub closed spec fn to_seq(&self) -> Seq<T> {
        Seq::new(self.size as nat, |i| self.map[i])
    }

    proof fn tracked_push(tracked &mut self, tracked v: T)
        ensures
            self.to_seq() =~= old(self).to_seq().push(v),
    {
        use_type_invariant(&*self);
        self.map.tracked_insert(self.size as int, v);
        self.size = self.size + 1;
    }

    proof fn tracked_pop(tracked &mut self) -> (tracked ret: T)
        requires
            old(self).size > 0,
        ensures
            ret === old(self).last(),
            self.to_seq().len() == old(self).to_seq().len() - 1,
            self.to_seq() =~= old(self).to_seq().take(old(self).to_seq().len() - 1),
    {
        use_type_invariant(&*self);
        let oldmap = self.map;
        self.size = self.size - 1;
        assert(oldmap =~= self.map);
        self.map.tracked_remove(self.size as int)
    }
}

struct RawMemPermWithAddrOrder {
    pub vaddr: VirtAddr,
    pub order: int,
    pub perm: RawMemPerm,
}

impl RawMemPermWithAddrOrder {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        let RawMemPermWithAddrOrder { vaddr, order, perm } = *self;
        perm.wf_perm_for_alloc_order(vaddr@ as int, order)
    }
}

tracked struct MemoryRegionPerms<const N: usize> {
    tracked avail: Map<(int, int), RawMemPermWithAddrOrder>,  //bucket -> next_id -> perm list
    tracked reserved: ReservedMapType,  //pfn -> pginfo
    ghost next: Seq<Seq<usize>>,  // bucket -> page_list
    ghost page_count: nat,
    ghost start_phys: int,
    ghost start_virt: VirtAddr,
}

ghost struct MemoryRegionParameters {
    ghost page_count: nat,
    ghost start_phys: int,
    ghost start_virt: VirtAddr,
}

pub trait AllocatorManagedMemory {
    spec fn wf_perm_for_alloc_range(&self, start: int, end: int) -> bool;

    closed spec fn wf_perm_for_alloc_order(&self, vaddr: int, order: int) -> bool {
        self.wf_perm_for_alloc_range(vaddr, vaddr + (1usize << (order as usize)))
    }
}

impl AllocatorManagedMemory for RawMemPerm {
    // TODO: defines the memory property and content
    // e.g., allocator-managed memory is private
    open spec fn wf_perm_for_alloc_range(&self, start: int, end: int) -> bool {
        self.is_range(start, end)
    }
}

impl PageInfo {
    spec fn get_free(&self) -> Option<FreeInfo> {
        match *self {
            PageInfo::Free(info) => { Some(info) },
            _ => { None },
        }
    }
}

spec fn spec_page_count<T>(next: Seq<Seq<T>>, max_order: int) -> int
    decreases max_order,
{
    if max_order <= 0 {
        0
    } else {
        let prev_next = next.remove(max_order - 1);
        spec_page_count(prev_next, max_order - 1) + next[max_order - 1].len()
    }
}

#[verifier(inline)]
spec fn spec_empty_seqs(max_order: int) -> Seq<Seq<usize>> {
    Seq::new(max_order as nat, |k| Seq::empty())
}

impl<const N: usize> MemoryRegionPerms<N> {
    pub closed spec fn params(&self) -> MemoryRegionParameters {
        let MemoryRegionPerms { page_count, start_phys, start_virt, .. } = *self;
        MemoryRegionParameters { page_count, start_phys, start_virt }
    }

    pub closed spec fn page_count(&self) -> nat {
        self.page_count
    }

    pub closed spec fn start_virt(&self) -> VirtAddr {
        self.start_virt
    }

    pub closed spec fn start_phys(&self) -> int {
        self.start_phys
    }

    pub closed spec fn get_pfn(&self, vaddr: VirtAddr) -> int {
        (vaddr.offset() - self.start_virt.offset()) / PAGE_SIZE as int
    }

    pub closed spec fn get_virt(&self, pfn: int) -> VirtAddr {
        VirtAddr::from_spec((self.start_virt@ + (pfn * PAGE_SIZE)) as usize)
    }

    #[verifier(inline)]
    pub open spec fn next_pages(&self) -> Seq<usize> {
        Seq::new(N as nat, |i| self.next_page(i) as usize)
    }

    #[verifier(inline)]
    spec fn free_page_counts(&self) -> Seq<nat> {
        Seq::new(N as nat, |i| self.next[i].len())
    }

    closed spec fn next_pages_after_remove(&self, order: int) -> Seq<usize> {
        Seq::new(
            N as nat,
            |i|
                if order == i {
                    self.next_next_page(i) as usize
                } else {
                    self.next_page(i) as usize
                },
        )
    }

    pub closed spec fn next_page(&self, i: int) -> int {
        if self.next[i].len() == 0 {
            0
        } else {
            self.next[i].last() as int
        }
    }

    closed spec fn next_next_page(&self, i: int) -> int {
        let len = self.next[i].len();
        if len < 2 {
            0
        } else {
            self.next[i][len - 2] as int
        }
    }

    spec fn wf_dom(&self) -> bool {
        let avail = self.avail;
        let next = self.next;
        let reserved = self.reserved;
        let page_count = self.page_count;
        &&& next.len() == N
        &&& avail.dom() =~= Set::new(
            |k: (int, int)| 0 <= k.0 < N && 0 <= k.1 < self.next[k.0].len(),
        )
        &&& reserved.dom() =~= set_int_range(0, page_count as int)
    }

    #[verifier(inline)]
    spec fn spec_page_storage_type(&self, pfn: int) -> Option<PageStorageType> {
        let mem = self.reserved[pfn].opt_value();
        if mem.is_init() {
            Some(mem.value())
        } else {
            None
        }
    }

    #[verifier(inline)]
    spec fn spec_page_info(&self, pfn: int) -> Option<PageInfo> {
        let mem = self.spec_page_storage_type(pfn);
        if mem.is_some() {
            PageInfo::spec_decode(mem.unwrap())
        } else {
            None
        }
    }

    spec fn get_free_info(&self, pfn: int) -> Option<FreeInfo> {
        let p_info = self.spec_page_info(pfn);
        if p_info.is_some() {
            let pi = p_info.unwrap();
            pi.get_free()
        } else {
            None
        }
    }

    spec fn wf_item(&self, order: int, i: int) -> bool {
        let next = self.next[order];
        let pfn = next[i] as int;
        let perm = self.avail[(order, i)];
        let info = self.get_free_info(pfn);
        let vaddr = self.get_virt(pfn);
        &&& 0 < pfn < self.page_count
        &&& perm.order == order
        &&& perm.vaddr == vaddr
        &&& info.is_some()
        &&& if i > 0 {
            info.unwrap().next_page == next[i - 1]
        } else {
            info.unwrap().next_page == 0
        }
        &&& info.unwrap().order == order
    }

    spec fn wf_next(&self, order: int) -> bool {
        let i = self.next[order].len() - 1;
        self.wf_item(order, i)
    }

    spec fn spec_page_count(&self) -> int {
        spec_page_count(self.next, N as int)
    }

    spec fn spec_pfn_info_addr(&self, pfn: int) -> VirtAddr {
        let reserved_unit_size = size_of::<PageStorageType>();

        VirtAddr::from_spec((self.start_virt@ + (pfn * reserved_unit_size)) as usize)
    }

    spec fn wf_reserved(&self) -> bool {
        let reserved = self.reserved;
        &&& forall|pfn: int|
            #![trigger reserved[pfn]]
            0 <= pfn < self.page_count ==> (reserved[pfn].addr() == self.spec_pfn_info_addr(pfn)@
                && self.spec_page_info(pfn).is_some())
        &&& reserved.dom() =~= set_int_range(0, self.page_count as int)
    }

    spec fn wf_info(&self) -> bool {
        let next = self.next;
        &&& forall|order, i|
            0 <= order < N && 0 <= i < next[order].len() ==> #[trigger] self.wf_item(order, i)
        &&& self.wf_reserved()
    }

    pub open spec fn wf_page_count(&self) -> bool {
        let page_count = self.page_count();

        page_count > 0 ==> (page_count - 1) * PAGE_SIZE < (crate::address::VADDR_RANGE_SIZE
            - self.start_virt().offset())
    }

    proof fn lemma_wf_pfn(&self, pfn: int)
        requires
            self.wf_page_count(),
            pfn < self.page_count,
        ensures
            pfn * PAGE_SIZE < crate::address::VADDR_RANGE_SIZE - self.start_virt().offset(),
            pfn * size_of::<PageStorageType>() < crate::address::VADDR_RANGE_SIZE
                - self.start_virt().offset(),
    {
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_dom()
        &&& self.wf_info()
        &&& self.wf_page_count()
    }

    proof fn lemma_new_is_empty(max_order: int)
        requires
            max_order >= 0,
        ensures
            spec_page_count(spec_empty_seqs(max_order), max_order) == 0,
        decreases max_order,
    {
        let next = spec_empty_seqs(max_order);
        if max_order > 0 {
            let prev_next = spec_empty_seqs(max_order - 1);
            Self::lemma_new_is_empty(max_order - 1);
            assert(prev_next =~= next.remove(max_order - 1));
            assert(next[max_order - 1].len() == 0);
        } else {
            assert(spec_page_count(next, max_order) == 0);
        }
    }

    pub proof fn tracked_new() -> (tracked ret: MemoryRegionPerms<N>)
        ensures
            ret.wf(),
            ret.start_virt() == VirtAddr::from_spec(0usize),
            ret.start_phys() == 0,
            ret.page_count() == 0,
            ret.next_pages() =~= Seq::new(N as nat, |i| 0),
        decreases N,
    {
        Self::lemma_new_is_empty(N as int);
        let tracked ret = MemoryRegionPerms {
            avail: Map::tracked_empty(),
            reserved: Map::tracked_empty(),
            next: spec_empty_seqs(N as int),
            page_count: 0,
            start_phys: 0,
            start_virt: VirtAddr::from_spec(0usize),
        };
        assert forall|i| 0 <= i < ret.page_count implies ret.reserved.dom().contains(i) by {};
        ret
    }

    proof fn tracked_pop_next_perm(tracked &mut self, order: int, pfn: int) -> (tracked ret:
        RawMemPermWithAddrOrder)
        requires
            0 <= order < N,
            old(self).wf(),
            pfn == old(self).next_page(order),
            pfn > 0,
        ensures
            ret.order == order,
            ret.vaddr == self.get_virt(pfn),
            self.wf(),
            self.params() === old(self).params(),
            self.reserved === old(self).reserved,
            self.next_page(order) == old(self).next_next_page(order),
            self.next_page(order) == old(self).get_free_info(pfn).unwrap().next_page,
            self.next_pages() =~= old(self).next_pages().update(
                order,
                self.next_page(order) as usize,
            ),
            self.free_page_counts() =~~= old(self).free_page_counts().update(
                order,
                (old(self).free_page_counts()[order] - 1) as nat,
            ),
    {
        let vaddr = self.get_virt(pfn);
        let last_idx = self.next[order].len() - 1;
        let old_self = *self;
        assert(self.wf_item(order, last_idx));
        let tracked perm = self.avail.tracked_remove((order, last_idx));
        self.next = self.next.update(order, self.next[order].take(last_idx));
        assert(self.next[order].len() == last_idx);
        let next = self.next;
        assert forall|o, i| 0 <= o < N && 0 <= i < next[o].len() implies self.wf_item(o, i) by {
            assert(old_self.wf_item(o, i));
        }
        assert(self.free_page_counts()[order] == self.next[order].len());
        assert(self.wf());
        perm
    }

    spec fn marked_free(&self, pfn: int, order: usize, next_pfn: usize) -> bool {
        let pi = self.spec_page_info(pfn);
        pi === Some(PageInfo::Free(FreeInfo { next_page: next_pfn, order }))
    }
}

impl MemoryRegion {
    spec fn view(&self) -> MemoryRegionPerms<MAX_ORDER> {
        self.perms@
    }

    pub closed spec fn wf_params(&self) -> bool {
        let perms = self@;
        &&& perms.wf_page_count()
        &&& perms.start_phys() == self.start_phys@
        &&& perms.start_virt() === self.start_virt
        &&& perms.page_count() == self.page_count
        &&& perms.next_pages().len() == MAX_ORDER
    }

    pub closed spec fn wf_after_init(&self) -> bool {
        let perms = self@;
        &&& perms.wf()
        &&& self.wf_params()
        &&& perms.next_pages() =~= self.next_page@
        &&& perms.free_page_counts() =~= Seq::new(MAX_ORDER as nat, |i| self.free_pages[i] as nat)
        &&& perms.wf_reserved()
    }

    pub closed spec fn wf_reserved(&self) -> bool {
        &&& self@.wf_reserved()
        &&& self.wf_params()
    }

    pub closed spec fn ensures_get_next_page(
        &self,
        order: int,
        new_self: &Self,
        ret: Result<usize, AllocError>,
    ) -> bool {
        let perms = self.perms@;
        let new_perms = new_self.perms@;
        let tmp = self.tmp_perms@.to_seq();
        let new_tmp = new_self.tmp_perms@.to_seq();
        let perm = new_tmp.last();
        let vaddr = new_perms.get_virt(ret.unwrap() as int);
        &&& self.wf_after_init()
        &&& ret.is_err() == (self.next_page[order] == 0)
        &&& ret.is_ok() ==> {
            &&& perm.order == order
            &&& perm.vaddr == vaddr
            &&& new_tmp =~= tmp.push(perm)
            &&& ret.unwrap() == self.next_page[order]
        }
        &&& ret.is_err() ==> perms === new_perms
    }

    pub closed spec fn ens_read_page_info(self, pfn: usize, ret: PageInfo) -> bool {
        &&& self@.spec_page_info(pfn as int).is_some()
        &&& self@.spec_page_info(pfn as int).unwrap() === ret
    }

    pub closed spec fn spec_alloc_fails(&self, order: int) -> bool {
        forall|i| #![trigger self.next_page[i]] order <= i < MAX_ORDER ==> self.next_page[i] == 0
    }

    pub closed spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        &&& pfn < self.page_count
        &&& order < MAX_ORDER
    }

    pub closed spec fn ens_has_free_pages(&self, new: Self, ret: bool, order: int) -> bool {
        let new_free_perms = new@.next;
        // No available if no slot >= order
        let valid_order = (0 <= order < MAX_ORDER);
        if self.spec_alloc_fails(order) || !valid_order {
            &&& *self === new
            &&& !ret
        } else {
            &&& ret
            &&& new_free_perms[order].len() > 0
        }
    }

    pub closed spec fn req_tmp_perm(&self, pfn: usize, order: usize) -> bool {
        let perm = self.tmp_perms@.last();
        let vaddr = self@.get_virt(pfn as int);
        &&& perm.vaddr == vaddr
        &&& perm.order == order
    }

    pub closed spec fn ens_split_page_ok(&self, new: Self, pfn: usize, order: usize) -> bool {
        let free_perms = self@.next;
        let new_free_perms = new@.next;
        let tmp = self.tmp_perms@.to_seq();
        let new_tmp = new.tmp_perms@.to_seq();
        let rhs_pfn = (pfn + (1usize << order) / 2) as usize;
        let new_order = order - 1;
        let p = free_perms[new_order];
        let newp = p.push(pfn).push(rhs_pfn);
        &&& new_free_perms =~= free_perms.update(new_order, newp)
        &&& new_tmp =~= tmp.take(tmp.len() - 1)
    }

    pub closed spec fn req_write_page_info(&self, pfn: usize) -> bool {
        self.wf_reserved()
    }

    pub closed spec fn ens_write_page_info(&self, new: Self, pfn: usize, pi: PageInfo) -> bool {
        &&& self.only_update_reserved(new)
        &&& new@.reserved =~~= self@.reserved.insert(pfn as int, new@.reserved[pfn as int])
        &&& new@.spec_page_info(pfn as int) === Some(pi)
        &&& new.wf_reserved()
    }

    pub closed spec fn req_mark_compound_page(&self, pfn: usize, order: usize) -> bool {
        &&& self.wf_reserved()
        &&& self.valid_pfn_order(pfn, order)
    }

    pub closed spec fn ens_mark_compound_page(&self, new: Self, pfn: usize, n: usize) -> bool {
        let pfn = pfn as int;
        &&& self.only_update_reserved(new)
        &&& new@.reserved =~~= self@.reserved.union_prefer_right(
            Map::new(|i| pfn < i < pfn + n, |i| new@.reserved[i]),
        )
        &&& new@.reserved[pfn] === self@.reserved[pfn]
        &&& new.wf_reserved()
    }

    pub closed spec fn req_init_compound_page(
        &self,
        pfn: usize,
        order: usize,
        next_pfn: usize,
    ) -> bool {
        &&& self.valid_pfn_order(pfn, order)
        &&& self.wf_reserved()
    }

    spec fn only_update_reserved(&self, new: Self) -> bool {
        let MemoryRegionPerms { avail, next, reserved, .. } = self@;
        let tmp = self.tmp_perms@.to_seq();
        let new_tmp = new.tmp_perms@.to_seq();
        &&& tmp === new_tmp
        &&& new@.avail === avail
        &&& new@.next === next
        &&& new@.params() === self@.params()
    }

    pub closed spec fn ens_init_compound_page(
        &self,
        new: Self,
        pfn: usize,
        order: usize,
        next_pfn: usize,
    ) -> bool {
        let n = 1usize << order;
        let pfn = pfn as int;
        //let c_changes = Map::new(|i|  pfn < i < pfn + n, |i|new@.reserved[i]);
        let changes = Map::new(|i| pfn <= i < pfn + n, |i| new@.reserved[i]);
        //&&& n > 0
        //&&& new@.reserved =~~= self@.reserved.insert(pfn, new@.reserved[pfn]).union_prefer_right(c_changes)
        //&&& !c_changes.dom().contains(pfn)
        &&& self.only_update_reserved(new)
        &&& new@.reserved =~~= self@.reserved.union_prefer_right(changes)
        &&& new@.marked_free(pfn, order, next_pfn)
        &&& new.wf_reserved()
    }
}

trait FromPageStorageTypeSpec: core::marker::Sized {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    proof fn proof_encode_decode(&self)
        ensures
            Self::spec_decode(self.spec_encode()).is_some(),
            Self::spec_decode(self.spec_encode()).unwrap() === *self,
    ;
}

impl FromPageStorageTypeSpec for PageType {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self) {
    }
}

impl FromPageStorageTypeSpec for FreeInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::Free),
    {
    }
}

impl FromPageStorageTypeSpec for AllocatedInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::Allocated),
    {
    }
}

impl FromPageStorageTypeSpec for SlabPageInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::SlabPage),
    {
    }
}

impl FromPageStorageTypeSpec for CompoundInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::Compound),
    {
    }
}

impl FromPageStorageTypeSpec for FileInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::File),
    {
    }
}

impl FromPageStorageTypeSpec for ReservedInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self>;

    spec fn spec_encode(&self) -> PageStorageType;

    #[verifier::external_body]
    proof fn proof_encode_decode(&self)
        ensures
            PageType::spec_decode(self.spec_encode()) === Some(PageType::Reserved),
    {
    }
}

impl FromPageStorageTypeSpec for PageInfo {
    spec fn spec_decode(mem: PageStorageType) -> Option<Self> {
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

    spec fn spec_encode(&self) -> PageStorageType {
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
