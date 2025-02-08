use vstd::set_lib::set_int_range;
use vstd::simple_pptr::PointsTo;
use vstd::raw_ptr::PointsToRaw;
use verify_proof::tracked_exec_arbirary;
use verify_external::convert::FromSpec;
use verify_proof::bits::lemma_bit_usize_shl_values;
use crate::address::{spec_is_vaddr, spec_vaddr_offset};
use vstd::*;
use crate::mm::address_space::LinearMap;
use verify_external::hw_spec::{SpecMemMapTr, SpecVAddrImpl};

verus! {

include!("alloc.proof.verus.rs");

pub broadcast group alloc_proof {
    crate::address::sign_extend_proof,
    vstd::arithmetic::mul::lemma_mul_left_inequality,
}

pub broadcast group alloc_basic_axiom {
    crate::types::lemma_page_size,
    lemma_bit_usize_shl_values,
}

broadcast use alloc_proof;

global size_of PageStorageType == 8;

pub type RawMemPerm = PointsToRaw;

pub type TypedMemPerm<T> = PointsTo<T>;

type ReservedMapType = Map<int, TypedMemPerm<PageStorageType>>;

struct MapSeq<T> {
    pub map: Map<int, T>,
    pub ghost size: nat,
}

impl<T> MapSeq<T> {
    #[verifier::type_invariant]
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
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
            self.size == old(self).size + 1,
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
        self.size = (self.size - 1) as nat;
        assert(oldmap =~= self.map);
        self.map.tracked_remove(self.size as int)
    }
}

struct RawMemPermWithAddrSize<VAdrr: SpecVAddrImpl> {
    pub ghost vaddr: VAdrr,
    pub ghost size: nat,
    pub tracked perm: RawMemPerm,
}

impl<VAddr: SpecVAddrImpl> RawMemPermWithAddrSize<VAddr> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        let RawMemPermWithAddrSize { vaddr, size, perm } = *self;
        perm.dom() =~= vaddr.region_to_dom(size)
    }

    spec fn wf_vaddr_order(&self, vaddr: VAddr, order: usize) -> bool {
        let RawMemPermWithAddrSize { vaddr, size, perm } = *self;
        perm.dom() =~= vaddr.region_to_dom((1usize << order) as nat)
    }
}

#[verifier(inline)]
pub open spec fn spec_vaddr_range(start: int, end: int) -> Set<int> {
    Set::new(
        |v: int|
            v <= usize::MAX && spec_vaddr_offset(start) <= spec_vaddr_offset(v) < spec_vaddr_offset(
                end,
            ),
    )
}

struct VirtInfo<VAddr> {
    vaddr: VAddr,
    info_vaddr: VAddr
}

tracked struct MemoryRegionTracked<VAddr: SpecVAddrImpl, const N: usize> 
{
    tracked avail: Map<(int, int), RawMemPermWithAddrSize<VAddr>>,  //bucket -> next_id -> perm list
    ghost next: Seq<Seq<usize>>,  // bucket -> page_list
    tracked reserved: ReservedMapType,  //pfn -> pginfo
    ghost pfn_to_virt: Seq<VirtInfo<VAddr>>, // pfn -> virt address
}

pub trait AllocatorManagedMemory {
    spec fn wf_perm_for_alloc_range(
        &self,
        start: int,
        end: int,
    ) -> bool;/*closed spec fn wf_perm_for_alloc_order(&self, vaddr: VirtAddr, order: int) -> bool {
        self.wf_perm_for_alloc_range(vaddr, vaddr + (1usize << (order as usize)))
    }*/

}

impl AllocatorManagedMemory for RawMemPerm {
    // TODO: defines the memory property and content
    // e.g., allocator-managed memory is private
    open spec fn wf_perm_for_alloc_range(&self, start: int, end: int) -> bool {
        &&& self.dom() =~= spec_vaddr_range(start, end)
    }
}

proof fn lemma_vaddr_range_sub_of(start: int, end: int, start2: int, end2: int)
    requires
        spec_is_vaddr(start),
        spec_is_vaddr(end),
        spec_is_vaddr(start2),
        spec_is_vaddr(end2),
        start2 <= start,
        end <= end2,
        start <= end,
        start2 <= end2,
    ensures
        spec_vaddr_range(start, end).subset_of(spec_vaddr_range(start2, end2)),
{
    let d1 = spec_vaddr_range(start, end);
    let d2 = spec_vaddr_range(start2, end2);
    assert forall|v| d1.contains(v) implies d2.contains(v) by {
        assert(v <= usize::MAX);
        assert(spec_vaddr_offset(start) <= spec_vaddr_offset(v) < spec_vaddr_offset(end));
        assert(start2 <= start);
        assert(spec_vaddr_offset(start2) <= spec_vaddr_offset(start));
        assert(end <= end2);
        assert(spec_vaddr_offset(end) <= spec_vaddr_offset(end2));
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

spec fn spec_page_count<T>(next: Seq<Seq<T>>, max_order: usize) -> int
    decreases max_order,
{
    let order = max_order - 1;
    if max_order <= 0 {
        0
    } else {
        let prev_next = next.remove(order);
        spec_page_count(prev_next, order as usize) + next[order].len() * (1 << order)
    }
}

#[verifier(inline)]
spec fn spec_empty_seqs(max_order: int) -> Seq<Seq<usize>> {
    Seq::new(max_order as nat, |k| Seq::empty())
}

impl<VAddr: SpecVAddrImpl, const N: usize> MemoryRegionTracked<VAddr, N>
{
    proof fn tracked_new() -> (tracked ret: MemoryRegionTracked<VAddr, N>)
    ensures
        ret.wf(),
        ret.avail === Map::empty(),
        ret.reserved === Map::empty(),
        ret.pfn_to_virt === Seq::empty()
    decreases N,
    {
        Self::lemma_new_is_empty(N);
        let tracked ret = MemoryRegionTracked {
            avail: Map::tracked_empty(),
            reserved: Map::tracked_empty(),
            next: Seq::new(N as nat, |k| Seq::empty()),
            pfn_to_virt: Seq::empty(),
        };
        VirtAddr::lemma_wf(0usize);
        assert forall|i| 0 <= i < ret.page_count() implies ret.reserved.dom().contains(i) by {};
        ret
    }

    proof fn tracked_pop_next(tracked &mut self, order: int, pfn: int) -> (tracked ret:
        RawMemPermWithAddrSize<VAddr>)
        requires
            0 <= order < N,
            old(self).wf(),
            pfn == old(self).next_page(order),
            pfn > 0,
        ensures
            ret.wf_vaddr_order(self.pfn_to_virt[pfn].vaddr, order as usize),
            self.wf(),
            self.reserved === old(self).reserved,
            self.pfn_to_virt === old(self).pfn_to_virt,
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
        let vaddr = self.pfn_to_virt[pfn].vaddr;
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
}

impl<VAddr: SpecVAddrImpl, const N: usize> MemoryRegionTracked<VAddr, N> {
    pub closed spec fn spec_page_info_addr(&self, pfn: int) -> VAddr {
        self.pfn_to_virt[pfn].info_vaddr
    }
    pub closed spec fn next_page(&self, i: int) -> int {
        if self.next[i].len() == 0 {
            0
        } else {
            self.next[i].last() as int
        }
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

    closed spec fn next_next_page(&self, i: int) -> int {
        let len = self.next[i].len();
        if len < 2 {
            0
        } else {
            self.next[i][len - 2] as int
        }
    }

    pub closed spec fn page_count(&self) -> nat {
        self.pfn_to_virt.len()
    }

    spec fn wf_dom(&self) -> bool {
        let avail = self.avail;
        let next = self.next;
        let reserved = self.reserved;
        let page_count = self.page_count();
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

    pub closed spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        let n = 1usize << order;
        &&& pfn < self.page_count()
        &&& pfn + n <= self.page_count()
        &&& order < MAX_ORDER
    }

    spec fn wf_item(&self, order: int, i: int) -> bool {
        let next = self.next[order];
        let pfn = next[i] as int;
        let perm = self.avail[(order, i)];
        let info = self.get_free_info(pfn);
        let vaddr = self.pfn_to_virt[pfn].vaddr;
        &&& pfn > 0
        &&& self.valid_pfn_order(pfn as usize, order as usize)
        &&& perm.wf_vaddr_order(vaddr, order as usize)
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
        spec_page_count(self.next, N)
    }

    spec fn wf_reserved(&self) -> bool {
        let reserved = self.reserved;
        let page_count = self.page_count();
        &&& forall|pfn: int|
            #![trigger reserved[pfn]]
            0 <= pfn < page_count ==> (reserved[pfn].addr() == self.spec_page_info_addr(pfn).spec_int_addr().unwrap()
                && self.spec_page_info(pfn).is_some())
        &&& reserved.dom() =~= set_int_range(0, page_count as int)
    }

    spec fn wf_info(&self) -> bool {
        let next = self.next;
        &&& forall|order, i|
            0 <= order < N && 0 <= i < next[order].len() ==> #[trigger] self.wf_item(order, i)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_dom()
        &&& self.wf_info()
        &&& self.wf_reserved()
    }

    proof fn lemma_new_is_empty(max_order: usize)
        requires
            max_order >= 0,
        ensures
            spec_page_count(spec_empty_seqs(max_order as int), max_order) == 0,
        decreases max_order,
    {
        let next = spec_empty_seqs(max_order as int);
        if max_order > 0 {
            let prev_next = spec_empty_seqs(max_order - 1);
            Self::lemma_new_is_empty((max_order - 1) as usize);
            assert(prev_next =~= next.remove(max_order - 1));
            assert(next[max_order - 1].len() == 0);
        } else {
            assert(spec_page_count(next, max_order) == 0);
        }
    }

    spec fn marked_free(&self, pfn: int, order: usize, next_pfn: usize) -> bool {
        let pi = self.spec_page_info(pfn);
        pi === Some(PageInfo::Free(FreeInfo { next_page: next_pfn, order }))
    }
}

impl MemoryRegion {
    pub closed spec fn view(&self) -> MemoryRegionTracked<VirtAddr, MAX_ORDER> {
        self.perms@
    }

    spec fn map(&self) -> LinearMap {
        LinearMap {
            start_virt: self.start_virt,
            start_phys: self.start_phys@ as int,
            size: (self.page_count * PAGE_SIZE) as nat
        }
    }

    pub closed spec fn spec_get_pfn(&self, vaddr: VirtAddr) -> int {
        (self.map().get_paddr(vaddr) - self.start_phys@) / PAGE_SIZE as int
    }

    pub closed spec fn spec_try_get_virt(&self, pfn: int) -> Option<VirtAddr> {
        let phy = self.start_phys@ + pfn * PAGE_SIZE;
        self.map().to_vaddr(phy)
    }

    pub closed spec fn spec_get_virt(&self, pfn: int) -> VirtAddr {
        self.spec_try_get_virt(pfn).unwrap()
    }

    /*
    pub open spec fn wf_page_count(&self) -> bool {
        let page_count = self.page_count;
        &&& self.start_virt.is_canonical()
        &&& self.start_virt().offset() + (page_count - 1) * PAGE_SIZE < crate::address::VADDR_RANGE_SIZE
    }
    */
    pub closed spec fn wf_page_count(&self) -> bool {
        if self.page_count > 0 {
            let pfn = self.page_count - 1;
            self.map().to_vaddr(self.start_phys@ + pfn * PAGE_SIZE).is_some()
        } else {
            true
        }
    }

    proof fn lemma_get_virt(&self, pfn: int) -> (ret: VirtAddr)
        requires
            self.wf_params(),
            0 <= pfn < self@.page_count(),
        ensures
            self.spec_try_get_virt(pfn).is_some(),
            ret == self.spec_get_virt(pfn),
            ret.is_canonical(),
            ret.offset() ==  self.start_virt.offset() + (pfn * PAGE_SIZE),
    {
        broadcast use crate::types::lemma_page_size;
        crate::address::lemma_vaddr_upper_mask();
        assert(self.start_virt.is_canonical());
        VirtAddr::lemma_wf((self.start_virt@ + (pfn * PAGE_SIZE)) as usize);
        self.spec_get_virt(pfn)
    }

    closed spec fn wf_accounting(&self) -> bool {
        &&& forall |order| 0 <= order < MAX_ORDER ==>
            #[trigger]self.free_pages[order]  <= self.nr_pages[order] <= self.page_count / (1usize << order as usize)
    }

    closed spec fn wf_accounting_strict(&self) -> bool {
        &&& forall |order| self.nr_pages[order] == self.free_pages[order]
    }

    spec fn spec_page_info_addr(&self, pfn: int) -> VirtAddr {
        let reserved_unit_size = size_of::<PageStorageType>();
        let start = self.start_virt;
        VirtAddr::from_spec((start@ + (pfn * reserved_unit_size)) as usize)
    }

    // Basic invariant that should hold except in initialization stage
    pub closed spec fn wf_params(&self) -> bool {
        let perms = self@;
        &&& perms.next_pages().len() == MAX_ORDER
        &&& perms.pfn_to_virt =~= Seq::new(self.page_count as nat, 
            |pfn| VirtInfo {
                vaddr: self.spec_get_virt(pfn),
                info_vaddr: self.spec_page_info_addr(pfn)
            }
        )
        &&& self@.page_count() == self.page_count
        &&& self.start_virt.is_canonical()
        &&& self.wf_accounting()
        &&& self.wf_page_count()
    }

    pub closed spec fn wf_reserved(&self) -> bool {
        &&& self@.wf_reserved()
        &&& self.wf_params()
    }

    // Strict invariant that should hold at public interfaces.
    pub closed spec fn wf_after_init(&self) -> bool {
        let perms = self@;
        &&& perms.wf()
        &&& self.wf_params()
        &&& perms.next_pages() =~= self.next_page@
        &&& perms.free_page_counts() =~= Seq::new(MAX_ORDER as nat, |i| self.free_pages[i] as nat)
        &&& perms.wf_reserved()
    }

    pub closed spec fn ensures_get_next_page(
        &self,
        new_self: &Self,
        order: usize,
        ret: Result<usize, AllocError>,
    ) -> bool {
        let perms = self.perms@;
        let new_perms = new_self.perms@;
        let tmp = self.tmp_perms@.to_seq();
        let new_tmp = new_self.tmp_perms@.to_seq();
        let perm = new_tmp.last();
        let vaddr = new_self.spec_get_virt(ret.unwrap() as int);
        let order = order as int;
        &&& self.wf_after_init()
        &&& ret.is_err() == (self.next_page[order] == 0)
        &&& ret.is_ok() ==> {
            &&& perm.wf_vaddr_order(vaddr, order as usize)
            &&& new_tmp =~= tmp.push(perm)
            &&& new_self.tmp_perms@.size == self.tmp_perms@.size + 1
            &&& ret.unwrap() == self.next_page[order]
            &&& new_self.valid_pfn_order(ret.unwrap(), order as usize)
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
        self@.valid_pfn_order(pfn, order)
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

    pub closed spec fn req_split_page(&self, pfn: usize, order: usize) -> bool {
        let perm = self.tmp_perms@.last();
        let vaddr = self.spec_get_virt(pfn as int);
        &&& self.tmp_perms@.size > 0
        &&& perm.wf_vaddr_order(vaddr, order as usize)
        &&& self.valid_pfn_order(pfn, order)
        &&& order >= 1
        &&& self.wf_after_init()
        &&& self.free_pages[order - 1] + 2 < usize::MAX
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
        &&& new.wf_after_init()
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
        let MemoryRegionTracked { avail, next, reserved, .. } = self@;
        let tmp = self.tmp_perms@.to_seq();
        let new_tmp = new.tmp_perms@.to_seq();
        &&& tmp === new_tmp
        &&& new@.avail === avail
        &&& new@.next === next
        &&& new@.pfn_to_virt === self@.pfn_to_virt
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
