use verify_external::convert::FromSpec;
use verify_external::hw_spec::{SpecMemMapTr, SpecVAddrImpl};
use verify_proof::bits::lemma_bit_usize_shl_values;
use verify_proof::tracked_exec_arbirary;
use verify_proof::tseq::TrackedSeq;
use vstd::arithmetic::mul::lemma_mul_inequality;
use vstd::raw_ptr::PointsToRaw;
use vstd::set_lib::set_int_range;
use vstd::simple_pptr::PointsTo;
//use vstd::;

verus! {

use crate::mm::address_space::LinearMap;

include!("alloc.proof.verus.rs");

pub broadcast group alloc_proof {
    crate::address::sign_extend_proof,
}

pub broadcast group alloc_size_proof {
    crate::types::lemma_page_size,
    lemma_bit_usize_shl_values,
}

//broadcast use alloc_proof;
global size_of PageStorageType == 8;

pub type RawPerm = PointsToRaw;

pub type TypedPerm<T> = PointsTo<T>;

pub trait MemPermWithVAddrOrder<VAddr: SpecVAddrImpl> {
    spec fn wf_vaddr_order(&self, vaddr: VAddr, order: usize) -> bool;
}

impl<VAddr: SpecVAddrImpl> MemPermWithVAddrOrder<VAddr> for RawPerm {
    open spec fn wf_vaddr_order(&self, vaddr: VAddr, order: usize) -> bool {
        let size = ((1usize << order) * PAGE_SIZE) as nat;
        self.dom() =~= vaddr.region_to_dom(size)
    }
}

spec fn spec_page_storage_type(perm: TypedPerm<PageStorageType>) -> Option<PageStorageType> {
    if perm.is_init() {
        Some(perm.value())
    } else {
        None
    }
}

spec fn spec_page_info(perm: TypedPerm<PageStorageType>) -> Option<PageInfo> {
    let mem = spec_page_storage_type(perm);
    if mem.is_some() {
        PageInfo::spec_decode(mem.unwrap())
    } else {
        None
    }
}

spec fn spec_free_info(perm: TypedPerm<PageStorageType>) -> Option<FreeInfo> {
    let p_info = spec_page_info(perm);
    if p_info.is_some() {
        let pi = p_info.unwrap();
        pi.get_free()
    } else {
        None
    }
}

spec fn get_compound_info(perm: TypedPerm<PageStorageType>) -> Option<CompoundInfo> {
    let p_info = spec_page_info(perm);
    if p_info.is_some() {
        let pi = p_info.unwrap();
        pi.get_compound()
    } else {
        None
    }
}

struct VirtInfo<VAddr> {
    vaddr: VAddr,
    info_vaddr: VAddr,
}

tracked struct MemoryRegionTracked<VAddr: SpecVAddrImpl, const N: usize> {
    tracked avail: Map<(int, int), RawPerm>,  //(order, idx) -> perm
    ghost next: Seq<Seq<usize>>,  // order -> next page list
    tracked reserved: Map<int, TypedPerm<PageStorageType>>,  //pfn -> pginfo
    ghost pfn_to_virt: Seq<VirtInfo<VAddr>>,  // pfn -> virt address
}

impl PageInfo {
    spec fn get_free(&self) -> Option<FreeInfo> {
        match *self {
            PageInfo::Free(info) => { Some(info) },
            _ => { None },
        }
    }

    spec fn get_compound(&self) -> Option<CompoundInfo> {
        match *self {
            PageInfo::Compound(info) => { Some(info) },
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

impl<VAddr: SpecVAddrImpl, const N: usize> MemoryRegionTracked<VAddr, N> {
    proof fn tracked_new() -> (tracked ret: MemoryRegionTracked<VAddr, N>)
        ensures
            ret.wf(),
            ret.avail === Map::empty(),
            ret.reserved === Map::empty(),
            ret.pfn_to_virt === Seq::empty(),
    {
        let tracked ret = MemoryRegionTracked {
            avail: Map::tracked_empty(),
            reserved: Map::tracked_empty(),
            next: Seq::new(N as nat, |k| Seq::empty()),
            pfn_to_virt: Seq::empty(),
        };
        VirtAddr::lemma_wf(0usize);
        assert(ret.reserved.dom() =~= set_int_range(0, 0));
        //assert forall|i| 0 <= i < ret.page_count() implies ret.reserved.dom().contains(i) by {};
        ret
    }

    proof fn tracked_pop_next(tracked &mut self, order: int, pfn: int) -> (tracked ret: RawPerm)
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
            self.next === old(self).next.update(
                order,
                old(self).next[order].take(old(self).next[order].len() - 1),
            ),
            self.next_page(order) == old(self).next_next_page(order),
            self.next_page(order) == old(self).get_free_info(pfn).unwrap().next_page,
            self.next_pages() === old(self).next_pages().update(
                order,
                self.next_page(order) as usize,
            ),
            self.free_page_counts() === old(self).free_page_counts().update(
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
        assert(self.next_pages() =~= old(self).next_pages().update(
            order,
            self.next_page(order) as usize,
        ));
        assert(self.free_page_counts() =~= old(self).free_page_counts().update(
            order,
            (old(self).free_page_counts()[order] - 1) as nat,
        ));
        perm
    }

    proof fn tracked_push(tracked &mut self, order: usize, pfn: usize, tracked perm: RawPerm)
        requires
            0 <= order < old(self).next.len(),
            old(self).wf_perms(),
            old(self).valid_pfn_order(pfn, order),
            perm.wf_vaddr_order(old(self).pfn_to_virt[pfn as int].vaddr, order as usize),
            pfn > 0,
        ensures
            self.wf_perms(),
            self.next[order as int].last() == pfn,
            self.next[order as int] === old(self).next[order as int].push(pfn),
            self.next === old(self).next.update(order as int, self.next[order as int]),
            self.reserved === old(self).reserved,
            self.pfn_to_virt === old(self).pfn_to_virt,
            self.avail[(order as int, old(self).next[order as int].len() as int)] === perm,
            self.avail === old(self).avail.insert(
                (order as int, old(self).next[order as int].len() as int),
                perm,
            ),
    {
        reveal(MemoryRegionTracked::wf_perms);
        let order = order as int;
        let idx = self.next[order].len() as int;
        self.avail.tracked_insert((order, idx), perm);
        self.next = self.next.update(order, self.next[order].push(pfn));
        assert(self.wf_item_perm(order, idx));
        assert forall|o, i|
            0 <= o < N && 0 <= i < self.next[o].len() implies #[trigger] self.wf_item_perm(
            o,
            i,
        ) by {
            if i < old(self).next[o].len() {
                assert(old(self).wf_item_perm(o, i))
            } else {
                assert(o == order);
                assert(i == idx);
            }
        }
    }
}

impl<VAddr: SpecVAddrImpl, const N: usize> MemoryRegionTracked<VAddr, N> {
    pub closed spec fn spec_page_info_addr(&self, pfn: int) -> VAddr {
        self.pfn_to_virt[pfn].info_vaddr
    }

    pub closed spec fn pfn_not_available(&self, pfn: usize, order: usize) -> bool {
        forall|o: int, i: int|
            0 <= o < MAX_ORDER && 0 <= i < self.next[o].len() ==> (self.next[o][i] + (1usize << (
            o as usize)) <= pfn || pfn + (1usize << order) <= self.next[o][i])
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
        //&&& reserved.dom() =~= set_int_range(0, page_count as int)

    }

    #[verifier(inline)]
    spec fn spec_page_storage_type(&self, pfn: int) -> Option<PageStorageType> {
        spec_page_storage_type(self.reserved[pfn])
    }

    #[verifier(inline)]
    spec fn spec_page_info(&self, pfn: int) -> Option<PageInfo> {
        spec_page_info(self.reserved[pfn])
    }

    #[verifier(inline)]
    spec fn get_free_info(&self, pfn: int) -> Option<FreeInfo> {
        spec_free_info(self.reserved[pfn])
    }

    pub closed spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        let n = 1usize << order;
        &&& 0 < pfn < self.page_count()
        &&& pfn + n <= self.page_count()
        &&& pfn % n == 0
        &&& order < MAX_ORDER
    }

    pub closed spec fn wf_item_perm(&self, order: int, i: int) -> bool {
        let pfn = self.next[order][i] as int;
        let perm = self.avail[(order, i)];
        let vaddr = self.pfn_to_virt[pfn].vaddr;
        &&& pfn > 0
        &&& self.valid_pfn_order(pfn as usize, order as usize)
        &&& perm.wf_vaddr_order(vaddr, order as usize)
    }

    pub closed spec fn wf_item(&self, order: int, i: int) -> bool {
        let next = self.next[order];
        let pfn = next[i] as int;
        let next_pfn = if i > 0 {
            next[i - 1]
        } else {
            0
        };
        &&& self.wf_item_perm(order, i)
        &&& self.marked_free(pfn, order as usize, next_pfn)
    }

    #[verifier(inline)]
    spec fn wf_next(&self, order: int) -> bool {
        let i = self.next[order].len() - 1;
        &&& self.wf_item(order, i)
    }

    spec fn spec_page_count(&self) -> int {
        spec_page_count(self.next, N)
    }

    spec fn wf_reserved(&self) -> bool {
        let reserved = self.reserved;
        let page_count = self.page_count();
        &&& forall|pfn: int|
            #![trigger reserved[pfn]]
            0 <= pfn < page_count ==> (reserved[pfn].addr() == self.spec_page_info_addr(
                pfn,
            ).spec_int_addr().unwrap() && self.spec_page_info(pfn).is_some())
        &&& reserved.dom() === set_int_range(0, page_count as int)
    }

    spec fn wf_info(&self) -> bool {
        let next = self.next;
        &&& forall|order, i| 0 <= order < N && 0 <= i < next[order].len() ==> self.wf_item(order, i)
    }

    #[verifier(opaque)]
    spec fn wf_perms(&self) -> bool {
        let next = self.next;
        &&& next.len() == N
        &&& self.avail.dom() =~= Set::new(
            |k: (int, int)| 0 <= k.0 < N && 0 <= k.1 < self.next[k.0].len(),
        )
        &&& forall|order, i|
            0 <= order < N && 0 <= i < next[order].len() ==> #[trigger] self.wf_item_perm(order, i)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_dom()
        &&& self.wf_info()
        &&& self.wf_reserved()
    }

    spec fn marked_free(&self, pfn: int, order: usize, next_pfn: usize) -> bool {
        let n = 1usize << order;
        let pi = self.spec_page_info(pfn);
        &&& pi === Some(PageInfo::Free(FreeInfo { next_page: next_pfn, order }))
        &&& forall|i|
            #![trigger self.spec_page_info(i)]
            pfn < i < pfn + n ==> self.spec_page_info(i) == Some(
                PageInfo::Compound(CompoundInfo { order }),
            )
    }
}

impl MemoryRegion {
    pub closed spec fn view(&self) -> MemoryRegionTracked<VirtAddr, MAX_ORDER> {
        self.perms@
    }

    pub closed spec fn map(&self) -> LinearMap {
        LinearMap {
            start_virt: self.start_virt,
            start_phys: self.start_phys@ as int,
            size: (self.page_count * PAGE_SIZE) as nat,
        }
    }

    spec fn with_same_mapping(&self, new: &Self) -> bool {
        self.map() === new.map()
    }

    pub closed spec fn spec_get_pfn(&self, vaddr: VirtAddr) -> int {
        (self.map().get_paddr(vaddr) - self.start_phys@) / PAGE_SIZE as int
    }

    pub closed spec fn spec_map_try_get_virt(map: LinearMap, pfn: int) -> Option<VirtAddr> {
        let phy = map.start_phys + pfn * PAGE_SIZE;
        map.to_vaddr(phy)
    }

    pub open spec fn spec_try_get_virt(&self, pfn: int) -> Option<VirtAddr> {
        Self::spec_map_try_get_virt(self.map(), pfn)
    }

    pub closed spec fn spec_get_virt(&self, pfn: int) -> VirtAddr {
        self.spec_try_get_virt(pfn).unwrap()
    }

    proof fn lemma_get_virt(&self, pfn: int) -> (ret: VirtAddr)
        requires
            self.wf_params(),
            0 <= pfn < self@.page_count(),
        ensures
            self.spec_try_get_virt(pfn).is_some(),
            ret == self.spec_get_virt(pfn),
            ret.is_canonical(),
            ret.offset() == self.start_virt.offset() + (pfn * PAGE_SIZE),
    {
        broadcast use crate::types::lemma_page_size;

        reveal(<LinearMap as SpecMemMapTr>::to_vaddr);
        crate::address::lemma_vaddr_upper_mask();
        assert(self.start_virt.is_canonical());
        VirtAddr::lemma_wf((self.start_virt@ + (pfn * PAGE_SIZE)) as usize);
        self.spec_get_virt(pfn)
    }

    spec fn spec_map_page_info_addr(map: LinearMap, pfn: int) -> VirtAddr {
        let reserved_unit_size = size_of::<PageStorageType>();
        let start = map.start_virt;
        VirtAddr::from_spec((start@ + (pfn * reserved_unit_size)) as usize)
    }

    spec fn spec_page_info_addr(&self, pfn: int) -> VirtAddr {
        Self::spec_map_page_info_addr(self.map(), pfn)
    }

    spec fn wf_pfn_to_virt(&self) -> bool {
        let map = self.map();
        self@.pfn_to_virt === Seq::new(
            (map.size / PAGE_SIZE as nat),
            |pfn|
                VirtInfo {
                    vaddr: Self::spec_map_try_get_virt(map, pfn).unwrap(),
                    info_vaddr: Self::spec_map_page_info_addr(map, pfn),
                },
        )
    }

    #[verifier(inline)]
    spec fn wf_page_count(&self) -> bool {
        &&& self.start_virt.offset() + self.page_count * PAGE_SIZE
            <= crate::address::VADDR_RANGE_SIZE
        &&& self@.page_count() == self.page_count
    }

    spec fn wf_accounting(&self) -> bool {
        &&& forall|order|
            0 <= order < MAX_ORDER ==> #[trigger] self.free_pages[order] <= self.nr_pages[order]
        &&& forall|order|
            0 <= order < MAX_ORDER ==> #[trigger] self.nr_pages[order] * (1usize << order as usize)
                <= self.page_count
    }

    spec fn wf_accounting_strict(&self) -> bool {
        &&& forall|order| 0 <= order < MAX_ORDER ==> self.nr_pages[order] == self.free_pages[order]
    }

    // Basic invariant that should hold except in initialization stage
    pub closed spec fn wf_params(&self) -> bool {
        let perms = self@;
        &&& self.start_virt.is_canonical()
        &&& self.wf_pfn_to_virt()
        &&& self.wf_page_count()
        &&& self.wf_accounting()
    }

    pub closed spec fn wf_reserved(&self) -> bool {
        &&& self@.wf_reserved()
        &&& self.wf_params()
    }

    pub closed spec fn wf_free_pages(&self) -> bool {
        forall|order|
            0 <= order < MAX_ORDER ==> self@.next[order].len() == #[trigger] self.free_pages[order]
    }

    // Strict invariant that should hold at public interfaces.
    pub closed spec fn wf_mem_state(&self) -> bool {
        let perms = self@;
        &&& self.wf_params()
        &&& self.wf_free_pages()
        &&& perms.wf()
        &&& perms.next_pages() =~= self.next_page@
        &&& perms.wf_reserved()
    }

    pub closed spec fn wf_mem_stat_state(&self) -> bool {
        self.wf_mem_state() && self.wf_accounting_strict()
    }

    pub closed spec fn ensures_get_next_page(
        &self,
        new_self: &Self,
        order: usize,
        ret: Result<usize, AllocError>,
    ) -> bool {
        let tmp = self.tmp_perms@.to_seq();
        let new_tmp = new_self.tmp_perms@.to_seq();
        let vaddr = new_self.spec_get_virt(ret.unwrap() as int);
        let order = order as int;
        &&& self.wf_mem_state()
        &&& self.with_same_mapping(new_self)
        &&& ret.is_err() == (self.next_page[order] == 0)
        &&& ret.is_err() == (self.free_pages[order] == 0)
        &&& ret.is_err() ==> self === new_self
        &&& ret.is_ok() ==> {
            &&& new_tmp.last().wf_vaddr_order(vaddr, order as usize)
            &&& new_tmp === tmp.push(
                new_tmp.last(),
            )
            //&&& new_self.tmp_perms@.len() == self.tmp_perms@.len() + 1
            &&& ret.unwrap() == self.next_page[order]
            &&& new_self.valid_pfn_order(ret.unwrap(), order as usize)
            &&& new_self.free_pages@ === self.free_pages@.update(
                order,
                (self.free_pages[order] - 1) as usize,
            )
            &&& new_self.next_page@ === self.next_page@.update(order, new_self.next_page[order])
            &&& new_self.nr_pages === self.nr_pages
            &&& new_self@.pfn_not_available(ret.unwrap(), order as usize)
        }
    }

    pub closed spec fn ens_read_page_info(self, pfn: usize, ret: PageInfo) -> bool {
        &&& self@.spec_page_info(pfn as int).is_some()
        &&& self@.spec_page_info(pfn as int).unwrap() === ret
    }

    pub closed spec fn spec_alloc_fails(&self, order: int) -> bool {
        forall|i| #![trigger self.next_page[i]] order <= i < MAX_ORDER ==> self.next_page[i] == 0
    }

    #[verifier(inline)]
    pub open spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        self@.valid_pfn_order(pfn, order)
    }

    pub closed spec fn ens_refill_page_list(&self, new: Self, ret: bool, order: usize) -> bool {
        let new_free_perms = new@.next;
        // No available if no slot >= order
        let valid_order = (0 <= order < MAX_ORDER);
        if self.spec_alloc_fails(order as int) || !valid_order {
            &&& *self === new
            &&& !ret
        } else {
            &&& ret
            //&&& new@.next[order as int].len() > 0
            &&& new.free_pages[order as int] > 0
            &&& self.only_update_order_higher(new, order)
        }
    }

    pub closed spec fn req_split_page(&self, pfn: usize, order: usize) -> bool {
        let perm = self.tmp_perms@.last();
        let vaddr = self.spec_get_virt(pfn as int);
        let new_size = (1usize << (order - 1) as usize);
        &&& self.tmp_perms@.len() > 0
        &&& perm.wf_vaddr_order(vaddr, order as usize)
        &&& self.valid_pfn_order(pfn, order)
        &&& order >= 1
        &&& self.wf_mem_state()
        &&& self.nr_pages[order as int] > 0
        &&& (self.nr_pages[order - 1] + 2) * new_size <= self.page_count
        &&& self.free_pages[order - 1] + 2 <= usize::MAX
        &&& self.nr_pages[order - 1] + 2 <= usize::MAX
        &&& self@.pfn_not_available(pfn, order)
        &&& self.free_pages[order as int] == self.nr_pages[order as int] - 1
    }

    pub closed spec fn ens_split_page_ok(&self, new: &Self, pfn: usize, order: usize) -> bool {
        let free_perms = self@.next;
        let new_free_perms = new@.next;
        let tmp = self.tmp_perms@@;
        let new_tmp = new.tmp_perms@@;
        let rhs_pfn = (pfn + (1usize << order) / 2) as usize;
        let new_order = order - 1;
        let order = order as int;
        let newp = free_perms[new_order].push(rhs_pfn).push(pfn);
        &&& new_free_perms =~= free_perms.update(new_order, newp)
        &&& new_tmp =~= tmp.take(tmp.len() - 1)
        &&& self.with_same_mapping(new)
        &&& new.nr_pages@[new_order] == self.nr_pages[new_order] + 2
        &&& new.nr_pages@[order] == self.nr_pages[order] - 1
        &&& new.free_pages[new_order] == self.free_pages[new_order] + 2
        &&& new.nr_pages@ =~= self.nr_pages@.update(new_order, new.nr_pages[new_order]).update(
            order,
            new.nr_pages[order],
        )
        &&& new.free_pages@ =~= self.free_pages@.update(new_order, new.free_pages[new_order])
        &&& new.next_page@ =~= self.next_page@.update(order - 1, pfn)
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

    pub closed spec fn ens_mark_compound_page(
        &self,
        new: Self,
        pfn: usize,
        n: usize,
        order: usize,
    ) -> bool {
        let pfn = pfn as int;
        &&& self.only_update_reserved(new)
        &&& new@.reserved =~~= self@.reserved.union_prefer_right(
            Map::new(|i| pfn < i < pfn + n, |i| new@.reserved[i]),
        )
        &&& new@.reserved[pfn] === self@.reserved[pfn]
        &&& new.wf_reserved()
        &&& forall|i|
            #![trigger new@.reserved[i]]
            pfn < i < pfn + n ==> new@.spec_page_info(i) == Some(
                PageInfo::Compound(CompoundInfo { order }),
            )
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
        let expected_perm = MemoryRegionTracked { reserved: new@.reserved, ..self@ };
        let expected_self = MemoryRegion { perms: new.perms, ..*self };
        &&& expected_self === new
        &&& expected_perm === new@
    }

    spec fn only_update_order_higher(&self, new: Self, order: usize) -> bool {
        &&& self.with_same_mapping(&new)
        &&& forall|i: int|
            0 <= i < order ==> {
                &&& self.free_pages[i] == new.free_pages[i]
                &&& self.nr_pages[i] == new.nr_pages[i]
                &&& self.next_page[i] == new.next_page[i]
            }
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
        let changes = Map::new(|i| pfn <= i < pfn + n, |i| new@.reserved[i]);
        &&& self.only_update_reserved(new)
        &&& new@.reserved =~~= self@.reserved.union_prefer_right(changes)
        &&& new@.marked_free(pfn, order, next_pfn)
        &&& new.wf_reserved()
    }

    spec fn req_compound_neighbor(&self, pfn: usize, order: usize) -> bool {
        self.valid_pfn_order(pfn, order)
    }

    spec fn ens_compound_neighbor_ok(&self, pfn: usize, order: usize, ret_pfn: usize) -> bool {
        let new_order = (order + 1) as usize;
        let n = 1usize << order;
        if ret_pfn == pfn - n {
            self.valid_pfn_order(ret_pfn, new_order)
        } else if ret_pfn == pfn + n {
            self.valid_pfn_order(pfn, new_order)
        } else {
            false
        }
    }
}

} // verus!
