// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// This module defines specification helper functions to verify the correct use of memory.
//
// Trusted Assumptions:
// - Upon entry to the SVSM (Secure Virtual Machine Monitor) kernel, there exists a set of unique
//   memory permissions that are predefined and trusted.
// - Memory permissions are considered unforgeable, ensuring their integrity during execution.
// - LinearMap is correct and is used for all memory managed by allocator.
//
// Note:
// - No additional specification needs to be trusted here; all assumptions are established
//   within the trusted context of the kernel entry.
use crate::types::lemma_page_size;
use crate::utils::util::spec_align_up;
use verify_external::convert::FromSpec;
use verify_external::hw_spec::{SpecMemMapTr, SpecVAddrImpl};
use verify_proof::bits::{
    lemma_bit_usize_and_mask_is_mod, lemma_bit_usize_shl_values, lemma_bit_usize_xor_neighbor,
};
use verify_proof::nonlinear::lemma_modulus_add_sub_m;
use verify_proof::set::{lemma_int_range_disjoint, seq_sets_to_set, spec_int_range_disjoint};
use verify_proof::tseq::TrackedSeq;
use verify_proof::frac_ptr::FracTypedPerm;
use vstd::arithmetic::mul::group_mul_properties;
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_ordering};
use vstd::raw_ptr::PointsToRaw;
use vstd::raw_ptr::{IsExposed, Provenance};
use vstd::set_lib::set_int_range;

verus! {

use crate::mm::address_space::LinearMap;

broadcast group alloc_broadcast_group {
    //crate::address::group_addr_proofs,
    lemma_bit_usize_shl_values,
    lemma_page_size,
    set_len_group,
}

broadcast use alloc_broadcast_group;

include!("alloc_proof.verus.rs");

include!("alloc_types.verus.rs");

pub type RawPerm = PointsToRaw;

pub const MAX_PAGE_COUNT: usize = usize::MAX >> 12;

#[verifier(inline)]
spec fn order_set(start: usize, order: usize) -> Set<int> {
    set_int_range(start as int, start as int + (1usize << order))
}

spec fn order_disjoint(start1: usize, order1: usize, start2: usize, order2: usize) -> bool {
    let end1 = start1 + (1usize << order1);
    let end2 = start2 + (1usize << order2);
    //(end1 <= start2 || end2 <= start1)
    spec_int_range_disjoint(start1 as int, end1, start2 as int, end2)
}

pub uninterp spec fn allocator_provenance() -> Provenance;

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
        &&& pfn < map.size / PAGE_SIZE as nat
        &&& self.wf_vaddr_order(vaddr.unwrap(), order)
    }
}

spec fn spec_page_storage_type(perm: FracTypedPerm<PageStorageType>) -> Option<PageStorageType> {
    if perm.is_init() {
        Some(perm.value())
    } else {
        None
    }
}

spec fn spec_page_info(perm: FracTypedPerm<PageStorageType>) -> Option<PageInfo> {
    let mem = spec_page_storage_type(perm);
    if mem.is_some() {
        PageInfo::spec_decode(mem.unwrap())
    } else {
        None
    }
}

spec fn spec_free_info(perm: FracTypedPerm<PageStorageType>) -> Option<FreeInfo> {
    let p_info = spec_page_info(perm);
    if p_info.is_some() {
        let pi = p_info.unwrap();
        pi.get_free()
    } else {
        None
    }
}

ghost struct VirtInfo<VAddr> {
    vaddr: VAddr,
    info_vaddr: VAddr,
}

tracked struct MemoryRegionTracked<VAddr: SpecVAddrImpl, const N: usize> {
    tracked avail: Map<(int, int), RawPerm>,  //(order, idx) -> perm
    ghost next: Seq<Seq<usize>>,  // order -> next page list
    tracked reserved: Map<int, FracTypedPerm<PageStorageType>>,  //pfn -> pginfo
    ghost pfn_to_virt: Seq<VirtInfo<VAddr>>,  // pfn -> virt address
    tracked is_exposed: IsExposed,
}

ghost struct FreePerms<VAddr: SpecVAddrImpl, const N: usize> {
    avail: Map<(int, int), RawPerm>,  //(order, idx) -> perm
    next: Seq<Seq<usize>>,  // order -> next page list
    pfn_to_virt: Seq<VirtInfo<VAddr>>,  // pfn -> virt address
    page_count: PageCountParam<N>,
}

impl<VAddr: SpecVAddrImpl, const N: usize> FreePerms<VAddr, N> {
    spec fn wf_at(&self, order: int, i: int) -> bool {
        let pfn = self.next[order][i] as int;
        let perm = self.avail[(order, i)];
        let vaddr = self.pfn_to_virt[pfn].vaddr;
        &&& pfn >= self.page_count.reserved_pfn_count()
        &&& self.page_count.valid_pfn_order(pfn as usize, order as usize)
        &&& perm.wf_vaddr_order(vaddr, order as usize)
    }

    spec fn wf(&self) -> bool {
        &&& forall|order, i|
            0 <= order < N && 0 <= i < self.next[order].len() ==> #[trigger] self.wf_at(order, i)
    }
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

        let x = self.page_count * 8 as int;
        assert(PAGE_SIZE == 0x1000);
        let count = spec_align_up(x, PAGE_SIZE as int);
        verify_proof::nonlinear::lemma_align_up_properties(x, PAGE_SIZE as int, count);
        assert(self.page_count * 8 / 0x1000 == self.page_count / 512);
    }
}

impl<const N: usize> ReservedPerms<N> {
    spec fn page_count(&self) -> usize {
        self.page_count.page_count
    }

    spec fn reserved_count(&self) -> nat {
        self.page_count.reserved_pfn_count()
    }

    #[verifier(inline)]
    spec fn spec_page_info(&self, pfn: usize) -> Option<PageInfo> {
        spec_page_info(self.reserved[pfn as int])
    }

    spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        self.page_count.valid_pfn_order(pfn, order)
    }

    #[verifier(inline)]
    spec fn pfn_filter(&self, order: usize) -> spec_fn(int) -> bool {
        |pfn: int| self.spec_page_info(pfn as usize).unwrap().get_order() == order
    }

    spec fn pfn_dom(&self, order: usize) -> Set<int> {
        set_int_range(0, self.page_count() as int).filter(self.pfn_filter(order))
    }

    spec fn marked_compound(&self, pfn: usize, order: usize) -> bool {
        let n = 1usize << order;
        let pi = self.spec_page_info(pfn);
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
        &&& pi.unwrap().get_order() == order
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
        &&& pi.unwrap().get_order() == order
        &&& pi.unwrap().get_free().is_some()
        &&& self.marked_compound(pfn, order)
    }

    spec fn marked_allocated(&self, pfn: usize, order: usize) -> bool {
        let pi = self.spec_page_info(pfn);
        &&& pi.unwrap().get_order() == order
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
            #![trigger self.reserved[pfn as int]]
            0 <= pfn < self.reserved_count() ==> #[trigger] self.spec_page_info(pfn) === Some(
                PageInfo::Reserved(ReservedInfo),
            )
    }

    spec fn wf_dom(&self) -> bool {
        &&& self.reserved.dom() === set_int_range(0, self.page_count() as int)
        &&& forall|pfn: usize|
            0 <= pfn < self.page_count() ==> #[trigger] (self.spec_page_info(pfn).is_some())
    }

    spec fn wf_ptr<VAddr: SpecVAddrImpl>(&self, pfn_to_virt: Seq<VirtInfo<VAddr>>) -> bool {
        forall|pfn: usize|
            0 <= pfn < self.page_count() ==> (#[trigger] self.reserved[pfn as int]).addr()
                == pfn_to_virt[pfn as int].info_vaddr.spec_int_addr().unwrap()
    }

    spec fn wf(&self) -> bool {
        &&& self.wf_dom()
        &&& self.wf_reserved_basic()
        &&& self.wf_page_info()
        &&& self.page_count() <= MAX_PAGE_COUNT
    }

    spec fn ens_allocate_pfn(&self, new: Self, pfn: usize, prev_pfn: usize, order: usize) -> bool {
        &&& new.marked_order(pfn, order)
        &&& new.reserved =~= self.reserved.union_prefer_right(
            Map::new(|k| k == pfn || k == prev_pfn, |k| new.reserved[k]),
        )
        &&& prev_pfn > 0 ==> new.marked_free_order(prev_pfn, order)
    }
}

impl PageInfo {
    spec fn get_order(&self) -> usize {
        match *self {
            PageInfo::Compound(CompoundInfo { order }) => order,
            PageInfo::Allocated(AllocatedInfo { order }) => order,
            PageInfo::Free(FreeInfo { order, .. }) => order,
            _ => 0,
        }
    }

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

spec fn seq_range_to_sets(next: Seq<usize>, size: nat) -> Seq<Set<int>> {
    next.map_values(|pfn: usize| set_int_range(pfn as int, pfn + size))
}

#[verifier(inline)]
spec fn find_pfn_head(pfn: usize, order: usize) -> usize {
    crate::utils::util::spec_align_down(pfn as int, (1usize << order) as int) as usize
}

impl<VAddr: SpecVAddrImpl, const N: usize> MemoryRegionTracked<VAddr, N> {
    #[verifier(inline)]
    spec fn pg_params(&self) -> PageCountParam<N> {
        PageCountParam { page_count: self.page_count() as usize }
    }

    #[verifier(inline)]
    spec fn reserved(&self) -> ReservedPerms<N> {
        ReservedPerms { page_count: self.pg_params(), reserved: self.reserved }
    }

    spec fn free_perms(&self) -> FreePerms<VAddr, N> {
        FreePerms {
            page_count: self.pg_params(),
            avail: self.avail,
            next: self.next,
            pfn_to_virt: self.pfn_to_virt,
        }
    }

    spec fn free_pfn_len(&self, order: int) -> nat {
        self.next[order].len()
    }

    spec fn free_pfn_dom_seq(&self, order: int) -> Seq<Set<int>> {
        Seq::new(self.free_pfn_len(order), |idx| self.free_dom_at(order as usize, idx))
    }

    spec fn free_pfn_dom(&self, order: int) -> Set<int> {
        seq_sets_to_set(self.free_pfn_dom_seq(order))
    }

    spec fn free_dom(&self) -> Set<int> {
        self.full_pfn_dom().filter(
            |pfn: int|
                exists|o: usize, idx: int|
                    #![trigger self.next[o as int][idx]]
                    self.free_dom_at(o, idx).contains(pfn) && 0 <= idx < self.next[o as int].len()
                        && 0 <= o < N,
        )
    }

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

    #[verifier::spinoff_prover]
    proof fn lemma_free_order_at(&self, order: usize, idx: int)
        requires
            0 <= idx < self.next[order as int].len(),
            0 <= order < N,
            self.wf(),
        ensures
            self.free_dom_at(order, idx).subset_of(self.free_order_dom(order)),
            self.free_dom_at(order, idx).subset_of(self.full_pfn_dom()),
    {
        let s1 = self.free_order_dom(order);
        let s2 = self.free_dom_at(order, idx);
        assert forall|e| s2.contains(e) implies s1.contains(e) by {
            assert(self.free_dom_at(order, idx).contains(e));
            assert(self.wf_at(order as int, idx));
            assert(self.full_pfn_dom().contains(e));
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_free_order_dom_rec(&self, order: usize, len: nat)
        requires
            self.wf(),
            0 <= order < N,
            len <= self.next[order as int].len(),
        ensures
            self.free_order_dom_rec(order, len).len() == len * (1usize << order),
        decreases len,
    {
        let size = 1usize << order;
        if len > 0 {
            let idx = len - 1;
            let next_list = self.next[order as int][idx];
            let s = self.free_order_dom_rec(order, len);
            let s1 = self.free_order_dom_rec(order, idx as nat);
            let s2 = self.free_dom_at(order, idx);
            assert forall|e| s1.contains(e) implies (s.contains(e) && !s2.contains(e)) by {
                let i = choose|i: int|
                    #![trigger self.next[order as int][i]]
                    0 <= i < idx && self.free_dom_at(order, i).contains(e);
                self.lemma_unique_pfn(order as int, i, order as int, idx);
            }
            self.lemma_free_order_at(order, idx);
            self.lemma_free_order_dom_rec(order, idx as nat);
            assert(s =~= s1 + s2);
            assert(s1.disjoint(s2));
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int, idx as int, 1);
        } else {
            assert(0 * (1usize << order) == 0);
            assert(self.free_order_dom_rec(order, 0).is_empty());
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_free_order_dom_subset(&self, order: usize)
        requires
            self.wf(),
            0 <= order < N <= 64,
        ensures
            self.free_order_dom(order).subset_of(self.free_dom()),
    {
        assert(self.free_order_dom(order).subset_of(self.free_dom()));
    }

    #[verifier::spinoff_prover]
    proof fn lemma_free_order_dom(&self, order: usize)
        requires
            self.wf(),
            0 <= order < N <= 64,
        ensures
            self.free_order_dom(order).len() == self.next[order as int].len() * (1usize << order),
            self.free_order_dom(order).len() >= self.next[order as int].len(),
            self.free_order_dom(order).len() <= self.free_dom().len(),
    {
        broadcast use set_len_group, lemma_mul_ordering;

        assert(1usize << order >= 1) by {
            broadcast use lemma_bit_usize_shl_values;

        }
        self.lemma_free_order_dom_subset(order);
        self.lemma_free_order_dom_rec(order, self.next[order as int].len());
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
    spec fn spec_page_info_addr(&self, pfn: int) -> VAddr {
        self.pfn_to_virt[pfn].info_vaddr
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

    #[verifier(inline)]
    spec fn next_pages(&self) -> Seq<usize> {
        Seq::new(N as nat, |i| self.next_page(i) as usize)
    }

    #[verifier(inline)]
    spec fn free_page_counts(&self) -> Seq<nat> {
        Seq::new(N as nat, |i| self.next[i].len())
    }

    spec fn next_pages_after_remove(&self, order: int) -> Seq<usize> {
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

    spec fn wf_dom(&self) -> bool {
        let avail = self.avail;
        let next = self.next;
        &&& self.page_count() <= MAX_PAGE_COUNT
        &&& next.len() == N
        &&& self.is_exposed@ == allocator_provenance()
        &&& avail.dom() =~= Set::new(
            |k: (int, int)| 0 <= k.0 < N && 0 <= k.1 < self.next[k.0].len(),
        )
    }

    #[verifier(inline)]
    spec fn spec_page_storage_type(&self, pfn: int) -> Option<PageStorageType> {
        spec_page_storage_type(self.reserved[pfn])
    }

    #[verifier(inline)]
    spec fn spec_page_info(&self, pfn: int) -> Option<PageInfo> {
        self.reserved().spec_page_info(pfn as usize)
    }

    #[verifier(inline)]
    spec fn get_free_info(&self, pfn: int) -> Option<FreeInfo> {
        spec_free_info(self.reserved[pfn])
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
    }

    #[verifier(inline)]
    spec fn wf_next(&self, order: int) -> bool {
        let i = self.next[order].len() - 1;
        i >= 0 ==> self.wf_at(order, i)
    }

    spec fn spec_page_count(&self) -> int {
        spec_page_count(self.next, N)
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
        &&& self.reserved().wf_ptr(self.pfn_to_virt)
        &&& self.reserved().wf_reserved_basic()
    }

    spec fn wf_page_info_at(&self, pfn: usize) -> bool {
        self.reserved().wf_page_info_at(pfn)
    }

    spec fn wf_info_content(&self) -> bool {
        self.reserved().wf_page_info()
    }

    spec fn no_duplicates(&self) -> bool {
        &&& forall|order| 0 <= order < N ==> (#[trigger] self.next[order]).no_duplicates()
    }

    spec fn wf_info(&self) -> bool {
        let next = self.next;
        &&& forall|order, i| 0 <= order < N && 0 <= i < next[order].len() ==> #[trigger]self.wf_at(order, i)
        &&& self.wf_info_content()
        &&& self.no_duplicates()
    }

    spec fn wf_perms(&self) -> bool {
        let next = self.next;
        &&& self.wf_dom()
        &&& self.free_perms().wf()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_dom()
        &&& self.wf_info()
        &&& self.wf_reserved()
    }

    #[verifier(inline)]
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

spec fn sum_nr_pages(nr_pages: Seq<usize>) -> int
    decreases nr_pages.len(),
{
    let order = nr_pages.len() - 1;
    if order >= 0 {
        sum_nr_pages(nr_pages.remove(order)) + nr_pages.last() * (1usize << order)
    } else {
        0
    }
}

impl MemoryRegion {
    pub closed spec fn view(&self) -> MemoryRegionTracked<VirtAddr, MAX_ORDER> {
        self.perms@
    }

    // Strict invariant that should hold at public interfaces.
    pub closed spec fn wf(&self) -> bool {
        let perms = self@;
        &&& self.wf_params()
        &&& self.wf_nr_pages()
        &&& self.wf_free_pages()
        &&& perms.wf()
        &&& perms.next_pages() =~= self.next_page@
        &&& perms.wf_reserved()
    }

    spec fn map(&self) -> LinearMap {
        LinearMap {
            start_virt: self.start_virt,
            start_phys: self.start_phys@ as int,
            size: (self.page_count * PAGE_SIZE) as nat,
        }
    }

    spec fn with_same_mapping(&self, new: &Self) -> bool {
        self.map() === new.map()
    }

    spec fn spec_get_pfn(&self, vaddr: VirtAddr) -> Option<usize> {
        if self.map().to_paddr(vaddr).is_some() {
            Some(((vaddr.offset() - self.start_virt.offset()) / PAGE_SIZE as int) as usize)
        } else {
            None
        }
    }

    spec fn spec_try_get_virt(&self, pfn: int) -> Option<VirtAddr> {
        self.map().try_get_virt(pfn as usize)
    }

    spec fn spec_get_virt(&self, pfn: int) -> VirtAddr {
        self.spec_try_get_virt(pfn).unwrap()
    }

    broadcast proof fn lemma_get_pfn_get_virt(&self, vaddr: VirtAddr)
        requires
            self.wf_params(),
            vaddr.is_canonical(),
            vaddr@ % 0x1000 == 0,
        ensures
            (#[trigger] self.spec_get_pfn(vaddr)).is_some() ==> self.spec_get_virt(
                self.spec_get_pfn(vaddr).unwrap() as int,
            ) == vaddr,
    {
        broadcast use lemma_page_size;

        assert(self.start_virt@ % 0x1000 == 0);
        assert(vaddr.offset() - self.start_virt.offset() == (vaddr.offset()
            - self.start_virt.offset()) / 0x1000 * 0x1000) by {
            vaddr.property_canonical();
            self.start_virt.property_canonical();
            assert(self.start_virt.offset() % 0x1000 == 0);
            broadcast use verify_proof::bits::lemma_bit_usize_not_is_sub;

        }
        self.map().proof_one_to_one_mapping_vaddr(vaddr);
    }

    spec fn spec_map_page_info_addr(map: LinearMap, pfn: int) -> VirtAddr {
        let reserved_unit_size = size_of::<PageStorageType>();
        let start = map.start_virt;
        VirtAddr::from_spec((start@ + (pfn * reserved_unit_size)) as usize)
    }

    spec fn spec_page_info_addr(&self, pfn: int) -> VirtAddr {
        Self::spec_map_page_info_addr(self.map(), pfn)
    }

    spec fn wf_nr_pages(&self) -> bool {
        /*&&& forall|order|
            0 <= order < MAX_ORDER ==> #[trigger] self.free_pages[order] <= self.nr_pages[order]*/
        &&& forall|order|
            0 <= order < MAX_ORDER ==> (#[trigger] self.nr_pages[order]) * (1usize << order)
                == self@.reserved().pfn_dom(order as usize).len()
    }

    #[verifier::spinoff_prover]
    proof fn lemma_nr_page_add(&self, new: &Self, n: int, order: usize)
        requires
            self.wf_nr_pages(),
            0 <= order < MAX_ORDER,
            new.nr_pages[order as int] == self.nr_pages[order as int] + n,
            new@.reserved().pfn_dom(order).len() == self@.reserved().pfn_dom(order).len() + n * (
            1usize << order),
        ensures
            new.nr_pages[order as int] * (1usize << order) == new@.reserved().pfn_dom(order).len(),
    {
        broadcast use lemma_bit_usize_shl_values;

        let size = (1usize << order);
        assert((self.nr_pages[order as int] + n) * size == self.nr_pages[order as int] * size + n
            * size) by {
            broadcast use group_mul_properties;

        }
    }

    #[verifier::spinoff_prover]
    broadcast proof fn lemma_accounting_basic(&self, order: usize)
        requires
            self.wf_nr_pages(),
            self.wf_params(),
            self@.reserved().wf(),
            0 <= order < MAX_ORDER,
        ensures
            (#[trigger] self.nr_pages[order as int]) * (1usize << order) <= self.page_count,
            self.nr_pages[order as int] <= self.page_count,
            self.nr_pages[order as int] == self@.reserved().pfn_dom(order).len() / (1usize
                << order) as nat,
    {
        self.lemma_accounting(order)
    }

    #[verifier::spinoff_prover]
    broadcast proof fn lemma_accounting(&self, order: usize)
        requires
            self.wf_nr_pages(),
            self.wf_params(),
            self@.reserved().wf(),
            0 <= order < MAX_ORDER,
        ensures
            (#[trigger] self.nr_pages[order as int]) * (1usize << order) <= self.page_count,
            self.nr_pages[order as int] <= self.page_count,
            self.nr_pages[order as int] == self@.reserved().pfn_dom(order).len() / (1usize
                << order) as nat,
            (exists|pfn: usize| #[trigger]self@.marked_order(pfn, order)) ==> self.nr_pages[order as int]
                >= 1,
            (exists|pfn: usize, pfn2: usize|
                pfn2 != pfn && #[trigger]self@.marked_order(pfn, order) && #[trigger]self@.marked_order(pfn2, order))
                ==> self.nr_pages[order as int] >= 1,
            (exists|order2: usize|
                order2 != order && 0 < order2 < MAX_ORDER && self.nr_pages[order2 as int] > 0)
                ==> self.nr_pages[order as int] <= self.page_count - 2,
    {
        broadcast use lemma_bit_usize_shl_values, lemma_mul_inequality, lemma_mul_ordering;

        let count = self.nr_pages[order as int];
        let size = (1usize << order) as int;
        assert(count <= count * size);
        assert(count * size / size == count) by (nonlinear_arith)
            requires
                size != 0,
        ;
        //assert(self.nr_pages[order] * (1usize << order) == self@.reserved().pfn_dom(order as usize).len());
        self@.reserved().lemma_pfn_dom(order as usize);
        if exists|pfn: usize| #[trigger]self@.marked_order(pfn, order) {
            let pfn = choose|pfn: usize| #[trigger]self@.marked_order(pfn, order);
            self@.reserved().lemma_pfn_dom_len_with_one(pfn, order);
        }
        if exists|pfn: usize, pfn2: usize|
            pfn2 != pfn && #[trigger]self@.marked_order(pfn, order) && #[trigger]self@.marked_order(pfn2, order) {
            let (pfn1, pfn2) = choose|pfn: usize, pfn2: usize|
                pfn2 != pfn && #[trigger]self@.marked_order(pfn, order) && #[trigger]self@.marked_order(pfn2, order);
            self@.reserved().lemma_pfn_dom_len_with_two(pfn1, pfn2, order);
        }
        if exists|order2: usize|
            order2 != order && 0 < order2 < MAX_ORDER && self.nr_pages[order2 as int] > 0 {
            let order2 = choose|order2: usize|
                order2 != order && 0 < order2 < MAX_ORDER && self.nr_pages[order2 as int] > 0;
            self@.reserved().lemma_pfn_dom_pair(order, order2);
            assert((1usize << order2) >= 2);
        }
    }

    spec fn wf_pfn_to_virt(&self) -> bool {
        let map = self.map();
        self@.pfn_to_virt === Seq::new(
            (map.size / PAGE_SIZE as nat),
            |pfn|
                VirtInfo {
                    vaddr: map.try_get_virt(pfn as usize).unwrap(),
                    info_vaddr: Self::spec_map_page_info_addr(map, pfn),
                },
        )
    }

    // Basic invariant that should hold except in initialization stage
    spec fn wf_params(&self) -> bool {
        let perms = self@;
        &&& self.map().wf()
        &&& self.wf_pfn_to_virt()
        &&& self@.page_count() == self.page_count
        &&& self@.is_exposed@ == allocator_provenance()
        &&& self.start_virt@ % PAGE_SIZE == 0
        &&& self.page_count <= MAX_PAGE_COUNT
    }

    spec fn wf_reserved(&self) -> bool {
        &&& self@.wf_reserved()
        &&& self.wf_params()
    }

    spec fn wf_free_pages(&self) -> bool {
        &&& forall|order|
            0 <= order < MAX_ORDER ==> self@.next[order].len() == #[trigger] self.free_pages[order]
    }

    spec fn ens_get_next_page(
        &self,
        new_self: &Self,
        order: usize,
        ret: Result<usize, AllocError>,
    ) -> bool {
        let tmp = self.tmp_perms@.to_seq();
        let new_tmp = new_self.tmp_perms@.to_seq();
        let vaddr = new_self.spec_get_virt(ret.unwrap() as int);
        let order = order as int;
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
            &&& new_self@.next[order] === self@.next[order].remove(self@.next[order].len() - 1)
            &&& new_self@.next === self@.next.update(order, new_self@.next[order])
            &&& self@.inv_remove_pfn(new_self@)
            &&& new_self.nr_pages === self.nr_pages
            &&& new_self@.pfn_range_is_allocated(ret.unwrap(), order as usize)
            &&& new_self@.reserved === self@.reserved
        }
    }

    spec fn ens_read_page_info(self, pfn: usize, ret: PageInfo) -> bool {
        &&& self@.spec_page_info(pfn as int).is_some()
        &&& self@.spec_page_info(pfn as int).unwrap() === ret
        &&& pfn < self.page_count
    }

    spec fn spec_alloc_fails(&self, order: int) -> bool {
        forall|i| #![trigger self.next_page[i]] order <= i < MAX_ORDER ==> self.next_page[i] == 0
    }

    #[verifier(inline)]
    spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        self@.valid_pfn_order(pfn, order)
    }

    spec fn ens_refill_page_list(&self, new: Self, ret: bool, order: usize) -> bool {
        // No available if no slot >= order
        let valid_order = (0 <= order < MAX_ORDER);
        if self.spec_alloc_fails(order as int) || !valid_order {
            &&& *self === new
            &&& !ret
        } else {
            &&& new.wf()
            &&& ret
            &&& new.free_pages[order as int] > 0
            &&& self.only_update_order_higher(new, order)
        }
    }

    spec fn req_split_page(&self, pfn: usize, order: usize) -> bool {
        let perm = self.tmp_perms@.last();
        let vaddr = self.spec_get_virt(pfn as int);
        let new_size = (1usize << (order - 1) as usize);
        &&& self.tmp_perms@.len() > 0
        &&& perm.wf_vaddr_order(vaddr, order as usize)
        &&& self.valid_pfn_order(pfn, order)
        &&& order >= 1
        &&& self.wf()
        &&& self.free_pages[order - 1] + 2 <= usize::MAX
        &&& self@.pfn_range_is_allocated(pfn, order)
        &&& self@.marked_order(pfn, order)
    }

    spec fn ens_split_page_ok(&self, new: &Self, pfn: usize, order: usize) -> bool {
        let tmp = self.tmp_perms@@;
        let new_tmp = new.tmp_perms@@;
        let rhs_pfn = (pfn + (1usize << order) / 2) as usize;
        let new_order = order - 1;
        let order = order as int;
        let newp = self@.next[new_order].push(rhs_pfn).push(pfn);
        &&& new@.next =~= self@.next.update(new_order, newp)
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

    spec fn req_write_page_info(&self, pfn: usize, pi: PageInfo) -> bool {
        &&& self@.wf_reserved()
        &&& self.wf_params()
        &&& pfn < self@.reserved_pfn_count() ==> pi === PageInfo::Reserved(ReservedInfo)
        &&& pfn < self@.page_count()
    }

    spec fn ens_write_page_info(&self, new: Self, pfn: usize, pi: PageInfo) -> bool {
        let new_order = pi.get_order();
        let old_order = self@.spec_page_info(pfn as int).unwrap().get_order();
        &&& self.only_update_reserved(new)
        &&& new@.reserved =~~= self@.reserved.insert(pfn as int, new@.reserved[pfn as int])
        &&& new@.spec_page_info(pfn as int) === Some(pi)
        &&& (new_order == old_order) ==> (forall|order|
            0 <= order < MAX_ORDER ==> #[trigger]self@.reserved().pfn_dom(order) =~= new@.reserved().pfn_dom(
                order,
            ))
        &&& old_order != new_order ==> forall|order|
            0 <= order < MAX_ORDER && order != old_order && order != new_order
                ==> #[trigger]self@.reserved().pfn_dom(order) =~= new@.reserved().pfn_dom(order)
        &&& old_order != new_order ==> {
            &&& new@.reserved().pfn_dom(old_order) =~= self@.reserved().pfn_dom(old_order).remove(
                pfn as int,
            )
            &&& new@.reserved().pfn_dom(new_order) =~= self@.reserved().pfn_dom(new_order).insert(
                pfn as int,
            )
        }
        &&& new@.wf_reserved()
    }

    spec fn req_mark_compound_page(&self, pfn: usize, order: usize) -> bool {
        &&& self.wf_reserved()
        &&& self.valid_pfn_order(pfn, order)
    }

    spec fn ens_mark_compound_page(&self, new: Self, pfn: usize, n: usize, order: usize) -> bool {
        let pfn_set = set_int_range(pfn + 1, pfn + n);
        &&& self.only_update_reserved(new)
        &&& new@.reserved =~~= self@.reserved.union_prefer_right(new@.reserved.restrict(pfn_set))
        &&& new.wf_reserved()
        &&& forall|i|
            #![trigger new@.reserved[i]]
            pfn < i < pfn + n ==> new@.spec_page_info(i) == Some(
                PageInfo::Compound(CompoundInfo { order }),
            )
    }

    spec fn req_init_compound_page(&self, pfn: usize, order: usize, next_pfn: usize) -> bool {
        &&& self.valid_pfn_order(pfn, order)
        &&& (self.valid_pfn_order(next_pfn, order) || next_pfn == 0)
        &&& self.wf_reserved()
        &&& self.wf_params()
    }

    spec fn only_update_reserved(&self, new: Self) -> bool {
        let expected_perm = MemoryRegionTracked { reserved: new@.reserved, ..self@ };
        let expected_self = MemoryRegion { perms: new.perms, ..*self };
        &&& expected_self === new
        &&& expected_perm === new@
    }

    spec fn only_update_reserved_and_tmp_nr(&self, new: &Self) -> bool {
        let expected_perm = MemoryRegionTracked { reserved: new@.reserved, ..self@ };
        let expected_self = MemoryRegion {
            perms: new.perms,
            nr_pages: new.nr_pages,
            tmp_perms: new.tmp_perms,
            ..*self
        };
        &&& expected_self === *new
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

    spec fn ens_init_compound_page(
        &self,
        new: Self,
        pfn: usize,
        order: usize,
        next_pfn: usize,
    ) -> bool {
        let n = 1usize << order;
        let changes = Map::new(|i| pfn <= i < pfn + n, |i| new@.reserved[i]);
        &&& self.only_update_reserved(new)
        &&& new@.reserved =~~= self@.reserved.union_prefer_right(changes)
        &&& new@.marked_free(pfn, order, next_pfn)
        &&& new.wf_reserved()
    }

    spec fn ens_find_neighbor(pfn: usize, order: usize, ret_pfn: usize) -> bool {
        &&& ret_pfn == pfn - (1usize << order) || ret_pfn == pfn + (1usize << order)
        &&& ret_pfn == pfn - (1usize << order) ==> ret_pfn % (1usize << (order + 1) as usize) == 0
        &&& ret_pfn == pfn + (1usize << order) ==> pfn % (1usize << (order + 1) as usize) == 0
        &&& ret_pfn % (1usize << order) == 0
    }

    spec fn ens_compound_neighbor_ok(&self, pfn: usize, order: usize, ret_pfn: usize) -> bool {
        let new_order = (order + 1) as usize;
        let n = 1usize << order;
        let m = 1usize << new_order;
        &&& ret_pfn < self.page_count
        &&& Self::ens_find_neighbor(pfn, order, ret_pfn)
    }

    spec fn req_allocate_pfn(&self, pfn: usize, order: usize) -> bool {
        let n = 1usize << order;
        &&& self@.reserved_pfn_count() <= pfn
        &&& pfn % n == 0
        &&& order < MAX_ORDER
        &&& self.wf()
    }

    spec fn ens_allocate_pfn(&self, new: &Self, pfn: usize, order: usize) -> bool {
        &&& self@.ens_allocate_pfn(new@, pfn, order)
        &&& new.tmp_perms@@ === self.tmp_perms@@.push(new.tmp_perms@@.last())
        &&& new.tmp_perms@@.last().wf_vaddr_order(self.spec_get_virt(pfn as int), order as usize)
        &&& new.wf()
        &&& new.map() === self.map()
        &&& new.valid_pfn_order(pfn, order)
        &&& new.nr_pages === self.nr_pages
        &&& new.free_pages@ === self.free_pages@.update(
            order as int,
            (self.free_pages[order as int] - 1) as usize,
        )
        &&& new@.pfn_range_is_allocated(
            pfn,
            order,
        )
        //&&& forall|pfn, order| #[trigger]
        //    self@.pfn_range_is_allocated(pfn, order) ==> new@.pfn_range_is_allocated(pfn, order)

    }

    spec fn req_try_to_merge_page(&self, pfn: usize, order: usize) -> bool {
        &&& self.wf_reserved()
        &&& self.wf()
        &&& self.tmp_perms@@.len() >= 1
        &&& self.tmp_perms@@.last().wf_vaddr_order(self.spec_get_virt(pfn as int), order as usize)
        &&& self.valid_pfn_order(pfn, order)
        &&& self@.marked_not_free(pfn, order)
        &&& self@.pfn_range_is_allocated(pfn, order)
    }

    spec fn ens_try_to_merge_page_ok(
        &self,
        new: &Self,
        pfn: usize,
        order: usize,
        ret: Result<usize, AllocError>,
    ) -> bool {
        let new_pfn = ret.unwrap();
        let vaddr = new.spec_get_virt(new_pfn as int);
        let order = order as int;
        let n1 = (self.nr_pages[order] - 2) as usize;
        let n2 = (self.nr_pages[order + 1] + 1) as usize;
        let new_nr_pages = self.nr_pages@.update(order, n1).update(order + 1, n2);
        let new_free_pages = self.free_pages@.update(order, (self.free_pages[order] - 1) as usize);
        let new_order = (order + 1) as usize;
        &&& new_pfn == pfn || new_pfn == pfn - (1usize << order)
        &&& new.wf()
        &&& self.with_same_mapping(new)
        &&& new.tmp_perms@@.last().wf_vaddr_order(vaddr, new_order)
        &&& new.tmp_perms@@.len() >= 1
        &&& self.valid_pfn_order(new_pfn, new_order)
        &&& new.nr_pages@ =~= new_nr_pages
        &&& new.free_pages@ === new_free_pages
        &&& new@.marked_not_free(new_pfn, new_order)
        &&& new@.pfn_range_is_allocated(new_pfn, new_order)
    }

    spec fn ens_try_to_merge_page(
        &self,
        new: &Self,
        pfn: usize,
        order: usize,
        ret: Result<usize, AllocError>,
    ) -> bool {
        &&& ret.is_ok() ==> self.ens_try_to_merge_page_ok(new, pfn, order, ret)
        &&& ret.is_err() ==> (self == new)
    }

    spec fn req_merge_pages(&self, pfn1: usize, pfn2: usize, order: usize) -> bool {
        let pfn = vstd::math::min(pfn1 as int, pfn2 as int);
        &&& self.wf()
        &&& self.tmp_perms@@.len() >= 2
        &&& self.tmp_perms@@.last().wf_vaddr_order(self.spec_get_virt(pfn2 as int), order as usize)
        &&& self.tmp_perms@@[self.tmp_perms@@.len() - 2].wf_vaddr_order(
            self.spec_get_virt(pfn1 as int),
            order as usize,
        )
        &&& (pfn1 == pfn2 + (1usize << order)) || (pfn1 == pfn2 - (1usize << order))
        &&& self.valid_pfn_order(pfn as usize, (order + 1) as usize)
        &&& 0 <= order < MAX_ORDER - 1
        &&& self@.pfn_range_is_allocated(pfn1, order)
        &&& self@.pfn_range_is_allocated(pfn2, order)
        &&& self@.marked_order(pfn1, order)
        &&& self@.marked_order(pfn2, order)
    }

    spec fn ens_merge_pages_ok(
        &self,
        new: &Self,
        pfn1: usize,
        pfn2: usize,
        order: usize,
        ret: usize,
    ) -> bool {
        let order = order as int;
        let pfn = vstd::math::min(pfn1 as int, pfn2 as int);
        let n1 = (self.nr_pages[order] - 2) as usize;
        let n2 = (self.nr_pages[order + 1] + 1) as usize;
        let new_nr_pages = self.nr_pages@.update(order, n1).update(order + 1, n2);
        &&& new.wf()
        &&& ret == pfn
        &&& new.tmp_perms@@ === self.tmp_perms@@.take(self.tmp_perms@@.len() - 2).push(
            new.tmp_perms@@.last(),
        )
        &&& new.tmp_perms@@.last().wf_vaddr_order(self.spec_get_virt(pfn), (order + 1) as usize)
        &&& self.only_update_reserved_and_tmp_nr(new)
        &&& new.nr_pages@ === new_nr_pages
        &&& new@.marked_allocated(pfn as usize, (order + 1) as usize)
        &&& new@.pfn_range_is_allocated(pfn as usize, (order + 1) as usize)
    }

    spec fn ens_merge_pages(
        &self,
        new: &Self,
        pfn1: usize,
        pfn2: usize,
        order: usize,
        ret: Result<usize, AllocError>,
    ) -> bool {
        &&& ret.is_ok()
        &&& self.ens_merge_pages_ok(new, pfn1, pfn2, order, ret.unwrap())
    }

    spec fn ens_free_page_order(&self, new: &Self, pfn: usize, order: usize) -> bool {
        &&& new.wf()
        &&& new@.contains_range(pfn, order)
    }

    spec fn req_free_page(&self, vaddr: VirtAddr, tmp_perm: RawPerm) -> bool {
        let pfn = self.spec_get_pfn(vaddr).unwrap();
        let order = self@.reserved().spec_page_info(pfn).unwrap().get_order();
        &&& self.wf()
        &&& vaddr.is_canonical()
        &&& vaddr@ % 0x1000 == 0
        &&& tmp_perm.wf_vaddr_order(vaddr, order)
    }

    spec fn ens_free_page(&self, new: &Self, vaddr: VirtAddr) -> bool {
        let pfn = self.spec_get_pfn(vaddr);
        if pfn.is_some() {
            let order = self@.reserved().spec_page_info(pfn.unwrap()).unwrap().get_order();
            &&& new.wf()
            &&& new@.contains_range(pfn.unwrap(), order)
        } else {
            new === self
        }
    }

    proof fn lemma_derive_contains_range(
        &self,
        new: &Self,
        new_pfn: usize,
        new_order: usize,
        pfn: usize,
        order: usize,
    )
        requires
            new_pfn == pfn || new_pfn == pfn - (1usize << order),
            0 <= order < new_order < MAX_ORDER,
        ensures
            self.ens_free_page_order(new, new_pfn, new_order) ==> new@.contains_range(pfn, order),
    {
        broadcast use lemma_bit_usize_shl_values;

        if self.ens_free_page_order(new, new_pfn, new_order) {
            assert((1usize << order) < (1usize << new_order));
            let (o, i) = new@.choose_order_idx(new_pfn, new_order);
            assert(new@.contained_by_order_idx(new_pfn, new_order, o, i));
            assert(new@.contained_by_order_idx(pfn, order, o, i));
        }
    }

    spec fn req_free_page_raw(&self, pfn: usize, order: usize) -> bool {
        &&& self.wf()
        &&& self@.marked_not_free(pfn, order)
        &&& self.tmp_perms@@.last().wf_vaddr_order(self.spec_get_virt(pfn as int), order)
        &&& self.tmp_perms@@.len() > 0
        &&& self.valid_pfn_order(pfn, order)
        &&& self@.pfn_range_is_allocated(pfn, order)
    }

    spec fn ens_free_page_raw(&self, new: &Self, pfn: usize, order: usize) -> bool {
        let end = pfn + (1usize << order);
        let new_count = self.free_pages[order as int] + 1;
        &&& new.wf()
        &&& new.next_page@ === self.next_page@.update(order as int, pfn)
        &&& new.free_pages@ === self.free_pages@.update(order as int, new_count as usize)
        &&& new@.contained_by_order_idx(
            pfn,
            order,
            order as int,
            new@.next[order as int].len() - 1,
        )  // to prove contains_range

    }
}

} // verus!
