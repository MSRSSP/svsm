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
use verify_proof::frac_ptr::raw_perm_is_disjoint;
use verify_proof::frac_ptr::FracTypedPerm;
use verify_proof::nonlinear::lemma_align_down_properties;
use verify_proof::nonlinear::lemma_modulus_add_sub_m;
use verify_proof::set::{lemma_int_range_disjoint, spec_int_range_disjoint};
use vstd::arithmetic::div_mod::{lemma_add_mod_noop, lemma_mod_self_0, lemma_small_mod};
use vstd::arithmetic::mul::group_mul_properties;
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_ordering};
use vstd::arithmetic::mul::{
    lemma_mul_is_distributive_add_other_way, lemma_mul_is_distributive_sub_other_way,
};
use vstd::modes::tracked_swap;
use vstd::raw_ptr::PointsToRaw;
use vstd::raw_ptr::{IsExposed, Provenance};
use vstd::set_lib::set_int_range;

verus! {

use crate::mm::address_space::LinearMap;

broadcast group set_len_group {
    verify_proof::set::lemma_set_filter_disjoint_len,
    verify_proof::set::lemma_int_range,
    verify_proof::set::lemma_len_filter,
    verify_proof::set::lemma_len_subset,
}

broadcast group alloc_broadcast_group {
    //crate::address::group_addr_proofs,
    LinearMap::lemma_get_paddr,
    lemma_bit_usize_shl_values,
    lemma_page_size,
    set_len_group,
}

broadcast use alloc_broadcast_group;

include!("alloc_info.verus.rs");

include!("alloc_free.verus.rs");

include!("alloc_perms.verus.rs");

//include!("alloc_mr.verus.rs");
include!("alloc_p.verus.rs");

include!("alloc_types.verus.rs");

pub type RawPerm = PointsToRaw;

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

pub const MAX_PAGE_COUNT: usize = usize::MAX >> 12;

pub spec const MAX_PGINFO_SHARES: nat = 2;

pub spec const ALLOCATOR_PGINFO_SHARES: nat = 1;

pub spec const DEALLOC_PGINFO_SHARES: nat = 1;

pub uninterp spec fn allocator_provenance() -> Provenance;

#[verifier(inline)]
spec fn order_set(start: usize, order: usize) -> Set<int> {
    set_int_range(start as int, start as int + (1usize << order))
}

spec fn order_disjoint(start1: usize, order1: usize, start2: usize, order2: usize) -> bool {
    let end1 = start1 + (1usize << order1);
    let end2 = start2 + (1usize << order2);
    spec_int_range_disjoint(start1 as int, end1, start2 as int, end2)
}

impl MemoryRegion {
    spec fn remove_tracked(&self) -> Self {
        MemoryRegion { perms: arbitrary(), ..*self }
    }

    spec fn writable_page_info(&self, pfn: usize, perm: FracTypedPerm<PageStorageType>) -> bool {
        &&& perm.valid()
        &&& perm.writable()
        &&& perm.ptr() == self.view2().page_info_ptr(pfn)
    }

    spec fn writable_page_infos(
        &self,
        pfn: usize,
        size: usize,
        perms: Map<usize, PInfoPerm>,
    ) -> bool {
        &&& perms.contains_range(self.perms@.base_ptr(), pfn, size)
        &&& forall|i: usize|
            pfn <= i < pfn + size ==> self.writable_page_info(i, (#[trigger] perms[i]))
    }

    #[verifier(inline)]
    spec fn req_write_page_info(
        &self,
        pfn: usize,
        pi: PageInfo,
        perm: FracTypedPerm<PageStorageType>,
    ) -> bool {
        self.writable_page_info(pfn, perm)
    }

    spec fn ens_write_page_info(
        &self,
        new: Self,
        pfn: usize,
        pi: PageInfo,
        old_perm: FracTypedPerm<PageStorageType>,
        perm: FracTypedPerm<PageStorageType>,
    ) -> bool {
        &&& *self == new
        &&& old_perm.ens_write_page_info(&perm, pfn, pi)
    }

    spec fn req_mark_compound_page(
        &self,
        pfn: usize,
        order: usize,
        perms: Map<usize, PInfoPerm>,
    ) -> bool {
        let size = (1usize << order);
        &&& self.writable_page_infos((pfn + 1) as usize, (size - 1) as usize, perms)
        &&& self.valid_pfn_order(pfn, order)
        &&& self.wf_basic2()
    }

    spec fn ens_mark_compound_page(
        &self,
        new: Self,
        pfn: usize,
        order: usize,
        perms: Map<usize, PInfoPerm>,
        new_perms: Map<usize, PInfoPerm>,
    ) -> bool {
        &&& self.ens_mark_compound_page_loop(new, pfn, 1usize << order, order, perms, new_perms)
    }

    spec fn ens_mark_compound_page_loop(
        &self,
        new: Self,
        pfn: usize,
        size: usize,
        order: usize,
        perms: Map<usize, PInfoPerm>,
        new_perms: Map<usize, PInfoPerm>,
    ) -> bool {
        let pi = PageInfo::Compound(CompoundInfo { order });
        &&& *self == new
        &&& new_perms.dom() =~= perms.dom()
        &&& forall|i: usize|
            #![trigger new_perms[i]]
            perms.contains_key(i) ==> if pfn < i < pfn + size {
                perms[i].ens_write_page_info(&new_perms[i], i, pi)
            } else {
                new_perms[i] == perms[i]
            }
    }

    spec fn req_init_compound_page(
        &self,
        pfn: usize,
        order: usize,
        next_pfn: usize,
        perms: Map<usize, PInfoPerm>,
    ) -> bool {
        &&& self.valid_pfn_order(pfn, order)
        &&& (self.valid_pfn_order(next_pfn, order) || next_pfn == 0)
        &&& self.writable_page_infos(pfn, 1usize << order, perms)
    }

    spec fn update_page_info_group(
        pfn: usize,
        order: usize,
        pi: PageInfo,
        perms: Map<usize, PInfoPerm>,
        new_perms: Map<usize, PInfoPerm>,
    ) -> bool {
        let size = 1usize << order;
        let cpi = PageInfo::Compound(CompoundInfo { order });
        &&& new_perms.dom() =~= perms.dom()
        &&& forall|i: usize|
            #![trigger new_perms[i]]
            pfn <= i < pfn + size ==> perms[i].ens_write_page_info(
                &new_perms[i],
                i,
                if i == pfn {
                    pi
                } else {
                    cpi
                },
            )
    }

    spec fn ens_init_compound_page(
        &self,
        new: Self,
        pfn: usize,
        order: usize,
        next_pfn: usize,
        perms: Map<usize, PInfoPerm>,
        new_perms: Map<usize, PInfoPerm>,
    ) -> bool {
        let size = 1usize << order;
        let pi = PageInfo::Free(FreeInfo { next_page: next_pfn, order });
        &&& Self::update_page_info_group(order, next_pfn, pi, perms, new_perms)
        &&& *self == new
    }

    spec fn req_merge_pages(
        &self,
        pfn1: usize,
        pfn2: usize,
        order: usize,
        p1: PgUnitPerm<DeallocUnit>,
        p2: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        let pfn = vstd::math::min(pfn1 as int, pfn2 as int);
        &&& self.wf()
        &&& self.valid_pfn_order(pfn as usize, (order + 1) as usize)
        &&& 0 <= order < MAX_ORDER - 1
        &&& p1.wf_pfn_order(self@.mr_map, pfn1, order)
        &&& p2.wf_pfn_order(self@.mr_map, pfn2, order)
        &&& (pfn1 == pfn2 + (1usize << order)) || (pfn1 == pfn2 - (1usize << order))
    }

    spec fn ens_merge_pages_ok(
        &self,
        new: &Self,
        pfn1: usize,
        pfn2: usize,
        order: usize,
        ret: usize,
        perm: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        let pfn = vstd::math::min(pfn1 as int, pfn2 as int) as usize;
        let new_order = (order + 1) as usize;
        let n1 = (self.nr_pages[order as int] - 2) as usize;
        let n2 = (self.nr_pages[new_order as int] + 1) as usize;
        let new_nr_pages = self.nr_pages@.update(order as int, n1).update(order + 1, n2);
        &&& new.wf()
        &&& ret == pfn
        &&& perm.wf_pfn_order(self@.mr_map, pfn, new_order)
    }

    spec fn ens_merge_pages(
        &self,
        new: &Self,
        pfn1: usize,
        pfn2: usize,
        order: usize,
        ret: Result<usize, AllocError>,
        perm: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        &&& ret.is_ok()
        &&& self.ens_merge_pages_ok(new, pfn1, pfn2, order, ret.unwrap(), perm)
    }

    spec fn req_split_page(&self, pfn: usize, order: usize, perm: PgUnitPerm<DeallocUnit>) -> bool {
        let new_size = (1usize << (order - 1) as usize);
        &&& perm.wf_pfn_order(self@.mr_map, pfn, order)
        &&& self.valid_pfn_order(pfn, order)
        &&& order >= 1
        &&& self.wf()
        &&& self.free_pages[order - 1] + 2
            <= usize::MAX
        //&&& self@.pfn_range_is_allocated(pfn, order)
        //&&& self@.marked_order(pfn, order)
        //&&& self@.pfn_order_is_writable(pfn, order)

    }

    spec fn ens_split_page_ok(&self, new: &Self, pfn: usize, order: usize) -> bool {
        let rhs_pfn = (pfn + (1usize << order) / 2) as usize;
        let new_order = order - 1;
        let order = order as int;
        //let newp = self@.next[new_order].push(rhs_pfn).push(pfn);
        //&&& new@.next =~= self@.next.update(new_order, newp)
        &&& self.with_same_mapping(new)
        &&& new.wf()/*&&& new.nr_pages@[new_order] == self.nr_pages[new_order] + 2
        &&& new.nr_pages@[order] == self.nr_pages[order] - 1
        &&& new.free_pages[new_order] == self.free_pages[new_order] + 2
        &&& new.nr_pages@ =~= self.nr_pages@.update(new_order, new.nr_pages[new_order]).update(
            order,
            new.nr_pages[order],
        )
        &&& new.free_pages@ =~= self.free_pages@.update(new_order, new.free_pages[new_order])
        &&& new.next_page@ =~= self.next_page@.update(order - 1, pfn)*/

    }
}

impl MemoryRegion {
    pub closed spec fn view2(&self) -> MemoryRegionPerms {
        self.perms@
    }

    pub closed spec fn view(&self) -> MemoryRegionPerms {
        self.perms@
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

    // Basic invariant that should hold except in initialization stage
    spec fn wf_params(&self) -> bool {
        true
    }

    spec fn wf_reserved(&self) -> bool {
        true
    }

    spec fn spec_get_pfn(&self, vaddr: VirtAddr) -> Option<usize> {
        self.map().get_pfn(vaddr)
    }

    spec fn spec_try_get_virt(&self, pfn: int) -> Option<VirtAddr> {
        self.map().try_get_virt(pfn as usize)
    }

    #[verifier(inline)]
    spec fn spec_get_virt(&self, pfn: int) -> VirtAddr {
        self.spec_try_get_virt(pfn).unwrap()
    }

    /// virt_offset == physical_offset
    spec fn ens_get_pfn(&self, vaddr: VirtAddr, ret: Result<usize, AllocError>) -> bool {
        &&& ret.is_ok() == self.spec_get_pfn(vaddr).is_some()
        &&& ret.is_ok() ==> {
            &&& ret.unwrap() == self.spec_get_pfn(vaddr).unwrap()
            &&& self.spec_try_get_virt(ret.unwrap() as int).is_some()
            &&& ret.unwrap() < self.page_count
            &&& vaddr@ % 0x1000 == 0 ==> self.spec_get_virt(ret.unwrap() as int) == vaddr
        }
    }

    spec fn ens_get_next_page(
        &self,
        new_self: &Self,
        order: usize,
        ret: Result<usize, AllocError>,
        perm: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        let order = order as int;
        &&& self.with_same_mapping(new_self)
        &&& ret.is_err() == ((self.next_page[order] == 0) && (self.free_pages[order] == 0))
        &&& ret.is_err() ==> self === new_self
        &&& ret.is_ok() ==> {
            &&& perm.wf_pfn_order(new_self@.mr_map, ret.unwrap(), order as usize)
            &&& ret.unwrap() == self.next_page[order]
            &&& new_self.valid_pfn_order(
                ret.unwrap(),
                order as usize,
            )/*&&& new_self.free_pages@ === self.free_pages@.update(
                order,
                (self.free_pages[order] - 1) as usize,
            )
            &&& new_self.next_page@ === self.next_page@.update(order, new_self.next_page[order])
            &&& new_self@.next[order] === self@.next[order].remove(self@.next[order].len() - 1)
            &&& new_self@.next === self@.next.update(order, new_self@.next[order])
            &&& self@.inv_remove_pfn(new_self@)
            &&& new_self.nr_pages === self.nr_pages
            //&&& new_self@.pfn_range_is_allocated(ret.unwrap(), order as usize)
            &&& new_self@.marked_order(ret.unwrap(), order as usize)
            &&& new_self@.reserved === self@.reserved*/
            //&&& new_self@.pfn_order_is_writable(ret.unwrap(), order as usize)

        }
    }

    spec fn ens_read_page_info(self, pfn: usize, ret: PageInfo) -> bool {
        let pi = self@.get_info(pfn);
        &&& pi === Some(ret)
        &&& pfn < self.page_count
    }

    spec fn spec_alloc_fails(&self, order: int) -> bool {
        forall|i| #![trigger self.next_page[i]] order <= i < MAX_ORDER ==> self.next_page[i] == 0
    }

    spec fn pg_params(&self) -> PageCountParam<MAX_ORDER> {
        PageCountParam { page_count: self.page_count }
    }

    spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        &&& self.pg_params().valid_pfn_order(pfn, order)
        &&& pfn < MAX_PAGE_COUNT
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

    spec fn only_update_reserved_and_tmp_nr(&self, new: &Self) -> bool {
        true
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
        //let n = 1usize << order;
        //&&& self@.reserved_pfn_count() <= pfn
        //&&& pfn % n == 0
        &&& self.valid_pfn_order(pfn, order)
        //&&& order < MAX_ORDER
        &&& self.wf()
    }

    spec fn ens_allocate_pfn(
        &self,
        new: &Self,
        pfn: usize,
        order: usize,
        perm: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        //&&& self@.ens_allocate_pfn(new@, pfn, order)
        &&& perm.wf_pfn_order(self@.mr_map, pfn, order)
        &&& new.wf()
        &&& self.with_same_mapping(new)
        &&& new.valid_pfn_order(
            pfn,
            order,
        )/*&&& new.nr_pages === self.nr_pages
        &&& new.free_pages@ === self.free_pages@.update(
            order as int,
            (self.free_pages[order as int] - 1) as usize,
        )*/
        //&&& new@.pfn_order_is_writable(pfn, order)

    }

    spec fn req_try_to_merge_page(
        &self,
        pfn: usize,
        order: usize,
        perm: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        &&& self.wf_reserved()
        &&& self.wf()
        &&& perm.wf_pfn_order(self@.mr_map, pfn, order)
        &&& self.valid_pfn_order(
            pfn,
            order,
        )
        //&&& self@.marked_not_free(pfn, order)
        //&&& self@.pfn_range_is_allocated(pfn, order)
        //&&& self@.pfn_order_is_writable(pfn, order)

    }

    spec fn ens_try_to_merge_page_ok(
        &self,
        new: &Self,
        pfn: usize,
        order: usize,
        ret: Result<usize, AllocError>,
        perm: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        let new_pfn = ret.unwrap();
        let order = order as int;
        let n1 = (self.nr_pages[order] - 2) as usize;
        let n2 = (self.nr_pages[order + 1] + 1) as usize;
        let new_nr_pages = self.nr_pages@.update(order, n1).update(order + 1, n2);
        let new_free_pages = self.free_pages@.update(order, (self.free_pages[order] - 1) as usize);
        let new_order = (order + 1) as usize;
        &&& new_pfn == pfn || new_pfn == pfn - (1usize << order)
        &&& new.wf()
        &&& self.with_same_mapping(new)
        &&& perm.wf_pfn_order(new@.mr_map, new_pfn, new_order)
        &&& self.valid_pfn_order(new_pfn, new_order)
        &&& new.nr_pages@ =~= new_nr_pages
        &&& new.free_pages@
            === new_free_pages/*&&& new@.marked_not_free(new_pfn, new_order)
        &&& new@.pfn_range_is_allocated(new_pfn, new_order)
        &&& new@.pfn_order_is_writable(new_pfn, new_order)*/

    }

    spec fn ens_try_to_merge_page(
        &self,
        new: &Self,
        pfn: usize,
        order: usize,
        ret: Result<usize, AllocError>,
        old_perm: PgUnitPerm<DeallocUnit>,
        perm: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        &&& ret.is_ok() ==> self.ens_try_to_merge_page_ok(new, pfn, order, ret, perm)
        &&& ret.is_err() ==> (self == new) && perm == old_perm
    }

    spec fn ens_free_page_order(&self, new: &Self, pfn: usize, order: usize) -> bool {
        &&& new.wf()
        //&&& new@.contains_range(pfn, order)

    }

    spec fn req_free_page(&self, vaddr: VirtAddr, perm: UnitDeallocPerm) -> bool {
        /*let UnitDeallocPerm(perm) = perm;
        let pfn = self.spec_get_pfn(vaddr).unwrap();
        let order = self@.reserved().spec_page_info(pfn).unwrap().spec_order();
        &&& self.wf()
        &&& vaddr.is_canonical()
        &&& vaddr@ % 0x1000 == 0
        &&& perm.wf_pfn_order(self.view2().map(), pfn, order)*/
        true
    }

    spec fn ens_free_page(&self, new: &Self, vaddr: VirtAddr) -> bool {
        true/*let pfn = self.spec_get_pfn(vaddr);
        if pfn.is_some() {
            new.wf()
        } else {
            new === self
        }*/

    }

    spec fn req_free_page_raw(
        &self,
        pfn: usize,
        order: usize,
        perm: PgUnitPerm<DeallocUnit>,
    ) -> bool {
        &&& self.wf()
        //&&& self@.marked_not_free(pfn, order)
        &&& self.valid_pfn_order(pfn, order)
        &&& perm.wf_pfn_order(
            self@.mr_map,
            pfn,
            order,
        )
        //&&& self@.pfn_range_is_allocated(pfn, order)
        //&&& self@.pfn_order_is_writable(pfn, order)

    }

    spec fn ens_free_page_raw(&self, new: &Self, pfn: usize, order: usize) -> bool {
        let end = pfn + (1usize << order);
        let new_count = self.free_pages[order as int] + 1;
        &&& new.wf()/*&&& new.next_page@ === self.next_page@.update(order as int, pfn)
        &&& new.free_pages@ === self.free_pages@.update(
            order as int,
            new_count as usize,
        )
        &&& new@.contained_by_order_idx(
            pfn,
            order,
            order as int,
            new@.next[order as int].len() - 1,
        )*/

    }

    spec fn req_allocate_pages_info(&self, order: usize, pg: PageInfo) -> bool {
        &&& self.wf()
        &&& order < MAX_ORDER
        &&& pg.spec_order() == order
        &&& pg.spec_type().spec_is_deallocatable()
    }

    spec fn ens_allocate_pages_info(
        &self,
        new: &Self,
        order: usize,
        ret: Result<VirtAddr, AllocError>,
        perm_with_dealloc: Option<UnitDeallocPerm>,
    ) -> bool {
        let pfn = self.spec_get_pfn(ret.unwrap()).unwrap();
        let UnitDeallocPerm(perm) = perm_with_dealloc.unwrap();
        &&& self.with_same_mapping(new)
        &&& new.wf()/*&&& ret.is_ok() ==> {
            &&& perm.wf_pfn_order(new.view2().map(), pfn, order)
            &&& perm_with_dealloc.is_some()
        }*/

    }
}

} // verus!
