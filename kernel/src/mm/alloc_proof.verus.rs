// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// This file contains proofs for the allocator's invariants and correctness.
//
// Key Invariant to Prove:
// 1. PageInfo is consistent with the allocator state (MemoryRegionTracked::wf)
//    pfn in free list <==> pinfo is free info with correct order and next_pfn
//
// In order to prove the above invariant, we need to prove additional invariants:
// 1. Unique Memory Ranges
// 2. Mathematical Relationship between `page_count` and the allocator's page counter
//
// Those invariants are used to prove the correct implementation of allocator.
verus! {

use vstd::arithmetic::div_mod::{lemma_mod_self_0, lemma_small_mod, lemma_add_mod_noop};
use verify_proof::nonlinear::lemma_align_down_properties;
use vstd::modes::tracked_swap;

global size_of PageStorageType == 8;

broadcast group set_len_group {
    verify_proof::set::lemma_set_filter_disjoint_len,
    verify_proof::set::lemma_int_range,
    verify_proof::set::lemma_len_filter,
    verify_proof::set::lemma_len_subset,
}

proof fn is_disjoint(tracked p1: &mut RawPerm, p2: &RawPerm)
    requires
        old(p1).dom().len() > 0,
    ensures
        *old(p1) == *p1,
        p1.dom().disjoint(p2.dom()),
{
    admit();
}

impl MemoryRegionTracked<MAX_ORDER> {
    #[verifier::spinoff_prover]
    proof fn lemma_pfn_range_disjoint_rec1(
        tracked &self,
        tracked perm: &mut RawPerm,
        pfn: usize,
        order: usize,
        o: int,
        n: nat,
    )
        requires
            self.wf(),
            old(perm).wf_pfn_order(self.map, pfn, order),
            self.valid_pfn_order(pfn, order),
            0 <= order < MAX_ORDER,
            0 <= o < MAX_ORDER,
            n <= self.next[o].len(),
        ensures
            forall|i|
                0 <= i < n ==> order_disjoint(#[trigger] self.next[o][i], o as usize, pfn, order),
            forall|i|
                #![trigger self.next[o][i]]
                0 <= i < n ==> (self.free_dom_at(o as usize, i)).disjoint(order_set(pfn, order)),
            *old(perm) == *perm,
        decreases n,
    {
        broadcast use lemma_bit_usize_shl_values, verify_proof::set::lemma_int_range;

        let next = self.next;
        if n > 0 {
            let i = n - 1;
            let p = self.next[o][i];
            let npages = 1usize << order;
            let mem_size = npages * PAGE_SIZE;
            let vaddr1 = self.map.lemma_get_virt(pfn);
            let start1 = vaddr1@ as int;
            let end1 = start1 + npages;
            assert(self.wf_at(o, i));
            let pfn2 = self.next[o][i];
            let vaddr2 = self.map.lemma_get_virt(pfn2);
            let start2 = vaddr2@ as int;
            let end2 = start2 + (1usize << o);
            let perm2 = self.avail.tracked_borrow((o, i));
            vaddr1.lemma_vaddr_region_len(mem_size as nat);
            is_disjoint(perm, perm2);
            assert(perm.dom().contains(start1));
            assert(perm2.dom().contains(start2));
            assert(order_disjoint(#[trigger] self.next[o][n - 1], o as usize, pfn, order));
            assert(self.free_dom_at(o as usize, i).disjoint(order_set(pfn, order)));
            self.lemma_pfn_range_disjoint_rec1(perm, pfn, order, o, (n - 1) as nat);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pfn_range_disjoint_rec2(
        tracked &self,
        tracked perm: &mut RawPerm,
        pfn: usize,
        order: usize,
        max_order: int,
    )
        requires
            self.wf(),
            self.valid_pfn_order(pfn, order),
            old(perm).wf_pfn_order(self.map, pfn, order),
            0 <= order < MAX_ORDER,
            0 <= max_order <= MAX_ORDER,
        ensures
            forall|o, i|
                0 <= o < max_order && 0 <= i < self.next[o].len() ==> order_disjoint(
                    #[trigger] self.next[o][i],
                    o as usize,
                    pfn,
                    order,
                ),
            forall|o: usize|
                #![trigger self.next[o as int]]
                0 <= o < max_order ==> self.free_order_dom(o).disjoint(order_set(pfn, order)),
            *old(perm) == *perm,
        decreases max_order,
    {
        if max_order > 0 {
            let o = max_order - 1;
            self.lemma_pfn_range_disjoint_rec1(perm, pfn, order, o, self.next[o].len());
            assert(self.free_order_dom(o as usize).disjoint(order_set(pfn, order)));
            self.lemma_pfn_range_disjoint_rec2(perm, pfn, order, max_order - 1);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_perm_disjoint(
        tracked &self,
        tracked perm: &mut RawPerm,
        pfn: usize,
        order: usize,
    )
        requires
            self.wf(),
            self.valid_pfn_order(pfn, order),
            #[trigger] old(perm).wf_pfn_order(self.map, pfn, order),
            0 <= order < MAX_ORDER,
        ensures
            self.pfn_range_is_allocated(pfn, order),
            self.free_dom().disjoint(order_set(pfn, order)),
            //self.free_dom().len() + (1usize << order) <= self.max_free_page_count(),
            *old(perm) == *perm,
    {
        reveal(MemoryRegionTracked::free_dom);
        self.lemma_pfn_range_disjoint_rec2(perm, pfn, order, MAX_ORDER as int);
        assert(self.free_dom().disjoint(order_set(pfn, order)));
        broadcast use set_len_group;

    }

    #[verifier::spinoff_prover]
    proof fn lemma_tmp_perm_disjoint(
        tracked &self,
        tracked tmp_perms: &mut TrackedSeq<RawPerm>,
        pfn: usize,
        order: usize,
    )
        requires
            self.wf(),
            self.valid_pfn_order(pfn, order),
            old(tmp_perms).len() > 0,
            old(tmp_perms).last().wf_pfn_order(self.map, pfn, order),
            0 <= order < MAX_ORDER,
        ensures
            self.pfn_range_is_allocated(pfn, order),
            tmp_perms@ == old(tmp_perms)@,
            self.free_dom().disjoint(order_set(pfn, order)),
    {
        let tracked mut perm = tmp_perms.tracked_pop();
        self.lemma_perm_disjoint(&mut perm, pfn, order);
        tmp_perms.tracked_push(perm);
        assert(tmp_perms@ =~= old(tmp_perms)@);
    }
}

#[verifier::rlimit(4)]
proof fn tracked_merge(
    tracked p1: &mut RawPerm,
    tracked p2: RawPerm,
    map: LinearMap,
    pfn1: usize,
    pfn2: usize,
    order: usize,
)
    requires
        map.wf(),
        0 <= order < 64,
        pfn1 == pfn2 + (1usize << order) || pfn2 == pfn1 + (1usize << order),
        p2.wf_pfn_order(map, pfn2, order),
        old(p1).wf_pfn_order(map, pfn1, order),
    ensures
        p1.wf_pfn_order(
            map,
            if pfn1 < pfn2 {
                pfn1
            } else {
                pfn2
            },
            (order + 1) as usize,
        ),
{
    broadcast use lemma_bit_usize_shl_values;

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

impl<const N: usize> ReservedPerms<N> {
    #[verifier::spinoff_prover]
    proof fn lemma_pfn_dom_update(&self, new: Self, pfn_set: Set<int>, order1: usize, order2: usize)
        requires
            self.wf_dom(),
            new.wf_dom(),
            self.page_count() == new.page_count(),
            order1 != order2,
            pfn_set.finite(),
            forall|pfn: int| #[trigger]
                pfn_set.contains(pfn) ==> 0 <= pfn < self.page_count() && self.spec_page_info(
                    pfn as usize,
                ).unwrap().get_order() == order1,
            forall|pfn: int| #[trigger]
                pfn_set.contains(pfn) ==> new.spec_page_info(pfn as usize).unwrap().get_order()
                    == order2,
            forall|pfn: int|
                0 <= pfn < self.page_count() && !#[trigger] pfn_set.contains(pfn)
                    ==> self.spec_page_info(pfn as usize).unwrap().get_order()
                    == new.spec_page_info(pfn as usize).unwrap().get_order(),
        ensures
            new.pfn_dom(order1).union(pfn_set) =~= self.pfn_dom(order1),
            new.pfn_dom(order1).len() == self.pfn_dom(order1).len() - pfn_set.len(),
            new.pfn_dom(order2) =~= self.pfn_dom(order2).union(pfn_set),
            new.pfn_dom(order2).len() == self.pfn_dom(order2).len() + pfn_set.len(),
            forall|order|
                order != order1 && order != order2 ==> #[trigger] new.pfn_dom(order)
                    === self.pfn_dom(order),
    {
        reveal(ReservedPerms::pfn_dom);
        broadcast use ReservedPerms::lemma_pfn_dom;

        assert(pfn_set.subset_of(self.pfn_dom(order1)));
        assert(pfn_set.subset_of(new.pfn_dom(order2)));

        assert(new.pfn_dom(order1).len() == self.pfn_dom(order1).len() - pfn_set.len()) by {
            assert(new.pfn_dom(order1).union(pfn_set) =~= self.pfn_dom(order1));
            vstd::set_lib::lemma_set_disjoint_lens(new.pfn_dom(order1), pfn_set);
        }
        assert(new.pfn_dom(order2).len() == self.pfn_dom(order2).len() + pfn_set.len()) by {
            vstd::set_lib::lemma_set_disjoint_lens(self.pfn_dom(order2), pfn_set);
            assert(new.pfn_dom(order2) =~= self.pfn_dom(order2).union(pfn_set));
        }

        assert forall|order| order != order1 && order != order2 implies new.pfn_dom(order)
            =~= self.pfn_dom(order) by {
            assert forall|pfn|
                new.pfn_dom(order).contains(pfn) == self.pfn_dom(order).contains(pfn) by {
                if new.pfn_dom(order).contains(pfn) {
                    assert(new.spec_page_info(pfn as usize).unwrap().get_order() == order);
                    assert(!pfn_set.contains(pfn));
                }
                if self.pfn_dom(order).contains(pfn) {
                    assert(self.spec_page_info(pfn as usize).unwrap().get_order() == order);
                    assert(!pfn_set.contains(pfn));
                }
            }
        }
    }

    #[verifier::spinoff_prover]
    broadcast proof fn lemma_pfn_dom(&self, order: usize)
        requires
            self.wf_dom(),
        ensures
            (#[trigger] self.pfn_dom(order)).finite(),
            self.pfn_dom(order).subset_of(set_int_range(0, self.page_count() as int)),
            self.pfn_dom(order).len() <= self.page_count(),
    {
        reveal(ReservedPerms::pfn_dom);
        vstd::set_lib::lemma_int_range(0, self.page_count() as int);
        set_int_range(0, self.page_count() as int).lemma_len_filter(self.pfn_filter(order));
    }

    #[verifier::spinoff_prover]
    broadcast proof fn lemma_pfn_dom_pair(&self, order1: usize, order2: usize)
        requires
            self.wf_dom(),
            order1 != order2,
        ensures
            self.pfn_dom(order1).disjoint(self.pfn_dom(order2)),
            (#[trigger] self.pfn_dom(order1) + #[trigger] self.pfn_dom(order2)).subset_of(
                set_int_range(0, self.page_count() as int),
            ),
            self.pfn_dom(order1).len() + self.pfn_dom(order2).len() <= self.page_count(),
    {
        self.lemma_pfn_dom(order1);
        self.lemma_pfn_dom(order2);
        reveal(ReservedPerms::pfn_dom);
        broadcast use group_mul_properties, lemma_bit_usize_shl_values;

        vstd::set_lib::lemma_int_range(0, self.page_count() as int);
        vstd::set_lib::lemma_set_disjoint_lens(self.pfn_dom(order1), self.pfn_dom(order2));
        vstd::set_lib::lemma_len_subset(
            self.pfn_dom(order1) + self.pfn_dom(order2),
            set_int_range(0, self.page_count() as int),
        );
    }

    #[verifier::spinoff_prover]
    proof fn lemma_marked_order_len_rec(&self, pfn: usize, order: usize, size: int)
        requires
            self.wf_dom(),
            0 <= order < N,
            0 <= size <= (1usize << order),
            self.valid_pfn_order(pfn, order),
            forall|i: usize|
                (pfn <= i < pfn + size) ==> (#[trigger] self.spec_page_info(i)).unwrap().get_order()
                    == order,
        ensures
            self.pfn_dom(order).filter(|i| pfn <= i < pfn + size).len() == size,
            set_int_range(pfn as int, pfn + size).subset_of(self.pfn_dom(order)),
        decreases size,
    {
        reveal(ReservedPerms::pfn_dom);
        let s = self.pfn_dom(order);
        let s1 = s.filter(|i| pfn <= i < pfn + size);
        if size > 0 {
            let s2 = s.filter(|i| pfn <= i < pfn + size - 1);
            self.lemma_marked_order_len_rec(pfn, order, size - 1);
            let s3 = set_int_range(pfn + size - 1, pfn + size);
            vstd::set_lib::lemma_int_range(pfn + size - 1, pfn + size);
            let i = pfn + size - 1;
            assert((pfn <= (i as usize) < pfn + size));
            assert(self.spec_page_info(i as usize).unwrap().get_order() == order);
            assert(s1 =~= s2 + s3);
            self.lemma_pfn_dom(order);
            vstd::set_lib::lemma_set_disjoint_lens(s2, s3);
        } else {
            assert(s1 =~= Set::empty());
        }
    }

    #[verifier::spinoff_prover]
    broadcast proof fn lemma_pfn_dom_len_with_one(&self, pfn: usize, order: usize)
        requires
            self.wf_dom(),
            0 <= order < N <= 64,
            self.valid_pfn_order(pfn, order),
            #[trigger] self.marked_order(pfn, order),
        ensures
            self.pfn_dom(order).len() >= 1usize << order,
            order_set(pfn, order).subset_of(self.pfn_dom(order)),
    {
        broadcast use lemma_bit_usize_shl_values;

        reveal(ReservedPerms::pfn_dom);
        let size = (1usize << order) as int;
        assert forall|i: usize| pfn <= i < pfn + size implies (#[trigger] self.spec_page_info(
            i,
        )).unwrap().get_order() == order by {
            assert(self.spec_page_info(i).is_some());
        }
        self.lemma_marked_order_len_rec(pfn, order, size);
        self.lemma_pfn_dom(order);
        self.pfn_dom(order).lemma_len_filter(|i| pfn <= i < pfn + size);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pfn_dom_len_with_two(&self, pfn1: usize, pfn2: usize, order: usize)
        requires
            self.wf_dom(),
            0 <= order < N <= 64,
            pfn1 != pfn2,
            #[trigger] self.marked_order(pfn1, order),
            #[trigger] self.marked_order(pfn2, order),
        ensures
            self.pfn_dom(order).len() >= (1usize << order) * 2,
    {
        reveal(ReservedPerms::pfn_dom);
        let s = self.pfn_dom(order);
        self.lemma_pfn_dom(order);
        let size = (1usize << order);
        let s1 = set_int_range(pfn1 as int, pfn1 + size);
        vstd::set_lib::lemma_int_range(pfn1 as int, pfn1 + size);
        let s2 = set_int_range(pfn2 as int, pfn2 + size);
        vstd::set_lib::lemma_int_range(pfn2 as int, pfn2 + size);
        assert(s1.disjoint(s2)) by {
            self.page_count.lemma_valid_pfn_order_no_overlap(pfn1, pfn2, order);
        }
        vstd::set_lib::lemma_set_disjoint_lens(s1, s2);
        self.lemma_pfn_dom_len_with_one(pfn1, order);
        self.lemma_pfn_dom_len_with_one(pfn2, order);
        assert((s1 + s2).subset_of(s));
        assert(s1.len() + s2.len() == size * 2);
        vstd::set_lib::lemma_len_subset(s1 + s2, s);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_reserved_info_content_inner_pfn(
        &self,
        new: Self,
        lower_pfn: usize,
        lower_order: usize,
        higher_pfn: usize,
        higher_order: usize,
        pfn: usize,
    )
        requires
            0 <= lower_order < N <= 64,
            0 <= higher_order < N <= 64,
            self.wf_page_info(),
            self.wf_dom(),
            self.page_count() == new.page_count(),
            self.reserved.dom() === new.reserved.dom(),
            self.marked_order(lower_pfn, lower_order),
            self.marked_order(higher_pfn, higher_order),
            forall|p: usize|
                lower_pfn + (1usize << lower_order) <= p < higher_pfn && 0 <= p < self.page_count()
                    ==> #[trigger] self.spec_page_info(p) === new.spec_page_info(p),
        ensures
            lower_pfn + (1usize << lower_order) <= pfn < higher_pfn ==> new.wf_page_info_at(pfn),
    {
        reveal(ReservedPerms::wf_page_info);
        broadcast use lemma_bit_usize_shl_values;

        let pi = self.spec_page_info(pfn).unwrap();
        if lower_pfn + (1usize << lower_order) <= pfn < higher_pfn {
            assert(self.wf_page_info_at(pfn));
            let o = pi.get_order();
            let head = find_pfn_head(pfn, o);
            assert(self.wf_page_info_at(head));
            lemma_align_down_properties(pfn as int, (1usize << o) as int, head as int);
            assert(head == (pfn - (pfn % (1usize << o))) as usize);
            if lower_pfn + (1usize << lower_order) <= head < higher_pfn && self.marked_compound(
                head,
                o,
            ) {
                assert forall|i: usize|
                    head < i < head + (1usize << o) implies #[trigger] new.spec_page_info(i)
                    == Some(PageInfo::Compound(CompoundInfo { order: o })) by {
                    assert(new.spec_page_info(i) === self.spec_page_info(i));
                }
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_reserved_info_content_lower_pfn(
        &self,
        new: Self,
        upper_pfn: usize,
        order: usize,
        pfn: usize,
    )
        requires
            0 <= order < N <= 64,
            self.wf_page_info(),
            self.wf_dom(),
            self.page_count() == new.page_count(),
            self.reserved.dom() === new.reserved.dom(),
            self.marked_order(upper_pfn, order),
            forall|p: usize|
                p < upper_pfn && 0 <= p < self.page_count() ==> #[trigger] self.spec_page_info(p)
                    === new.spec_page_info(p),
        ensures
            self.reserved_count() <= pfn < upper_pfn ==> new.wf_page_info_at(pfn),
    {
        reveal(ReservedPerms::wf_page_info);
        broadcast use lemma_bit_usize_shl_values;

        let size = 1usize << order;
        let pi = self.spec_page_info(pfn).unwrap();
        if self.reserved_count() <= pfn < upper_pfn {
            assert(new.spec_page_info(pfn).unwrap() === pi);
            assert(self.wf_page_info_at(pfn));
            let o = pi.get_order();
            let head = find_pfn_head(pfn, o);
            assert(self.wf_page_info_at(head));
            lemma_align_down_properties(pfn as int, (1usize << o) as int, head as int);
            if head + (1usize << o) <= upper_pfn && self.marked_compound(head, o) {
                assert forall|i: usize|
                    head < i < head + (1usize << o) implies #[trigger] new.spec_page_info(i)
                    == Some(PageInfo::Compound(CompoundInfo { order: o })) by {
                    assert(new.spec_page_info(i) === self.spec_page_info(i));
                }
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_marked_order(&self, pfn: usize, order: usize, p: usize)
        requires
            self.marked_order(pfn, order),
            self.wf_dom(),
        ensures
            (pfn <= p < pfn + (1usize << order)) ==> self.wf_page_info_at(p),
    {
        broadcast use lemma_bit_usize_shl_values;

        let size = 1usize << order;
        if pfn <= p < pfn + (1usize << order) {
            lemma_align_down_properties(p as int, size as int, pfn as int);
            assert(find_pfn_head(p, order) == pfn);
            let pi = self.spec_page_info(p);
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(2)]
    proof fn lemma_reserved_info_content_higher_pfn(
        &self,
        new: Self,
        lower_pfn: usize,
        order: usize,
        pfn: usize,
    )
        requires
            0 <= order < N <= 64,
            self.wf_page_info(),
            self.wf_dom(),
            self.page_count() == new.page_count(),
            self.reserved.dom() === new.reserved.dom(),
            self.marked_order(lower_pfn, order),
            forall|p: usize|
                lower_pfn + (1usize << order) <= p < self.page_count() ==> self.spec_page_info(p)
                    === #[trigger] new.spec_page_info(p),
        ensures
            (lower_pfn + (1usize << order) <= pfn < self.page_count()) ==> new.wf_page_info_at(pfn),
    {
        reveal(ReservedPerms::wf_page_info);
        broadcast use lemma_bit_usize_shl_values;

        let size = 1usize << order;
        let pi = self.spec_page_info(pfn).unwrap();
        assert(self.marked_order(lower_pfn, order));
        if (lower_pfn + size) <= pfn < self.page_count() {
            assert(new.spec_page_info(pfn).unwrap() === pi);
            assert(self.wf_page_info_at(pfn));
            let o = pi.get_order();
            let head = find_pfn_head(pfn, o);
            let s = (1usize << o);
            lemma_align_down_properties(pfn as int, s as int, head as int);
            if head + s <= self.page_count() && self.marked_compound(head, o) {
                assert forall|i: usize| head < i < head + s implies #[trigger] new.spec_page_info(i)
                    == Some(PageInfo::Compound(CompoundInfo { order: o })) by {
                    assert(new.spec_page_info(i) === self.spec_page_info(i));
                }
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_reserved_info_update(&self, new: Self, pfn: usize, order: usize)
        requires
            0 <= order < N <= 64,
            self.wf_page_info(),
            self.wf_dom(),
            new.wf_dom(),
            new.page_count() === self.page_count(),
            self.reserved.dom() === new.reserved.dom(),
            self.marked_order(pfn, order),
            new.reserved =~= self.reserved.union_prefer_right(
                new.reserved.restrict(set_int_range(pfn as int, (1usize << order) + pfn)),
            ),
            new.marked_order(pfn, order),
        ensures
            new.wf_page_info(),
    {
        reveal(ReservedPerms::wf_page_info);
        assert forall|p: usize|
            new.reserved_count() <= p < new.page_count() implies new.wf_page_info_at(p) by {
            assert(self.wf_page_info_at(p));
            let pinfo = new.spec_page_info(p).unwrap();
            self.lemma_reserved_info_content_lower_pfn(new, pfn, order, p);
            self.lemma_reserved_info_content_higher_pfn(new, pfn, order, p);
            new.lemma_marked_order(pfn, order, p);
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(4)]
    proof fn lemma_reserved_info_merge(&self, new: Self, pfn: usize, order: usize)
        requires
            0 <= order < N - 1,
            N <= 64,
            self.wf_page_info(),
            self.wf_dom(),
            self.marked_order(pfn, order),
            new.page_count() === self.page_count(),
            self.reserved.dom() === new.reserved.dom(),
            new.wf_dom(),
            self.marked_order((pfn + (1usize << order)) as usize, order),
            new.reserved =~= self.reserved.union_prefer_right(
                new.reserved.restrict(set_int_range(pfn as int, (1usize << (order + 1)) + pfn)),
            ),
            new.marked_order(pfn, (order + 1) as usize),
        ensures
            new.wf_page_info(),
    {
        reveal(ReservedPerms::wf_page_info);
        let size = (1usize << order);
        let new_order = (order + 1) as usize;
        let pfn2 = (pfn + size) as usize;
        broadcast use lemma_bit_usize_shl_values;

        self.page_count.lemma_valid_pfn_order_split(pfn, new_order);
        assert(new.wf_page_info_at(pfn));
        assert forall|p: usize|
            new.reserved_count() <= p < new.page_count() implies new.wf_page_info_at(p) by {
            assert(self.wf_page_info_at(p));
            let pinfo = new.spec_page_info(p).unwrap();
            self.lemma_reserved_info_content_lower_pfn(new, pfn, order, p);
            self.lemma_reserved_info_content_higher_pfn(new, pfn2, order, p);
            new.lemma_marked_order(pfn, new_order, p);
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(5)]
    proof fn lemma_reserved_info_split(&self, new: Self, pfn: usize, order: usize)
        requires
            0 < order < N <= 64,
            self.wf_page_info(),
            self.wf_dom(),
            new.wf_dom(),
            self.marked_order(pfn, order),
            self.reserved.dom() == new.reserved.dom(),
            new.reserved =~= self.reserved.union_prefer_right(
                new.reserved.restrict(set_int_range(pfn as int, (1usize << order) + pfn)),
            ),
            new.page_count() === self.page_count(),
            new.marked_order(pfn, (order - 1) as usize),
            new.marked_order((pfn + (1usize << (order - 1))) as usize, (order - 1) as usize),
        ensures
            new.wf_page_info(),
    {
        reveal(ReservedPerms::wf_page_info);
        broadcast use lemma_bit_usize_shl_values;

        let new_order = (order - 1) as usize;
        let size = 1usize << order;
        let new_size = 1usize << new_order;
        let pfn2 = (pfn + new_size) as usize;
        self.page_count.lemma_valid_pfn_order_split(pfn, order);
        assert(new.wf_page_info_at(pfn));
        assert(new.wf_page_info_at(pfn2));
        assert forall|p: usize|
            (p < pfn || p >= pfn + size) && 0 <= p
                < self.page_count() implies #[trigger] self.spec_page_info(p)
            === new.spec_page_info(p) && self.spec_page_info(p).is_some() by {
            assert(self.reserved[p as int] === new.reserved[p as int]);
        }
        assert forall|p: usize|
            new.reserved_count() <= p < new.page_count() implies new.wf_page_info_at(p) by {
            assert(self.wf_page_info_at(p));
            let pinfo = new.spec_page_info(p).unwrap();
            self.lemma_reserved_info_content_lower_pfn(new, pfn, order, p);
            self.lemma_reserved_info_content_higher_pfn(new, pfn, order, p);
            new.lemma_marked_order(pfn, new_order, p);
            new.lemma_marked_order(pfn2, new_order, p);
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(4)]
    broadcast proof fn lemma_reserved_info_remove(
        &self,
        new: Self,
        pfn: usize,
        prev_pfn: usize,
        order: usize,
    )
        requires
            0 <= order < N <= 64,
            self.wf_page_info(),
            self.wf_dom(),
            new.wf_dom(),
            prev_pfn >= pfn + (1usize << order) || pfn >= prev_pfn + (1usize << order),
            self.marked_order(pfn, order),
            self.valid_pfn_order(pfn, order),
            self.marked_order(prev_pfn, order),
            self.valid_pfn_order(prev_pfn, order),
            new.page_count() === self.page_count(),
            self.reserved.dom() === new.reserved.dom(),
            #[trigger] self.ens_allocate_pfn(new, pfn, prev_pfn, order),
        ensures
            new.wf_page_info(),
    {
        reveal(ReservedPerms::wf_page_info);
        broadcast use lemma_bit_usize_shl_values;

        assert forall|p: usize|
            (p != pfn) && p != prev_pfn && 0 <= p
                < self.page_count() implies #[trigger] self.spec_page_info(p)
            === new.spec_page_info(p) && self.spec_page_info(p).is_some() by {
            assert(self.reserved[p as int] === new.reserved[p as int]);
        }
        assert forall|p: usize|
            new.reserved_count() <= p < new.page_count() implies new.wf_page_info_at(p) by {
            assert(self.wf_page_info_at(p));
            let pinfo = new.spec_page_info(p).unwrap();
            let (pfn1, pfn2) = if pfn < prev_pfn {
                (pfn, prev_pfn)
            } else {
                (prev_pfn, pfn)
            };
            self.lemma_reserved_info_content_lower_pfn(new, pfn1, order, p);
            self.lemma_reserved_info_content_higher_pfn(new, pfn2, order, p);
            self.lemma_reserved_info_content_inner_pfn(new, pfn1, order, pfn2, order, p);
            new.lemma_marked_order(pfn, order, p);
        }
    }
}

impl<const N: usize> PageCountParam<N> {
    #[verifier::spinoff_prover]
    proof fn lemma_valid_pfn_order_no_overlap(&self, pfn1: usize, pfn2: usize, order: usize)
        requires
            self.valid_pfn_order(pfn1, order),
            self.valid_pfn_order(pfn2, order),
            pfn1 != pfn2,
            N <= 64,
        ensures
            pfn1 <= pfn2 - (1usize << order) || pfn2 <= pfn1 - (1usize << order),
    {
        broadcast use lemma_bit_usize_shl_values;

        let size = (1usize << order);
        assert(pfn1 % size == 0);
        assert(pfn2 % size == 0);
        assert(pfn1 <= pfn2 - size || pfn2 <= pfn1 - size) by (nonlinear_arith)
            requires
                pfn1 % size == 0,
                pfn2 % size == 0,
                size > 0,
                pfn1 != pfn2,
        ;
    }

    #[verifier::spinoff_prover]
    proof fn lemma_valid_pfn_order_split(&self, pfn: usize, order: usize)
        requires
            self.valid_pfn_order(pfn, order),
            0 < order < N <= 64,
        ensures
            self.valid_pfn_order(pfn, (order - 1) as usize),
            self.valid_pfn_order(
                (pfn + (1usize << (order - 1) as usize)) as usize,
                (order - 1) as usize,
            ),
    {
        broadcast use lemma_bit_usize_shl_values;

        let n = 1usize << order;
        let lower_n = 1usize << (order - 1) as usize;
        assert(1usize << order == 2 * (1usize << (order - 1) as usize)) by (bit_vector)
            requires
                0 < order < 64,
        ;
        if self.valid_pfn_order(pfn, order) && order > 0 {
            verify_proof::nonlinear::lemma_modulus_product_divisibility(
                pfn as int,
                lower_n as int,
                2,
            );
        }
        lemma_add_mod_noop(pfn as int, lower_n as int, lower_n as int);
        lemma_mod_self_0(lower_n as int);
        lemma_small_mod(0, lower_n as nat);
        assert((pfn + lower_n) % lower_n as int == 0);
    }
}

impl<const N: usize> MemoryRegionTracked<N> {
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
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                size as int,
                idx as int,
                1,
            );
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
        reveal(MemoryRegionTracked::free_dom);
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

        reveal(MemoryRegionTracked::free_dom);
        assert(1usize << order >= 1) by {
            broadcast use lemma_bit_usize_shl_values;

        }
        self.lemma_free_order_dom_subset(order);
        self.lemma_free_order_dom_rec(order, self.next[order as int].len());
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(4)]
    proof fn lemma_wf_info_after_remove(&self, new: Self, order: usize, idx: int)
        requires
            self.wf(),
            new.free_perms().wf(),
            new.reserved().wf_page_info(),
            0 <= order < N,
            idx < self.next[order as int].len() - 1,
            0 <= idx < self.next[order as int].len(),
            new.next === self.next.update(order as int, new.next[order as int]),
            new.next[order as int] === self.next[order as int].remove(idx),
            self.reserved().ens_allocate_pfn(
                new.reserved(),
                self.next[order as int][idx],
                self.next[order as int][idx + 1],
                order,
            ),
            new.reserved().spec_page_info(self.next[order as int][idx + 1]) === Some(
                PageInfo::Free(
                    FreeInfo {
                        next_page: self.reserved().spec_page_info(
                            self.next[order as int][idx],
                        ).unwrap().get_free().unwrap().next_page,
                        order,
                    },
                ),
            ),
        ensures
            new.wf_info(),
    {
        reveal(FreePerms::wf);
        assert(self.next[order as int].len() == new.next[order as int].len() + 1);
        assert forall|o, i| 0 <= o < N && 0 <= i < new.next[o].len() implies new.wf_at(o, i) by {
            assert(self.wf_at(o, i));
            assert(new.free_perms().wf_at(o, i));
            if i + 1 < self.next[o].len() {
                assert(self.wf_at(o, i + 1));
            }
            if o != order || i < idx {
                self.lemma_unique_pfn(o, i, order as int, idx);
                self.lemma_unique_pfn(o, i, order as int, idx + 1);
            } else if i >= idx + 1 {
                self.lemma_unique_pfn(o, i + 1, order as int, idx);
                self.lemma_unique_pfn(o, i + 1, order as int, idx + 1);
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_next_index_of(&self, pfn: usize, order: usize, i: int)
        requires
            self.wf(),
            0 <= order < N,
            0 <= i < self.next[order as int].len(),
        ensures
            self.next[order as int][i] == pfn ==> self.next[order as int].index_of(pfn) == i,
    {
        let next = self.next[order as int];
        //self.lemma_next_no_duplicate(order as int);
        let idx = next.index_of(pfn);
        if self.next[order as int][i] == pfn {
            assert(next[i] == pfn);
            assert(next[idx] == pfn);
        }
    }

    /// Unique Memory Ranges
    /// For any pair of pfn range (r1, r2) in free list ==> r1.disjoint(r2)
    #[verifier::spinoff_prover]
    broadcast proof fn lemma_unique_pfn(&self, o1: int, i1: int, o2: int, i2: int)
        requires
            self.wf(),
            !((o1, i1) === (o2, i2)),
            0 <= o1 < N,
            0 <= o2 < N,
            0 <= i1 < self.next[o1].len(),
            0 <= i2 < self.next[o2].len(),
        ensures
            (#[trigger] self.next[o1][i1] + (1usize << o1 as usize) <= #[trigger] self.next[o2][i2])
                || (self.next[o2][i2] + (1usize << o2 as usize) <= self.next[o1][i1]),
            self.next[o1][i1] != self.next[o2][i2],
            N <= 64 ==> self.free_dom_at(o1 as usize, i1).disjoint(
                self.free_dom_at(o2 as usize, i2),
            ),
    {
        let perms = *self;
        broadcast use lemma_bit_usize_shl_values;

        let n1 = (1usize << o1 as usize);
        let n2 = (1usize << o2 as usize);
        let pfn1 = perms.next[o1][i1];
        let pfn2 = perms.next[o2][i2];
        assert(perms.wf_at(o1, i1));
        assert(perms.wf_at(o2, i2));
        lemma_int_range_disjoint(pfn1 as int, pfn1 + n1, pfn2 as int, pfn2 + n2)
    }

    #[verifier::spinoff_prover]
    proof fn tracked_new(
        virt_start: VirtAddr,
        phys_start: PhysAddr,
        tracked is_exposed: IsExposed,
    ) -> (tracked ret: MemoryRegionTracked<N>)
        requires
            is_exposed@ == allocator_provenance(),
            virt_start.is_canonical(),
        ensures
            ret.wf(),
            ret.avail === Map::empty(),
            ret.reserved === Map::empty(),
            ret.map.size == 0,
            ret.next === Seq::new(N as nat, |k| Seq::empty()),
    {
        virt_start.property_canonical();
        let tracked ret = MemoryRegionTracked {
            avail: Map::tracked_empty(),
            reserved: Map::tracked_empty(),
            next: Seq::new(N as nat, |k| Seq::empty()),
            map: LinearMap::spec_new(virt_start, virt_start, phys_start),
            is_exposed,
        };
        assert(ret.reserved.dom() =~= set_int_range(0, 0));
        reveal(ReservedPerms::wf_page_info);
        ret
    }

    spec fn ens_remove(&self, new: Self, order: int, idx: int, ret: RawPerm) -> bool {
        let next = self.next.update(order, self.next[order].remove(idx));
        let expected = MemoryRegionTracked { next, avail: new.avail, ..*self };
        let pfn = self.next[order][idx];
        &&& new === expected
        &&& ret.wf_pfn_order(self.map, pfn, order as usize)
        &&& (idx == self.next[order].len() - 1) ==> new.next_page(order) == self.next_next_page(
            order,
        )
        &&& new.next_pages() === self.next_pages().update(order, new.next_page(order) as usize)
        &&& new.free_page_counts() === self.free_page_counts().update(
            order,
            (self.free_page_counts()[order] - 1) as nat,
        )
        &&& self.inv_remove_pfn(new)
        &&& self.reserved() === new.reserved()
    }

    #[verifier::spinoff_prover]
    proof fn tracked_remove(tracked &mut self, order: int, idx: int) -> (tracked ret: RawPerm)
        requires
            0 <= order < N,
            old(self).wf_perms() || old(self).wf(),
            old(self).page_count() > 0,
            0 <= idx < old(self).next[order].len(),
        ensures
            self.wf_perms(),
            old(self).ens_remove(*self, order, idx, ret),
    {
        reveal(FreePerms::wf);
        assert(self.wf_perms()) by {
            broadcast use lemma_wf_perms;

        };
        let old_self = *self;
        assert(self.wf_freep(order, idx));
        let len = self.next[order].len();
        let m = Map::new(
            |k: (int, int)| self.avail.dom().contains(k) && k != (order, len - 1),
            |k: (int, int)|
                if k.0 == order && k.1 >= idx {
                    (k.0, k.1 + 1)
                } else {
                    k
                },
        );
        let tracked perm = self.avail.tracked_remove((order, idx));
        self.avail.tracked_map_keys_in_place(m);
        self.next = self.next.update(order, self.next[order].remove(idx));

        assert(self.next[order].len() == old_self.next[order].len() - 1);
        let next = self.next;
        assert forall|o, i| 0 <= o < N && 0 <= i < next[o].len() implies self.wf_freep(o, i) by {
            assert(old_self.wf_freep(o, i));
            if o == order && i >= idx {
                assert(old_self.wf_freep(o, i + 1));
                assert(self.avail[(o, i)] === old(self).avail[(o, i + 1)]);
                assert(self.next[o][i] === old(self).next[o][i + 1]);
                assert(self.wf_freep(o, i));
            } else {
                assert(self.avail[(o, i)] === old(self).avail[(o, i)]);
                assert(self.wf_freep(o, i));
            }
        }
        assert(self.free_page_counts()[order] == self.next[order].len());
        assert(self.wf_perms());
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

    #[verifier::spinoff_prover]
    proof fn tracked_pop_next(tracked &mut self, order: usize) -> (tracked ret: RawPerm)
        requires
            0 <= order < N,
            old(self).wf(),
            old(self).page_count() > 0,
            old(self).next[order as int].len() > 0,
        ensures
            old(self).ens_remove(*self, order as int, old(self).next[order as int].len() - 1, ret),
            self.wf(),
    {
        broadcast use lemma_wf_perms;

        let order = order as int;
        let tracked p = self.tracked_remove(order, self.next[order].len() - 1);
        let next = self.next;
        assert forall|o, i| 0 <= o < N && 0 <= i < next[o].len() implies self.wf_at(o, i) by {
            assert(old(self).wf_at(o, i));
            assert(self.wf_freep(o, i));
        }
        p
    }

    #[verifier::spinoff_prover]
    proof fn tracked_push(tracked &mut self, order: usize, pfn: usize, tracked perm: RawPerm)
        requires
            0 <= order < old(self).next.len(),
            old(self).wf_perms() || old(self).wf(),
            old(self).valid_pfn_order(pfn, order),
            perm.wf_pfn_order(old(self).map, pfn, order as usize),
            pfn >= old(self).reserved_pfn_count(),
        ensures
            self.wf_perms(),
            self.next[order as int] == old(self).next[order as int].push(pfn),
            self.next == old(self).next.update(order as int, self.next[order as int]),
            self.reserved() == old(self).reserved(),
            self.map == old(
                self,
            ).map,
    //self.avail[(order as int, old(self).next[order as int].len() as int)] === perm,
    //self.avail === old(self).avail.insert(
    //    (order as int, old(self).next[order as int].len() as int),
    //    perm,
    //),

    {
        assert(self.wf_perms()) by {
            broadcast use lemma_wf_perms;

        };
        let order = order as int;
        let idx = self.next[order].len() as int;
        self.avail.tracked_insert((order, idx), perm);
        self.next = self.next.update(order, self.next[order].push(pfn));
        assert(self.wf_freep(order, idx));
        assert forall|o, i|
            0 <= o < N && 0 <= i < self.next[o].len() implies #[trigger] self.wf_freep(o, i) by {
            if i < old(self).next[o].len() {
                assert(old(self).wf_freep(o, i))
            } else {
                assert(o == order);
                assert(i == idx);
            }
        }
    }
}

#[verifier::spinoff_prover]
broadcast proof fn lemma_wf_next_page_info(mr: MemoryRegion, order: int)
    requires
        mr.wf(),
        0 <= order < MAX_ORDER,
    ensures
        #![trigger mr.next_page[order]]
        mr@.wf_next(order),
        mr.next_page[order] == 0 || mr.next_page[order] < mr.page_count,
        (mr.next_page[order] == 0) == (mr.free_pages[order] == 0),
        //(mr@.next_next_page(order) == 0) ==> (mr.free_pages[order] <= 1),
        mr.free_pages[order] == mr@.next[order].len(),
{
    let perms = mr@;
    let i = perms.next[order].len() - 1;
    if i < 0 {
        assert(mr@.next_page(order) == 0);
    } else {
        assert(perms.wf_at(order, i));
        assert(perms.next_page(order) > 0);
    }
    assert(mr.free_pages[order] == perms.free_page_counts()[order]);
    assert(perms.free_page_counts()[order] == perms.next[order].len());
    if i > 0 {
        assert(perms.wf_at(order, i - 1));
        assert(mr@.next_next_page(order) > 0);
    } else {
        assert(perms.next[order].len() <= 1);
        assert(mr@.next_next_page(order) == 0);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_ens_has_free_pages_pages(mr: MemoryRegion, order: int)
    requires
        mr.spec_alloc_fails(order),
        0 <= order < MAX_ORDER - 1,
    ensures
        !mr.spec_alloc_fails(order + 1) ==> !mr.spec_alloc_fails(order),
        (mr.spec_alloc_fails(order + 1) && mr.next_page[order] == 0) ==> mr.spec_alloc_fails(order),
{
}

#[verifier::spinoff_prover]
broadcast proof fn lemma_wf_perms<const N: usize>(m: MemoryRegionTracked<N>)
    requires
        m.wf(),
    ensures
        #[trigger] m.wf_perms(),
{
    let l = m.next;
    assert forall|o, i| 0 <= o < N && 0 <= i < l[o].len() implies #[trigger] m.wf_freep(o, i) by {
        assert(m.wf_at(o, i))
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(4)]
broadcast proof fn lemma_compound_neighbor(pfn: usize, order: usize, ret_pfn: usize)
    requires
        pfn % (1usize << order) == 0,
        pfn + (1usize << order) <= usize::MAX,
        ret_pfn == pfn ^ (1usize << order),
        0 <= order < 63,
    ensures
        (ret_pfn == pfn - (1usize << order)) ==> ret_pfn % (1usize << (order + 1)) == 0,
        #[trigger] MemoryRegion::ens_find_neighbor(pfn, order, ret_pfn),
{
    broadcast use lemma_bit_usize_shl_values;

    assert(pfn % (1usize << order) == 0);
    let n = 1usize << (order + 1);
    assert(1usize << (order + 1) == 2 * (1usize << order));
    lemma_bit_usize_and_mask_is_mod(pfn, ((1usize << order) - 1) as usize);
    lemma_bit_usize_and_mask_is_mod(pfn, ((1usize << (order + 1) as usize) - 1) as usize);
    lemma_bit_usize_xor_neighbor(pfn, order);
    lemma_modulus_add_sub_m(pfn as int, (1usize << order) as int);
    if ret_pfn == pfn - (1usize << order) {
        let x = pfn;
        let m = 1usize << order;
        if x as int % (2 * m) == 0 {
            assert(x & (2 * m - 1) as usize == 0);
            assert(x & (n - 1) as usize == 0);
            assert(x ^ m == sub(x, m));
        }
        assert(x as int % (2 * m) != 0);
        assert(((x - m) % (2 * m) == 0 && (x >= m || x <= -m)))
    }
}

impl MemoryRegion {
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

        reveal(<LinearMap as SpecMemMapTr>::to_paddr);

        assert(self.start_virt@ % 0x1000 == 0);
        assert(vaddr.offset() - self.start_virt.offset() == (vaddr.offset()
            - self.start_virt.offset()) / 0x1000 * 0x1000) by {
            vaddr.property_canonical();
            self.start_virt.property_canonical();
            assert(self.start_virt.offset() % 0x1000 == 0);
            broadcast use verify_proof::bits::lemma_bit_usize_not_is_sub;

        }
        self@.map.proof_one_to_one_mapping_vaddr(vaddr);
    }

    /*proof fn lemma_derive_contains_range(
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
    }*/
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
            (exists|pfn: usize| #[trigger] self@.marked_order(pfn, order))
                ==> self.nr_pages[order as int] >= 1,
            (exists|pfn: usize, pfn2: usize|
                pfn2 != pfn && #[trigger] self@.marked_order(pfn, order)
                    && #[trigger] self@.marked_order(pfn2, order)) ==> self.nr_pages[order as int]
                >= 1,
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

        self@.reserved().lemma_pfn_dom(order as usize);
        if exists|pfn: usize| #[trigger] self@.marked_order(pfn, order) {
            let pfn = choose|pfn: usize| #[trigger] self@.marked_order(pfn, order);
            self@.reserved().lemma_pfn_dom_len_with_one(pfn, order);
        }
        if exists|pfn: usize, pfn2: usize|
            pfn2 != pfn && #[trigger] self@.marked_order(pfn, order)
                && #[trigger] self@.marked_order(pfn2, order) {
            let (pfn1, pfn2) = choose|pfn: usize, pfn2: usize|
                pfn2 != pfn && #[trigger] self@.marked_order(pfn, order)
                    && #[trigger] self@.marked_order(pfn2, order);
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
}

} // verus!
