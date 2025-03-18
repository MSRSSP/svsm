// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// This file contains proofs for the allocator's invariants and correctness.
//
// Key Invariant to Prove:
// 1. PageInfo is consistent with the allocator state (MemoryRegioinTracked::wf)
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

global size_of PageStorageType == 8;

proof fn is_disjoint(tracked p1: &mut RawPerm, p2: &RawPerm)
    ensures
        *old(p1) == *p1,
        p1.dom().disjoint(p2.dom()),
{
    admit();
}

impl MemoryRegionTracked<VirtAddr, MAX_ORDER> {
    #[verifier::spinoff_prover]
    proof fn lemma_pfn_range_disjoint_rec1(
        tracked &self,
        mr: &MemoryRegion,
        tracked perm: &mut RawPerm,
        pfn: usize,
        order: usize,
        o: int,
        n: nat,
    )
        requires
            mr.wf(),
            mr@ == *self,
            old(perm).wf_vaddr_order(mr.spec_get_virt(pfn as int), order),
            self.valid_pfn_order(pfn, order),
            0 <= order < MAX_ORDER,
            0 <= o < MAX_ORDER,
            n <= self.next[o].len(),
        ensures
            forall|i|
                0 <= i < n ==> addr_order_disjoint(
                    #[trigger] self.next[o][i],
                    o as usize,
                    pfn,
                    order,
                ),
            *old(perm) == *perm,
        decreases n,
    {
        broadcast use lemma_bit_usize_shl_values;

        let next = self.next;
        if n > 0 {
            let i = n - 1;
            let p = self.next[o][i];
            let start1 = mr.spec_get_virt(pfn as int)@ as int;
            let end1 = start1 + (1usize << order);
            assert(self.wf_at(o, i));
            let pfn2 = self.next[o][i];
            let start2 = mr.spec_get_virt(pfn2 as int)@ as int;
            let end2 = start2 + (1usize << o);
            mr.map().lemma_get_virt(pfn);
            mr.map().lemma_get_virt(pfn2);
            let perm2 = self.avail.tracked_borrow((o, i));
            is_disjoint(perm, perm2);
            assert(perm.dom().contains(start1));
            assert(perm2.dom().contains(start2));
            assert(addr_order_disjoint(#[trigger] self.next[o][n - 1], o as usize, pfn, order));
            self.lemma_pfn_range_disjoint_rec1(mr, perm, pfn, order, o, (n - 1) as nat);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pfn_range_disjoint_rec2(
        tracked &self,
        mr: &MemoryRegion,
        tracked perm: &mut RawPerm,
        pfn: usize,
        order: usize,
        max_order: int,
    )
        requires
            mr.wf(),
            mr@ == *self,
            self.valid_pfn_order(pfn, order),
            old(perm).wf_vaddr_order(mr.spec_get_virt(pfn as int), order),
            0 <= order < MAX_ORDER,
            0 <= max_order <= MAX_ORDER,
        ensures
            forall|o, i|
                0 <= o < max_order && 0 <= i < self.next[o].len() ==> addr_order_disjoint(
                    #[trigger] self.next[o][i],
                    o as usize,
                    pfn,
                    order,
                ),
            *old(perm) == *perm,
        decreases max_order,
    {
        if max_order > 0 {
            let o = max_order - 1;
            self.lemma_pfn_range_disjoint_rec1(mr, perm, pfn, order, o, self.next[o].len());
            self.lemma_pfn_range_disjoint_rec2(mr, perm, pfn, order, max_order - 1);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_perm_not_in_allocator(
        tracked &self,
        mr: &MemoryRegion,
        tracked perm: &mut RawPerm,
        pfn: usize,
        order: usize,
    )
        requires
            mr.wf(),
            mr@ == *self,
            self.valid_pfn_order(pfn, order),
            #[trigger] old(perm).wf_vaddr_order(mr.spec_get_virt(pfn as int), order),
            0 <= order < MAX_ORDER,
        ensures
            self.pfn_range_is_allocated(pfn, order),
            *old(perm) == *perm,
    {
        self.lemma_pfn_range_disjoint_rec2(mr, perm, pfn, order, MAX_ORDER as int);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_tmp_perm_disjoint(
        tracked &self,
        mr: &MemoryRegion,
        tracked tmp_perms: &mut TrackedSeq<RawPerm>,
        pfn: usize,
        order: usize,
    )
        requires
            mr.wf(),
            mr@ == *self,
            self.valid_pfn_order(pfn, order),
            old(tmp_perms).len() > 0,
            old(tmp_perms).last().wf_vaddr_order(mr.spec_get_virt(pfn as int), order),
            0 <= order < MAX_ORDER,
        ensures
            self.pfn_range_is_allocated(pfn, order),
            *tmp_perms == *old(tmp_perms),
    {
        let tracked mut perm = tmp_perms.tracked_pop();
        self.lemma_perm_not_in_allocator(mr, &mut perm, pfn, order);
        tmp_perms.tracked_push(perm);
        assert(tmp_perms@ =~= old(tmp_perms)@);
    }
}

#[verifier::rlimit(4)]
proof fn tracked_merge(
    tracked tmp_perms: &mut TrackedSeq<RawPerm>,
    map: LinearMap,
    pfn1: usize,
    pfn2: usize,
    order: usize,
)
    requires
        map.wf(),
        old(tmp_perms)@.len() >= 2,
        0 <= order < 64,
        pfn1 == pfn2 + (1usize << order) || pfn2 == pfn1 + (1usize << order),
        old(tmp_perms)@.last().wf_pfn_order(map, pfn2, order),
        old(tmp_perms)@[old(tmp_perms)@.len() - 2].wf_pfn_order(map, pfn1, order),
    ensures
        tmp_perms@ =~= old(tmp_perms)@.take(old(tmp_perms)@.len() - 2).push(tmp_perms@.last()),
        tmp_perms@.last().wf_pfn_order(
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
    let tracked p2 = tmp_perms.tracked_pop();
    let tracked p1 = tmp_perms.tracked_pop();

    let tracked p = if pfn1 < pfn2 {
        assert(pfn2 == pfn1 + size);
        p1.join(p2)
    } else {
        assert(pfn1 == pfn2 + size);
        p2.join(p1)
    };
    tmp_perms.tracked_push(p);
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
            (#[trigger]self.pfn_dom(order1) + #[trigger]self.pfn_dom(order2)).subset_of(
                set_int_range(0, self.page_count() as int),
            ),
            self.pfn_dom(order1).len() + self.pfn_dom(order2).len() <= self.page_count(),
    {
        self.lemma_pfn_dom(order1);
        self.lemma_pfn_dom(order2);
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
            0 <= size <= 1usize << order,
            self.valid_pfn_order(pfn, order),
            forall|i: usize|
                pfn <= i < pfn + size ==> #[trigger] self.spec_page_info(i).unwrap().get_order()
                    == order,
        ensures
            self.pfn_dom(order).filter(|i| pfn <= i < pfn + size).len() == size,
            set_int_range(pfn as int, pfn + size).subset_of(self.pfn_dom(order)),
        decreases size,
    {
        let s = self.pfn_dom(order);
        let s1 = s.filter(|i| pfn <= i < pfn + size);
        if size > 0 {
            let s2 = s.filter(|i| pfn <= i < pfn + size - 1);
            self.lemma_marked_order_len_rec(pfn, order, size - 1);
            let s3 = set_int_range(pfn + size - 1, pfn + size);
            vstd::set_lib::lemma_int_range(pfn + size - 1, pfn + size);
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
            set_int_range(pfn as int, pfn + (1usize << order)).subset_of(self.pfn_dom(order)),
    {
        broadcast use lemma_bit_usize_shl_values;

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
    #[verifier::rlimit(10)]
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
    #[verifier::rlimit(10)]
    proof fn lemma_reserved_info_split(&self, new: Self, pfn: usize, order: usize)
        requires
            0 < order < N <= 64,
            self.wf_page_info(),
            self.wf_dom(),
            new.wf_dom(),
            self.marked_order(pfn, order),
            self.reserved.dom() === new.reserved.dom(),
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
            #[trigger] self.valid_pfn_order(pfn, order),
            0 < order < N <= 64,
        ensures
            self.valid_pfn_order(pfn, (order - 1) as usize),
            (pfn + (1usize << (order - 1) as usize)) % (1usize << (order - 1) as usize) as int == 0,
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

impl<VAddr: SpecVAddrImpl, const N: usize> MemoryRegionTracked<VAddr, N> {
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
    proof fn lemma_free_pfn_dom_finite(&self, order: int)
        requires
            0 <= order < self.next.len(),
        ensures
            self.free_pfn_dom(order).finite(),
    {
        let next = self.next[order];
        let size = 1usize << order;
        let dom_seq = self.free_pfn_dom_seq(order);
        assert forall|i| 0 <= i < next.len() implies (#[trigger] dom_seq[i]).finite()
            && dom_seq[i].len() == size by {
            vstd::set_lib::lemma_int_range(next[i] as int, next[i] + size);
        }
        lemma_sets_to_set_finite_iff(dom_seq);
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
        self.lemma_next_no_duplicate(order as int);
        let idx = next.index_of(pfn);
        if self.next[order as int][i] == pfn {
            assert(next[i] == pfn);
            assert(next[idx] == pfn);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_free_pfn_dom_len(&self, order: int)
        requires
            0 <= order < self.next.len(),
            seq_sets_are_disjoint(self.free_pfn_dom_seq(order)),
        ensures
            self.free_pfn_dom(order).len() == self.next[order].len() * (1usize << order),
    {
        let size = 1usize << order;
        let next = self.next[order];
        let dom_seq = self.free_pfn_dom_seq(order);
        self.lemma_free_pfn_dom_finite(order);
        assert forall|i| 0 <= i < next.len() implies (#[trigger] dom_seq[i]).finite()
            && dom_seq[i].len() == size by {
            vstd::set_lib::lemma_int_range(next[i] as int, next[i] + size);
        }
        lemma_sets_to_set_fixed_len(dom_seq, size as nat);
    }

    /// Mathematical Relationship between `page_count` and the allocator's page counter
    /// Size of free list
    /// for any pair r1: (pfn1, order1), r2: (pfn2, order2) of pfn range in free list ==> r1.disjoint(r2)
    #[verifier::spinoff_prover]
    proof fn lemma_free_pfn_dom_exclude(&self, order: int, pfn_set: Set<int>)
        requires
            self.wf(),
            self.free_pfn_dom(order).disjoint(pfn_set),
            pfn_set.finite(),
            pfn_set.subset_of(self.full_pfn_dom()),
            0 <= order < N <= 64,
        ensures
            self.next[order].len() * (1usize << order) + pfn_set.len() <= self.page_count()
                - self.reserved_pfn_count(),
            self.page_count() > 0 ==> self.next[order].len() < self.page_count(),
    {
        broadcast use lemma_bit_usize_shl_values, lemma_mul_ordering;

        let next = self.next[order];
        let free_dom = self.free_pfn_dom(order);

        self.pg_params().lemma_reserved_pfn_count();
        if self.page_count() > 0 {
            assert(self.reserved_pfn_count() > 0);
        }
        self.lemma_unique_pfn_auto(order);
        self.lemma_free_pfn_dom_finite(order);
        vstd::set_lib::lemma_set_disjoint_lens(free_dom, pfn_set);
        vstd::set_lib::lemma_set_union_finite_iff(free_dom, pfn_set);
        vstd::set_lib::lemma_int_range(self.reserved_pfn_count() as int, self.page_count() as int);
        self.lemma_free_pfn_is_subset_of_full(order);
        vstd::set_lib::lemma_len_subset(free_dom.union(pfn_set), self.full_pfn_dom());
        self.lemma_free_pfn_dom_len(order);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_unique_pfn_auto(&self, order: int)
        requires
            self.wf(),
            0 <= order < N <= 64,
        ensures
            seq_sets_are_disjoint(self.free_pfn_dom_seq(order)),
    {
        let next = self.next[order];
        let size = 1usize << order;
        assert forall|i, j|
            #![trigger next[i], next[j]]
            0 <= i < j < next.len() implies set_int_range(next[i] as int, next[i] + size).disjoint(
            set_int_range(next[j] as int, next[j] + size),
        ) by { self.lemma_unique_pfn(order, i, order, j) }
    }

    /// Unique Memory Ranges
    /// For any pair of pfn range (r1, r2) in free list ==> r1.disjoint(r2)
    #[verifier::spinoff_prover]
    proof fn lemma_unique_pfn(&self, o1: int, i1: int, o2: int, i2: int)
        requires
            self.wf(),
            !((o1, i1) === (o2, i2)),
            0 <= o1 < N,
            0 <= o2 < N,
            0 <= i1 < self.next[o1].len(),
            0 <= i2 < self.next[o2].len(),
        ensures
            (self.next[o1][i1] + (1usize << o1 as usize) <= self.next[o2][i2]) || (self.next[o2][i2]
                + (1usize << o2 as usize) <= self.next[o1][i1]),
            self.next[o1][i1] != self.next[o2][i2],
            N <= 64 ==> self.free_pfn_dom_at(o1, i1).disjoint(self.free_pfn_dom_at(o2, i2)),
    {
        let perms = *self;
        broadcast use lemma_bit_usize_shl_values;

        lemma_unique_pfn_start(perms, o1, i1, o2, i2);
        let n1 = (1usize << o1 as usize);
        let n2 = (1usize << o2 as usize);
        let pfn1 = perms.next[o1][i1];
        let pfn2 = perms.next[o2][i2];
        assert(perms.wf_at(o1, i1));
        assert(perms.wf_at(o2, i2));
        let next_pfn1 = if i1 > 0 {
            perms.next[o1][i1 - 1]
        } else {
            0usize
        };
        let next_pfn2 = if i2 > 0 {
            perms.next[o2][i2 - 1]
        } else {
            0usize
        };
        assert(perms.marked_free(pfn1, o1 as usize, next_pfn1));
        assert(perms.marked_free(pfn2, o2 as usize, next_pfn2));
        let c1 = Some(PageInfo::Compound(CompoundInfo { order: o1 as usize }));
        let c2 = Some(PageInfo::Compound(CompoundInfo { order: o2 as usize }));
        assert(perms.spec_page_info(pfn1 as int) !== c2);
        assert(perms.spec_page_info(pfn2 as int) !== c1);
        lemma_int_range_disjoint(pfn1 as int, pfn1 + n1, pfn2 as int, pfn2 + n2)
    }

    #[verifier::spinoff_prover]
    proof fn lemma_free_pfn_is_subset_of_full(&self, order: int)
        requires
            self.wf(),
            0 <= order < N,
        ensures
            self.free_pfn_dom(order).subset_of(self.full_pfn_dom()),
    {
        let next_page = self.next[order];
        let size = 1usize << order;
        assert forall|pfn: int| #[trigger]
            self.free_pfn_dom(order).contains(pfn) implies self.full_pfn_dom().contains(pfn) by {
            let s = self.free_pfn_dom_seq(order);
            lemma_sets_to_set_contains(s, pfn);
            let i = choose|i: int| 0 <= i < next_page.len() && #[trigger] s[i].contains(pfn);
            assert(s[i].contains(pfn));
            assert(self.wf_at(order, i));
        };
    }

    #[verifier::spinoff_prover]
    proof fn lemma_next_no_duplicate(&self, order: int)
        requires
            self.wf(),
            0 <= order < N,
        ensures
            self.next[order].no_duplicates(),
            self.next[order].to_set().len() == self.next[order].len(),
    {
        let next_page = self.next[order];
        assert(next_page.no_duplicates()) by {
            lemma_unique_pfn_same_order(*self, order, next_page.len() as int);
        }
        next_page.unique_seq_to_set()
    }

    #[verifier::spinoff_prover]
    proof fn tracked_new() -> (tracked ret: MemoryRegionTracked<VAddr, N>)
        ensures
            ret.wf(),
            ret.avail === Map::empty(),
            ret.reserved === Map::empty(),
            ret.pfn_to_virt === Seq::empty(),
            ret.next === Seq::new(N as nat, |k| Seq::empty()),
    {
        let tracked ret = MemoryRegionTracked {
            avail: Map::tracked_empty(),
            reserved: Map::tracked_empty(),
            next: Seq::new(N as nat, |k| Seq::empty()),
            pfn_to_virt: Seq::empty(),
        };
        assert(ret.reserved.dom() =~= set_int_range(0, 0));
        reveal(ReservedPerms::wf_page_info);
        ret
    }

    spec fn ens_remove(&self, new: Self, order: int, idx: int, ret: RawPerm) -> bool {
        let next = self.next.update(order, self.next[order].remove(idx));
        let expected = MemoryRegionTracked { next, avail: new.avail, ..*self };
        let pfn = self.next[order][idx] as int;
        &&& new === expected
        &&& ret.wf_vaddr_order(self.pfn_to_virt[pfn].vaddr, order as usize)
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
            perm.wf_vaddr_order(old(self).pfn_to_virt[pfn as int].vaddr, order as usize),
            pfn >= old(self).reserved_pfn_count(),
        ensures
            self.wf_perms(),
            self.next[order as int].last() == pfn,
            self.next[order as int] === old(self).next[order as int].push(pfn),
            self.next === old(self).next.update(order as int, self.next[order as int]),
            self.reserved() === old(self).reserved(),
            self.pfn_to_virt === old(self).pfn_to_virt,
            self.avail[(order as int, old(self).next[order as int].len() as int)] === perm,
            self.avail === old(self).avail.insert(
                (order as int, old(self).next[order as int].len() as int),
                perm,
            ),
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
        mr.next_page[order] > 0 ==> mr@.wf_next(order),
        mr.next_page[order] == 0 || mr.next_page[order] < mr.page_count,
        (mr@.next_page(order) == 0) == (mr.free_pages[order] == 0),
        (mr@.next_next_page(order) == 0) ==> (mr.free_pages[order] <= 1),
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
broadcast proof fn lemma_wf_perms<VAddr: SpecVAddrImpl, const N: usize>(
    m: MemoryRegionTracked<VAddr, N>,
)
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
proof fn lemma_unique_pfn_same_order<VAddr: SpecVAddrImpl, const N: usize>(
    perms: MemoryRegionTracked<VAddr, N>,
    order: int,
    n: int,
)
    requires
        perms.wf(),
        0 <= order < N,
        0 <= n <= perms.next[order].len(),
    ensures
        forall|i1, i2| 0 <= i1 < i2 < n ==> perms.next[order][i1] != perms.next[order][i2],
    decreases n,
{
    if n == 2 {
        let i1 = n - 2;
        let i2 = n - 1;
        let pfn1 = perms.next[order][i1];
        let pfn2 = perms.next[order][i2];
        let pi1 = perms.get_free_info(pfn1 as int);
        let pi2 = perms.get_free_info(pfn2 as int);
        assert(perms.wf_at(order, i1));
        assert(perms.wf_at(order, i2));
        assert(pi2.unwrap().next_page == pfn1);
    } else if n > 2 {
        lemma_unique_pfn_same_order(perms, order, n - 1);
        assert forall|i1, i2| 0 <= i1 < i2 < n implies perms.next[order][i1]
            != perms.next[order][i2] by {
            let pfn1 = perms.next[order][i1];
            let pfn2 = perms.next[order][i2];
            let pfn1_next = perms.next[order][i1 - 1];
            let pfn2_next = perms.next[order][i2 - 1];
            let pi1 = perms.get_free_info(pfn1 as int);
            let pi2 = perms.get_free_info(pfn2 as int);
            assert(perms.wf_at(order, i1));
            assert(perms.wf_at(order, i2));
            assert(perms.wf_at(order, i2 - 1));
            if i2 == n - 1 {
                assert(pi2.unwrap().next_page == pfn2_next);
                if i1 > 0 {
                    assert(pi1.unwrap().next_page == pfn1_next);
                } else {
                    assert(pi1.unwrap().next_page == 0);
                }
                if pfn1 == pfn2 {
                    assert(pfn1_next == pfn2_next);
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_unique_pfn_start<VAddr: SpecVAddrImpl, const N: usize>(
    perms: MemoryRegionTracked<VAddr, N>,
    o1: int,
    i1: int,
    o2: int,
    i2: int,
)
    requires
        perms.wf(),
        !((o1, i1) === (o2, i2)),
        0 <= o1 < N,
        0 <= o2 < N,
        0 <= i1 < perms.next[o1].len(),
        0 <= i2 < perms.next[o2].len(),
    ensures
        perms.next[o1][i1] != perms.next[o2][i2],
{
    let pfn1 = perms.next[o1][i1];
    let pfn2 = perms.next[o2][i2];
    assert(perms.wf_at(o1, i1));
    assert(perms.wf_at(o2, i2));
    let pi1 = perms.get_free_info(pfn1 as int);
    let pi2 = perms.get_free_info(pfn2 as int);
    if o1 != o2 {
        assert(pi1.unwrap().order == o1);
        assert(pi2.unwrap().order == o2);
        assert(pfn1 != pfn2);
    } else {
        lemma_unique_pfn_same_order(perms, o1, perms.next[o1].len() as int);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_valid_pfn_order_merge(mr: MemoryRegion, pfn: usize, order: usize)
    requires
        #[trigger] mr.valid_pfn_order(pfn, order),
    ensures
        ((pfn % (1usize << (order + 1) as usize) == 0) && (pfn + (1usize << (order + 1) as usize)
            <= mr.page_count)) ==> (pfn + (1usize << order)) % (1usize << order) as int == 0,
        (pfn % (1usize << (order + 1) as usize) != 0) && (order + 1) < MAX_ORDER ==> (pfn - (1usize
            << order)) % (1usize << (order + 1) as usize) as int == 0,
{
    broadcast use lemma_bit_usize_shl_values;

    let n = 1usize << order;
    let m = 1usize << (order + 1) as usize;
    assert(2 * (1usize << order) == 1usize << (order + 1) as usize) by (bit_vector)
        requires
            order < 63,
    ;
    assert(m == n + n);

    verify_proof::nonlinear::lemma_modulus_add_sub_m(pfn as int, n as int);
    assert((pfn + n) % n as int == 0);
    if pfn % m != 0 {
        assert((pfn - n) % m as int == 0);
        assert(pfn - n >= 0);
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

} // verus!
