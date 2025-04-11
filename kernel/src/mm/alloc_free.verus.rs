verus! {

use vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way;

tracked struct MRFreePerms {
    tracked avail: Map<(usize, int), RawPerm>,  //(order, idx) -> perm
    ghost next: Seq<Seq<usize>>,  // order -> next page list
    ghost map: LinearMap,  // pfn -> virt address
    ghost page_count: PageCountParam<MAX_ORDER>,
}

proof fn raw_perm_order_disjoint(
    map: LinearMap,
    pfn1: usize,
    o1: usize,
    pfn2: usize,
    o2: usize,
    tracked p1: &mut RawPerm,
    tracked p2: &RawPerm,
)
    requires
        old(p1).wf_pfn_order(map, pfn1, o1),
        p2.wf_pfn_order(map, pfn2, o2),
    ensures
        order_disjoint(pfn1, o1, pfn2, o2),
        *old(p1) == *p1,
{
    let vaddr1 = map.lemma_get_virt(pfn1);
    let vaddr2 = map.lemma_get_virt(pfn2);
    let size1 = ((1usize << o1) * PAGE_SIZE) as nat;
    let size2 = ((1usize << o2) * PAGE_SIZE) as nat;
    vaddr1.lemma_vaddr_region_len(size1);
    vaddr2.lemma_vaddr_region_len(size2);
    raw_perm_is_disjoint(p1, p2);
    reveal(<VirtAddr as SpecVAddrImpl>::region_to_dom);
    assert(p1.dom().contains(vaddr1@ as int));
    assert(p2.dom().contains(vaddr2@ as int));
}

proof fn lemma_order_disjoint_len(s: Seq<usize>, o: usize, max_count: usize)
    requires
        o < MAX_ORDER,
        // s has a upper bound
        forall|i| #![trigger s[i]] 0 <= i < s.len() ==> s[i] < max_count,
        // s is order-disjoint
        forall|i, j|
            #![trigger s[i], s[j]]
            0 <= i < s.len() && 0 <= j < s.len() && i != j ==> order_disjoint(s[i], o, s[j], o),
    ensures
        s.len() * (1usize << o) <= max_count + (1usize << o) - 1,
        s.len() <= max_count,
    decreases s.len(),
{
    let gap = (1usize << o);
    let int_s = s.map_values(|x| x as int);
    assert(int_s.len() == s.len());
    if s.len() > 1 {
        int_s.max_ensures();
        let idx = choose|i| 0 <= i < int_s.len() && int_s[i] == int_s.max();
        assert(int_s[idx] == int_s.max());
        assert(s.remove(idx).len() < s.len());
        assert forall|i| #![trigger s[i]] 0 <= i < s.len() && i != idx implies s[i] < max_count
            - gap by {
            assert(s[idx] <= max_count);
            assert(int_s[i] <= int_s[idx]);
            assert(s[i] <= s[idx]);
            assert(order_disjoint(s[i], o, s[idx], o));
        }
        let s2 = s.remove(idx);
        if idx > 0 {
            assert(order_disjoint(s[idx], o, s[idx - 1], o));
        } else {
            assert(order_disjoint(s[idx], o, s[idx + 1], o));
        }
        assert(max_count >= gap);
        lemma_order_disjoint_len(s2, o, (max_count - gap) as usize);
        assert(s2.len() <= max_count - gap);
        assert(s2.len() * gap <= max_count - 1);
        assert(s.len() == s2.len() + 1);
        assert(s.len() * gap == s2.len() * gap + 1 * gap) by {
            lemma_mul_is_distributive_add_other_way(gap as int, s2.len() as int, 1);
        }
    } else if s.len() == 1 {
        assert(s[0] < max_count);
        assert(max_count > 0);
        assert(s.len() <= max_count);
        assert(1 * gap == gap);
        assert(s.len() * gap <= max_count + gap - 1);
    } else {
        assert(0 * gap == 0);
    }
}

impl MRFreePerms {
    pub proof fn tracked_merge(
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
            p2.wf_pfn_order(self.map(), pfn2, order),
            old(p1).wf_pfn_order(self.map(), pfn1, order),
        ensures
            p1.wf_pfn_order(
                self.map(),
                if pfn1 < pfn2 {
                    pfn1
                } else {
                    pfn2
                },
                (order + 1) as usize,
            ),
    {
        broadcast use lemma_bit_usize_shl_values;

        let map = self.map();
        use_type_invariant(self);
        assert(map.wf());
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

    /* properties to external */
    pub closed spec fn nr_free(&self) -> Seq<usize> {
        Seq::new(MAX_ORDER as nat, |order| self.next[order].len() as usize)
    }

    pub closed spec fn next_lists(&self) -> Seq<Seq<usize>> {
        self.next
    }

    pub closed spec fn next_pages(&self) -> Seq<usize> {
        Seq::new(
            MAX_ORDER as nat,
            |order|
                if self.next[order].len() > 0 {
                    self.next[order].last()
                } else {
                    0
                },
        )
    }

    pub closed spec fn map(&self) -> LinearMap {
        self.map
    }

    pub closed spec fn pg_params(&self) -> PageCountParam<MAX_ORDER> {
        self.page_count
    }

    #[verifier(inline)]
    spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        &&& self.pg_params().valid_pfn_order(pfn, order)
        &&& pfn > 0
    }

    pub proof fn tracked_empty(map: LinearMap) -> (tracked ret: Self)
        requires
            map.wf(),
        ensures
            ret.pg_params().page_count == 0,
            ret.nr_free() == Seq::new(MAX_ORDER as nat, |order| 0usize),
            ret.next_pages() == Seq::new(MAX_ORDER as nat, |order| 0usize),
            ret.next_lists() == Seq::new(MAX_ORDER as nat, |order| Seq::<usize>::empty()),
            ret.map() == map,
    {
        let tracked ret = MRFreePerms {
            avail: Map::tracked_empty(),
            next: Seq::new(MAX_ORDER as nat, |order| Seq::empty()),
            map,
            page_count: PageCountParam { page_count: 0 },
        };
        assert(ret.next_pages() =~= Seq::new(MAX_ORDER as nat, |order| 0usize));
        assert(ret.nr_free() =~= Seq::new(MAX_ORDER as nat, |order| 0usize));
        ret
    }

    spec fn wf_at(&self, order: usize, i: int) -> bool {
        let pfn = self.next[order as int][i];
        let perm = self.avail[(order, i)];
        &&& self.page_count.valid_pfn_order(pfn, order as usize)
        &&& perm.wf_pfn_order(self.map, pfn, order as usize)
        &&& pfn > 0
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.map.wf()
        &&& self.map.size >= self.page_count.page_count * PAGE_SIZE
        &&& self.next.len() == MAX_ORDER
        &&& self.avail.dom() =~= Set::new(
            |k: (usize, int)| 0 <= k.0 < MAX_ORDER && 0 <= k.1 < self.next[k.0 as int].len(),
        )
        &&& forall|order: usize, i: int|
            #![trigger self.next[order as int][i]]
            #![trigger self.avail[(order, i)]]
            0 <= order < MAX_ORDER && 0 <= i < self.next[order as int].len() ==> self.wf_at(
                order,
                i,
            )
    }

    proof fn tracked_disjoint_with_perm_rec1(
        tracked &self,
        pfn: usize,
        order: usize,
        tracked perm: &mut RawPerm,
        o: usize,
        len: nat,
    )
        requires
            old(perm).wf_pfn_order(self.map(), pfn, order),
            0 <= len <= self.next_lists()[o as int].len(),
            0 <= o < MAX_ORDER,
        ensures
            *perm == *old(perm),
            forall|i: int|
                #![trigger self.next_lists()[o as int][i]]
                0 <= i < len ==> order_disjoint(self.next_lists()[o as int][i], o, pfn, order),
        decreases len,
    {
        if len > 0 {
            self.tracked_disjoint_with_perm_rec1(pfn, order, perm, o, (len - 1) as nat);
            use_type_invariant(&*self);
            let pfn2 = self.next[o as int][len - 1];
            let tracked perm2 = self.avail.tracked_borrow((o, len - 1));
            raw_perm_order_disjoint(self.map, pfn, order, pfn2, o, perm, perm2);
        }
    }

    proof fn tracked_disjoint_with_perm_rec2(
        tracked &self,
        pfn: usize,
        order: usize,
        tracked perm: &mut RawPerm,
        max_order: usize,
    )
        requires
            old(perm).wf_pfn_order(self.map(), pfn, order),
            0 <= max_order <= MAX_ORDER,
        ensures
            *perm == *old(perm),
            forall|o: usize, i: int|
                #![trigger self.next_lists()[o as int][i]]
                0 <= o < max_order && 0 <= i < self.next_lists()[o as int].len() ==> order_disjoint(
                    self.next_lists()[o as int][i],
                    o,
                    pfn,
                    order,
                ),
        decreases max_order,
    {
        if max_order > 0 {
            self.tracked_disjoint_with_perm_rec2(pfn, order, perm, (max_order - 1) as usize);
            let o = (max_order - 1) as usize;
            self.tracked_disjoint_with_perm_rec1(
                pfn,
                order,
                perm,
                o,
                self.next_lists()[o as int].len(),
            );
        }
    }

    proof fn tracked_disjoint_with_perm(
        tracked &self,
        pfn: usize,
        order: usize,
        tracked perm: &mut RawPerm,
    )
        requires
            old(perm).wf_pfn_order(self.map(), pfn, order),
        ensures
            *perm == *old(perm),
            forall|o: usize, i: int|
                #![trigger self.next_lists()[o as int][i]]
                0 <= o < MAX_ORDER && 0 <= i < self.next_lists()[o as int].len() ==> order_disjoint(
                    self.next_lists()[o as int][i],
                    o,
                    pfn,
                    order,
                ),
    {
        self.tracked_disjoint_with_perm_rec2(pfn, order, perm, MAX_ORDER);
    }

    proof fn tracked_disjoint_pfn(tracked &mut self, o1: usize, i: int, o2: usize, j: int)
        requires
            (o1, i) != (o2, j),
            0 <= o1 < MAX_ORDER,
            0 <= o2 < MAX_ORDER,
            0 <= i < old(self).next[o1 as int].len() as int,
            0 <= j < old(self).next[o2 as int].len() as int,
        ensures
            *self == *old(self),
            order_disjoint(self.next[o1 as int][i], o1, self.next[o2 as int][j], o2),
    {
        use_type_invariant(&*self);
        let tracked mut tmp = MRFreePerms::tracked_empty(old(self).map());
        tracked_swap(&mut tmp, self);
        let tracked MRFreePerms { mut avail, next, map, page_count } = tmp;
        let pfn1 = next[o1 as int][i];
        let pfn2 = next[o2 as int][j];
        let tracked mut p1 = avail.tracked_remove((o1, i));
        let tracked p2 = avail.tracked_remove((o2, j));
        raw_perm_order_disjoint(self.map, pfn1, o1, pfn2, o2, &mut p1, &p2);
        avail.tracked_insert((o1, i), p1);
        avail.tracked_insert((o2, j), p2);
        assert(avail =~= old(self).avail);
        *self = MRFreePerms { avail, next, map, page_count };
    }

    proof fn tracked_next_no_dup_len(tracked &mut self, o: usize)
        requires
            0 <= o < MAX_ORDER,
        ensures
            *self == *old(self),
            self.next[o as int].no_duplicates(),
            self.next[o as int].len() <= self.pg_params().page_count,
            self.next[o as int].len() * (1usize << o) <= self.pg_params().page_count + (1usize << o)
                - 1,
    {
        let next_seq = self.next[o as int];
        self.tracked_next_is_disjoint_rec(o, 0, next_seq.len() as int);
        use_type_invariant(&*self);
        lemma_order_disjoint_len(next_seq, o, self.page_count.page_count);
    }

    proof fn tracked_next_is_disjoint_rec(tracked &mut self, o: usize, start: int, end: int)
        requires
            0 <= o < MAX_ORDER,
            0 <= start <= end <= old(self).next[o as int].len(),
        ensures
            *self == *old(self),
            forall|i, j|
                #![trigger self.next[o as int][i], self.next[o as int][j]]
                start <= i < end && start <= j < end && i != j ==> order_disjoint(
                    self.next[o as int][i],
                    o,
                    self.next[o as int][j],
                    o,
                ),
        decreases end - start,
    {
        if start + 1 < end {
            self.tracked_next_is_disjoint_rec(o, start + 1, end);
            self.tracked_next_is_disjoint_rec(o, start, end - 1);
            self.tracked_disjoint_pfn(o, start, o, end - 1);
            assert forall|i, j|
                #![trigger self.next[o as int][i], self.next[o as int][j]]
                start <= i < end && start <= j < end && i != j ==> order_disjoint(
                    self.next[o as int][i],
                    o,
                    self.next[o as int][j],
                    o,
                ) by {}
        }
    }

    #[verifier::spinoff_prover]
    proof fn tracked_push(tracked &mut self, order: usize, pfn: usize, tracked perm: RawPerm)
        requires
            0 <= order < MAX_ORDER,
            old(self).valid_pfn_order(pfn, order),
            perm.wf_pfn_order(old(self).map, pfn, order),
        ensures
            self.next_pages() == old(self).next_pages().update(order as int, pfn),
            self.next_lists() == old(self).next_lists().update(
                order as int,
                old(self).next_lists()[order as int].push(pfn),
            ),
            self.map() == old(self).map(),
            self.pg_params() == old(self).pg_params(),
            self.nr_free() == old(self).nr_free().update(
                order as int,
                (old(self).nr_free()[order as int] + 1) as usize,
            ),
            old(self).nr_free()[order as int] <= old(self).pg_params().page_count,
            old(self).nr_free()[order as int] * (1usize << order) <= old(
                self,
            ).pg_params().page_count - 1,
    {
        use_type_invariant(&*self);
        let tracked mut tmp = MRFreePerms::tracked_empty(old(self).map());
        tracked_swap(&mut tmp, self);
        let tracked MRFreePerms { mut avail, next, map, page_count } = tmp;
        avail.tracked_insert((order, next[order as int].len() as int), perm);
        *self =
        MRFreePerms {
            avail,
            next: next.update(order as int, next[order as int].push(pfn)),
            map: map,
            page_count: page_count,
        };
        assert(old(self).nr_free()[order as int] == old(self).next[order as int].len() as usize);
        self.tracked_next_no_dup_len(order);
        let gap = 1usize << order;
        lemma_mul_is_distributive_add_other_way(
            gap as int,
            old(self).nr_free()[order as int] as int,
            1,
        );

        assert(self.next[order as int].len() as usize == (old(self).nr_free()[order as int]
            + 1) as usize);
        assert(self.next_pages() =~= old(self).next_pages().update(order as int, pfn));
        assert forall|o: usize| 0 <= o < MAX_ORDER implies #[trigger] self.nr_free()[o as int]
            == if o != order {
            old(self).nr_free()[o as int]
        } else {
            (old(self).nr_free()[order as int] + 1) as usize
        } by {}
        assert(self.nr_free() =~= old(self).nr_free().update(
            order as int,
            (old(self).nr_free()[order as int] + 1) as usize,
        ));
    }

    #[verifier::spinoff_prover]
    proof fn tracked_remove(tracked &mut self, order: usize, i: int) -> (tracked perm: RawPerm)
        requires
            0 <= order < MAX_ORDER,
            0 <= i < old(self).next_lists()[order as int].len(),
        ensures
            self.next_pages() == old(self).next_pages().update(
                order as int,
                self.next_pages()[order as int],
            ),
            self.next_lists() == old(self).next_lists().update(
                order as int,
                old(self).next_lists()[order as int].remove(i),
            ),
            perm.wf_pfn_order(self.map, old(self).next_lists()[order as int][i], order),
            self.map() == old(self).map(),
            self.pg_params() == old(self).pg_params(),
            self.nr_free() == old(self).nr_free().update(
                order as int,
                (old(self).nr_free()[order as int] - 1) as usize,
            ),
            old(self).nr_free()[order as int] > 0,
    {
        use_type_invariant(&*self);
        let tracked mut tmp = MRFreePerms::tracked_empty(old(self).map());
        tracked_swap(&mut tmp, self);
        tmp.tracked_next_no_dup_len(order);
        assert(old(self).nr_free()[order as int] == old(self).next[order as int].len());

        let tracked MRFreePerms { mut avail, next, map, page_count } = tmp;
        let len = next[order as int].len();
        let m = Map::new(
            |k: (usize, int)| avail.dom().contains(k) && k != (order, len - 1),
            |k: (usize, int)|
                if k.0 == order && k.1 >= i {
                    (k.0, k.1 + 1)
                } else {
                    k
                },
        );
        let tracked perm = avail.tracked_remove((order, i));
        avail.tracked_map_keys_in_place(m);
        *self =
        MRFreePerms {
            avail,
            next: next.update(order as int, next[order as int].remove(i)),
            map: map,
            page_count: page_count,
        };
        assert(self.nr_free() =~= old(self).nr_free().update(
            order as int,
            (old(self).nr_free()[order as int] - 1) as usize,
        ));
        assert(self.next_pages() =~= old(self).next_pages().update(
            order as int,
            self.next_pages()[order as int],
        ));
        perm
    }
}

} // verus!
