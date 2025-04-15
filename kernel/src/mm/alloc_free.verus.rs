verus! {

tracked struct MRFreePerms {
    tracked avail: Seq<Seq<PgUnitPerm<DeallocUnit>>>,
    ghost mr_map: MemRegionMapping,
}

pub proof fn tracked_nested_empty<T>(n: nat) -> (tracked ret: Seq<Seq<T>>)
    requires
        n > 0,
    ensures
        ret.len() == n,
        ret == Seq::new(n, |i| Seq::<T>::empty()),
    decreases n,
{
    if n == 0 {
        Seq::tracked_empty()
    } else {
        let tracked mut ret = tracked_nested_empty((n - 1) as nat);
        ret.tracked_push(Seq::tracked_empty());
        ret
    }
}

proof fn raw_perm_order_disjoint(
    mr_map: MemRegionMapping,
    pfn1: usize,
    o1: usize,
    pfn2: usize,
    o2: usize,
    tracked p1: &mut RawPerm,
    tracked p2: &RawPerm,
)
    requires
        old(p1).wf_pfn_order(mr_map, pfn1, o1),
        p2.wf_pfn_order(mr_map, pfn2, o2),
    ensures
        order_disjoint(pfn1, o1, pfn2, o2),
        *old(p1) == *p1,
{
    let vaddr1 = mr_map@.map.lemma_get_virt(pfn1);
    let vaddr2 = mr_map@.map.lemma_get_virt(pfn2);
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
    #[verifier::spinoff_prover]
    #[verifier::rlimit(2)]
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
            p2.wf_pfn_order(self.mr_map(), pfn2, order),
            old(p1).wf_pfn_order(self.mr_map(), pfn1, order),
        ensures
            p1.wf_pfn_order(
                self.mr_map(),
                if pfn1 < pfn2 {
                    pfn1
                } else {
                    pfn2
                },
                (order + 1) as usize,
            ),
    {
        broadcast use lemma_bit_usize_shl_values;

        let map = self.mr_map()@.map;
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
        self.avail.map_values(|perms: Seq<PgUnitPerm<DeallocUnit>>| perms.len() as usize)
    }

    #[verifier(inline)]
    spec fn next_lists(&self) -> Seq<Seq<usize>> {
        Seq::new(self.avail.len(), |i| Seq::new(self.avail[i].len(), |k| self.avail[i][k].pfn()))
    }

    pub closed spec fn next_page(&self, order: usize) -> usize {
        let perms = self.avail[order as int];
        if perms.len() > 0 {
            perms.last().pfn()
        } else {
            0
        }
    }

    pub closed spec fn next_pages(&self) -> Seq<usize> {
        self.avail.map_values(
            |perms: Seq<PgUnitPerm<DeallocUnit>>|
                if perms.len() > 0 {
                    perms.last().pfn()
                } else {
                    0
                },
        )
    }

    pub closed spec fn mr_map(&self) -> MemRegionMapping {
        self.mr_map
    }

    pub closed spec fn pg_params(&self) -> PageCountParam<MAX_ORDER> {
        self.mr_map.pg_params()
    }

    #[verifier(inline)]
    spec fn valid_pfn_order(&self, pfn: usize, order: usize) -> bool {
        &&& self.pg_params().valid_pfn_order(pfn, order)
        &&& pfn > 0
    }

    proof fn tracked_empty(mr_map: MemRegionMapping) -> (tracked ret: Self)
        requires
            mr_map.wf(),
        ensures
            ret.nr_free() == Seq::new(MAX_ORDER as nat, |order| 0usize),
            ret.avail === Seq::new(MAX_ORDER as nat, |order| Seq::empty()),
            ret.mr_map() == mr_map,
    {
        let tracked ret = MRFreePerms { avail: tracked_nested_empty(MAX_ORDER as nat), mr_map };
        assert(ret.nr_free() =~= Seq::new(MAX_ORDER as nat, |order| 0usize));
        ret
    }

    spec fn wf_next(&self, order: usize, i: int) -> bool {
        let perm = self.avail[order as int][i];
        let next_perm = self.avail[order as int][i - 1];
        match perm.page_info() {
            Some(PageInfo::Free(FreeInfo { order, next_page })) => {
                &&& (next_page == 0 <==> i == 0)
                &&& next_page > 0 ==> next_page == next_perm.pfn()
            },
            _ => { false },
        }
    }

    #[verifier(opaque)]
    spec fn wf_strict(&self) -> bool {
        forall|order: usize, i: int|
            #![trigger self.avail[order as int][i]]
            0 <= order < MAX_ORDER && 0 <= i < self.avail[order as int].len() ==> self.wf_next(
                order,
                i,
            )
    }

    #[verifier(opaque)]
    spec fn wf_at(&self, order: usize, i: int) -> bool {
        let perm = self.avail[order as int][i];
        let pfn = perm.info.unit_start();
        &&& self.pg_params().valid_pfn_order(pfn, order)
        &&& perm.wf_pfn_order(self.mr_map, pfn, order)
        &&& perm.page_type() == PageType::Free
        &&& pfn > 0
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.mr_map.wf()
        &&& self.avail.len() == MAX_ORDER
        &&& forall|order: int, i: int|
            #![trigger self.avail[order][i]]
            0 <= order < MAX_ORDER && 0 <= i < self.avail[order as int].len() ==> self.wf_at(
                order as usize,
                i,
            )
    }

    proof fn tracked_perm_disjoint_rec1(
        tracked &self,
        pfn: usize,
        order: usize,
        tracked perm: &mut RawPerm,
        o: usize,
        len: nat,
    )
        requires
            old(perm).wf_pfn_order(self.mr_map, pfn, order),
            0 <= len <= self.avail[o as int].len(),
            0 <= o < MAX_ORDER,
        ensures
            *perm == *old(perm),
            forall|i: int|
                #![trigger self.avail[o as int][i]]
                0 <= i < len ==> order_disjoint(self.avail[o as int][i].pfn(), o, pfn, order),
        decreases len,
    {
        reveal(MRFreePerms::wf_at);
        if len > 0 {
            self.tracked_perm_disjoint_rec1(pfn, order, perm, o, (len - 1) as nat);
            use_type_invariant(&*self);
            let pfn2 = self.avail[o as int][len - 1].pfn();
            let tracked perm2 = self.avail.tracked_borrow(o as int).tracked_borrow(len - 1);
            raw_perm_order_disjoint(self.mr_map, pfn, order, pfn2, o, perm, &perm2.mem);
        }
    }

    proof fn tracked_perm_disjoint_rec2(
        tracked &self,
        pfn: usize,
        order: usize,
        tracked perm: &mut RawPerm,
        max_order: usize,
    )
        requires
            old(perm).wf_pfn_order(self.mr_map(), pfn, order),
            0 <= max_order <= MAX_ORDER,
        ensures
            *perm == *old(perm),
            forall|o: usize, i: int|
                #![trigger self.avail[o as int][i].pfn()]
                0 <= o < max_order && 0 <= i < self.avail[o as int].len() ==> order_disjoint(
                    self.avail[o as int][i].pfn(),
                    o,
                    pfn,
                    order,
                ),
        decreases max_order,
    {
        if max_order > 0 {
            self.tracked_perm_disjoint_rec2(pfn, order, perm, (max_order - 1) as usize);
            let o = (max_order - 1) as usize;
            self.tracked_perm_disjoint_rec1(pfn, order, perm, o, self.avail[o as int].len());
        }
    }

    proof fn tracked_perm_disjoint(
        tracked &self,
        tracked perm: &mut RawPerm,
        pfn: usize,
        order: usize,
    )
        requires
            old(perm).wf_pfn_order(self.mr_map(), pfn, order),
        ensures
            *perm == *old(perm),
            forall|o: usize, i: int|
                #![trigger self.avail[o as int][i].pfn()]
                0 <= o < MAX_ORDER && 0 <= i < self.avail[o as int].len() ==> order_disjoint(
                    self.avail[o as int][i].pfn(),
                    o,
                    pfn,
                    order,
                ),
    {
        self.tracked_perm_disjoint_rec2(pfn, order, perm, MAX_ORDER);
    }

    proof fn tracked_disjoint_pfn(tracked &mut self, o1: usize, i: int, o2: usize, j: int)
        requires
            (o1, i) != (o2, j),
            0 <= o1 < MAX_ORDER,
            0 <= o2 < MAX_ORDER,
            0 <= i < old(self).avail[o1 as int].len() as int,
            0 <= j < old(self).avail[o2 as int].len() as int,
        ensures
            *self == *old(self),
            order_disjoint(self.avail[o1 as int][i].pfn(), o1, self.avail[o2 as int][j].pfn(), o2),
    {
        reveal(MRFreePerms::wf_at);
        use_type_invariant(&*self);
        let pfn1 = self.avail[o1 as int][i].pfn();
        let pfn2 = self.avail[o2 as int][j].pfn();
        let tracked mut tmp = MRFreePerms::tracked_empty(old(self).mr_map);
        tracked_swap(&mut tmp, self);
        let tracked MRFreePerms { mut avail, mr_map } = tmp;

        let tracked mut a = avail.tracked_remove(o1 as int);
        let olda = a;
        let tracked mut p1 = a.tracked_remove(i);
        let tracked p2 = if o1 < o2 {
            avail.tracked_borrow(o2 - 1).tracked_borrow(j)
        } else if o1 > o2 {
            avail.tracked_borrow(o2 as int).tracked_borrow(j)
        } else {
            if i < j {
                a.tracked_borrow(j - 1)
            } else {
                a.tracked_borrow(j)
            }
        };
        use_type_invariant(&p1);
        raw_perm_order_disjoint(self.mr_map, pfn1, o1, pfn2, o2, &mut p1.mem, &p2.mem);
        a.tracked_insert(i, p1);
        avail.tracked_insert(o1 as int, a);
        assert(a =~= olda);
        assert(avail =~= old(self).avail);
        *self = MRFreePerms { avail, mr_map };
    }

    proof fn tracked_next_no_dup_len(tracked &mut self, o: usize)
        requires
            0 <= o < MAX_ORDER,
        ensures
            *self == *old(self),
            self.next_lists()[o as int].no_duplicates(),
            self.avail[o as int].len() <= self.pg_params().page_count,
            self.avail[o as int].len() * (1usize << o) <= self.pg_params().page_count + (1usize
                << o) - 1,
    {
        reveal(MRFreePerms::wf_at);
        use_type_invariant(&*self);

        let next_seq = self.next_lists()[o as int];
        assert(next_seq.len() == self.avail[o as int].len());
        self.tracked_next_is_disjoint_rec(o, 0, next_seq.len() as int);
        lemma_order_disjoint_len(next_seq, o, self.pg_params().page_count);
    }

    proof fn tracked_next_is_disjoint_rec(tracked &mut self, o: usize, start: int, end: int)
        requires
            0 <= o < MAX_ORDER,
            0 <= start <= end <= old(self).avail[o as int].len(),
        ensures
            *self == *old(self),
            forall|i, j|
                #![trigger self.avail[o as int][i], self.avail[o as int][j]]
                start <= i < end && start <= j < end && i != j ==> order_disjoint(
                    self.avail[o as int][i].pfn(),
                    o,
                    self.avail[o as int][j].pfn(),
                    o,
                ),
        decreases end - start,
    {
        if start + 1 < end {
            self.tracked_next_is_disjoint_rec(o, start + 1, end);
            self.tracked_next_is_disjoint_rec(o, start, end - 1);
            self.tracked_disjoint_pfn(o, start, o, end - 1);
            assert forall|i, j|
                #![trigger self.avail[o as int][i], self.avail[o as int][j]]
                start <= i < end && start <= j < end && i != j ==> order_disjoint(
                    self.avail[o as int][i].pfn(),
                    o,
                    self.avail[o as int][j].pfn(),
                    o,
                ) by {}
        }
    }

    #[verifier::spinoff_prover]
    proof fn tracked_insert(
        tracked &mut self,
        order: usize,
        idx: int,
        pfn: usize,
        tracked perm: PgUnitPerm<DeallocUnit>,
    )
        requires
            0 <= order < MAX_ORDER,
            0 <= idx <= old(self).avail[order as int].len() as int,
            old(self).valid_pfn_order(pfn, order),
            perm.wf_pfn_order(old(self).mr_map, pfn, order),
            perm.page_type() == PageType::Free,
        ensures
            self.avail == old(self).avail.update(
                order as int,
                old(self).avail[order as int].insert(idx, perm),
            ),
            self.avail[order as int] == old(self).avail[order as int].insert(idx, perm),
            self.mr_map() == old(self).mr_map(),
            self.pg_params() == old(self).pg_params(),
            self.nr_free() == old(self).nr_free().update(
                order as int,
                (old(self).nr_free()[order as int] + 1) as usize,
            ),
            old(self).nr_free()[order as int] <= old(self).pg_params().page_count - 1,
            old(self).nr_free()[order as int] * (1usize << order) <= old(
                self,
            ).pg_params().page_count - 1,
    {
        reveal(MRFreePerms::wf_at);
        use_type_invariant(&*self);
        let tracked mut tmp = MRFreePerms::tracked_empty(old(self).mr_map());
        tracked_swap(&mut tmp, self);
        let tracked MRFreePerms { mut avail, mr_map } = tmp;
        let tracked mut a = avail.tracked_remove(order as int);
        a.tracked_insert(idx, perm);
        avail.tracked_insert(order as int, a);

        *self = MRFreePerms { avail, mr_map: mr_map };
        assert(self.avail =~= old(self).avail.update(
            order as int,
            old(self).avail[order as int].insert(idx, perm),
        ));
        assert(old(self).nr_free()[order as int] == old(self).avail[order as int].len() as usize);
        self.tracked_next_no_dup_len(order);
        let gap = 1usize << order;
        lemma_mul_is_distributive_add_other_way(
            gap as int,
            old(self).nr_free()[order as int] as int,
            1,
        );

        assert(self.avail[order as int].len() as usize == (old(self).nr_free()[order as int]
            + 1) as usize);
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
    proof fn tracked_push(
        tracked &mut self,
        order: usize,
        pfn: usize,
        tracked perm: PgUnitPerm<DeallocUnit>,
    )
        requires
            0 <= order < MAX_ORDER,
            old(self).valid_pfn_order(pfn, order),
            perm.wf_pfn_order(old(self).mr_map, pfn, order),
            perm.page_type() == PageType::Free,
            old(self).wf_strict(),
            perm.page_info() == Some(
                PageInfo::Free(FreeInfo { order, next_page: old(self).next_page(order) }),
            ),
        ensures
            self.avail == old(self).avail.update(
                order as int,
                old(self).avail[order as int].push(perm),
            ),
            self.mr_map() == old(self).mr_map(),
            self.pg_params() == old(self).pg_params(),
            self.nr_free() == old(self).nr_free().update(
                order as int,
                (old(self).nr_free()[order as int] + 1) as usize,
            ),
            old(self).nr_free()[order as int] <= old(self).pg_params().page_count - 1,
            old(self).nr_free()[order as int] * (1usize << order) <= old(
                self,
            ).pg_params().page_count - 1,
            self.wf_strict(),
    {
        reveal(MRFreePerms::wf_strict);
        reveal(MRFreePerms::wf_at);
        use_type_invariant(&*self);
        self.tracked_insert(order, self.avail[order as int].len() as int, pfn, perm);
        assert(old(self).avail[order as int].push(perm) =~= old(self).avail[order as int].insert(
            old(self).avail[order as int].len() as int,
            perm,
        ));
        assert(self.avail[order as int].last() == perm);

    }

    #[verifier::spinoff_prover]
    proof fn tracked_pop(tracked &mut self, order: usize) -> (tracked perm: PgUnitPerm<DeallocUnit>)
        requires
            0 <= order < MAX_ORDER,
            old(self).next_page(order) > 0,
        ensures
            self.avail == old(self).avail.update(order as int, self.avail[order as int]),
            self.avail[order as int] == old(self).avail[order as int].take(
                old(self).avail[order as int].len() - 1,
            ),
            perm.wf_pfn_order(self.mr_map, old(self).avail[order as int].last().pfn(), order),
            self.mr_map() == old(self).mr_map(),
            self.pg_params() == old(self).pg_params(),
            self.nr_free() == old(self).nr_free().update(
                order as int,
                (old(self).nr_free()[order as int] - 1) as usize,
            ),
            old(self).nr_free()[order as int] > 0,
            old(self).next_page(order) > 0 ==> old(self).valid_pfn_order(
                old(self).next_page(order),
                order,
            ),
            perm.page_type() == PageType::Free,
    {
        self.tracked_remove(order, self.avail[order as int].len() - 1)
    }

    #[verifier::spinoff_prover]
    proof fn tracked_borrow(tracked &self, order: usize, i: int) -> (tracked perm: &PgUnitPerm<
        DeallocUnit,
    >)
        requires
            0 <= order < MAX_ORDER,
            0 <= i < self.avail[order as int].len(),
            self.wf_strict(),
        ensures
            perm.page_type() == PageType::Free,
            perm.wf_pfn_order(self.mr_map, self.avail[order as int][i].pfn(), order),
            self.pg_params().valid_pfn_order(self.avail[order as int][i].pfn(), order),
            perm.page_info() == Some(
                PageInfo::Free(FreeInfo { order, next_page: if i > 0 {self.avail[order as int][i - 1].pfn()} else {0} }),
            ),
            perm == self.avail[order as int][i],
    {
        reveal(MRFreePerms::wf_at);
        use_type_invariant(self);
        reveal(MRFreePerms::wf_strict);
        let tracked p = self.avail.tracked_borrow(order as int).tracked_borrow(i);
        use_type_invariant(&p);
        p
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(2)]
    proof fn tracked_remove(tracked &mut self, order: usize, idx: int) -> (tracked perm: PgUnitPerm<
        DeallocUnit,
    >)
        requires
            0 <= order < MAX_ORDER,
            0 <= idx < old(self).avail[order as int].len(),
        ensures
            self.avail == old(self).avail.update(order as int, self.avail[order as int]),
            self.avail == old(self).avail.update(order as int, self.avail[order as int]),
            self.avail[order as int] == old(self).avail[order as int].remove(idx),
            perm.wf_pfn_order(self.mr_map, old(self).avail[order as int][idx].pfn(), order),
            perm == old(self).avail[order as int][idx],
            self.mr_map() == old(self).mr_map(),
            self.pg_params() == old(self).pg_params(),
            self.nr_free() == old(self).nr_free().update(
                order as int,
                (old(self).nr_free()[order as int] - 1) as usize,
            ),
            old(self).nr_free()[order as int] > 0,
            old(self).avail[order as int][idx].pfn() > 0 ==> old(self).valid_pfn_order(
                old(self).avail[order as int][idx].pfn(),
                order,
            ),
            perm.page_type() == PageType::Free,
            old(self).wf_strict() ==> perm.page_info() == Some(
                PageInfo::Free(FreeInfo { order, next_page: if idx == 0 {0} else {
                    self.avail[order as int][idx - 1].pfn()
                }  }),
            ),
    {
        reveal(MRFreePerms::wf_at);
        reveal(MRFreePerms::wf_strict);
        use_type_invariant(&*self);
        let p = self.avail[order as int][idx];
        let tracked mut tmp = MRFreePerms::tracked_empty(old(self).mr_map());
        tracked_swap(&mut tmp, self);
        tmp.tracked_next_no_dup_len(order);
        assert(old(self).nr_free()[order as int] == old(self).avail[order as int].len());

        let tracked MRFreePerms { mut avail, mr_map } = tmp;
        let len = avail[order as int].len();
        let tracked mut a = avail.tracked_remove(order as int);
        let olda = a;
        let tracked perm = a.tracked_remove(idx);
        avail.tracked_insert(order as int, a);
        *self = MRFreePerms { avail, mr_map: mr_map };
        assert(self.avail =~= old(self).avail.update(
            order as int,
            old(self).avail[order as int].remove(idx),
        ));
        assert(self.nr_free() =~= old(self).nr_free().update(
            order as int,
            (old(self).nr_free()[order as int] - 1) as usize,
        ));
        perm
    }

    proof fn tracked_valid_next_at(tracked &self, order: usize, i: int)
        requires
            order < MAX_ORDER,
            0 <= i < self.avail[order as int].len(),
        ensures
            self.pg_params().valid_pfn_order(self.avail[order as int][i].pfn(), order as usize),
    {
        reveal(MRFreePerms::wf_at);
        use_type_invariant(self);
    }

    proof fn tracked_valid_next_page(tracked &self, order: usize)
        requires
            order < MAX_ORDER,
            self.wf_strict(),
        ensures
            self.next_page(order) != 0 ==> self.pg_params().valid_pfn_order(
                self.next_page(order),
                order as usize,
            ),
    {
        use_type_invariant(self);
        if self.next_page(order) != 0 {
            self.tracked_valid_next_at(order, self.avail[order as int].len() - 1);
        }
    }


    #[verifier::spinoff_prover]
    #[verifier::rlimit(2)]
    proof fn lemma_wf_restrict_remove(&self, tracked new: &Self, order: usize, idx: int)
        requires
            self.wf_strict(),
            self.wf(),
            new.avail =~= self.avail.update(
                order as int,
                new.avail[order as int],
            ),
            order < MAX_ORDER,
            0 <= idx < self.avail[order as int].len(),
            idx < self.avail[order as int].len() ==> new.avail[order as int] =~= self.avail[order as int].remove(idx + 1).update(idx, new.avail[order as int][idx]),
            idx == self.avail[order as int].len() - 1 ==> new.avail[order as int] =~= self.avail[order as int].remove(idx),
            new.avail[order as int][idx].pfn() == self.avail[order as int][idx + 1].pfn(),
            new.avail[order as int][idx].page_info() == Some(
                PageInfo::Free(FreeInfo { order, next_page: if idx > 0 {self.avail[order as int][idx - 1].pfn()} else {0} }),
            ),
        ensures
            new.wf_strict(),
    {
        use_type_invariant(new);
        reveal(MRFreePerms::wf_strict);
        reveal(MRFreePerms::wf_at);
        
        assert(idx > 0 ==> self.avail[order as int][idx - 1].pfn() == new.avail[order as int][idx - 1].pfn());
        assert forall |o: usize, i: int|
        #![trigger new.avail[o as int][i]]
        0 <= o < MAX_ORDER && 0 <= i < new.avail[o as int].len()
    implies new.wf_next(
            o,
            i,
        ) by {
            let a = new.avail[o as int][i];
            let prev_a = new.avail[o as int][i - 1];
            let old_a = self.avail[o as int][i];
            let old_prev_a = self.avail[o as int][i - 1];
            let old_prev_a = self.avail[o as int][i + 1];
        }
    }
}

} // verus!
