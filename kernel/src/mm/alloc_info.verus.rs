use verify_proof::frac_ptr::*;
use verify_proof::set::axiom_set_usize_range;
use vstd::raw_ptr::PtrData;
verus! {

struct PageInfoInner {
    pub ghost start_idx: usize,
    pub ghost npages: usize,
    pub ghost base_ptr: vstd::raw_ptr::PtrData,
    pub reserved: Map<usize, FracTypedPerm<PageStorageType>>,
}

type PInfoPerm = FracTypedPerm<PageStorageType>;

trait ValidRange {
    spec fn contains_range(
        &self,
        base_ptr: *const PageStorageType,
        pfn: usize,
        npage: usize,
    ) -> bool;
}

impl ValidRange for Map<usize, FracTypedPerm<PageStorageType>> {
    spec fn contains_range(
        &self,
        base_ptr: *const PageStorageType,
        pfn: usize,
        npage: usize,
    ) -> bool {
        &&& forall|idx|
            pfn <= idx < pfn + npage ==> {
                #[trigger] self.contains_key(idx)
            }
        &&& forall|idx|
            #![trigger self[idx]]
            pfn <= idx < pfn + npage ==> {
                &&& self[idx].is_valid_pginfo()
                &&& self[idx].ptr() == spec_ptr_add(base_ptr, idx)
            }
    }
}

impl PageInfoInner {
    #[verifier(spinoff_prover)]
    #[verifier(rlimit(2))]
    proof fn tracked_insert(
        tracked self,
        idx: usize,
        oldperm: FracTypedPerm<PageStorageType>,
        tracked perm: FracTypedPerm<PageStorageType>,
    ) -> PageInfoDb
        requires
            PageInfoDb::new(
                self.npages,
                self.start_idx,
                self.base_ptr,
                self.reserved.insert(idx, oldperm),
            ).wf(),
            perm@ == oldperm@.update_value(perm.opt_value()),
            perm.is_valid_pginfo(),
            oldperm.is_valid_pginfo(),
            self.start_idx <= idx < self.start_idx + self.npages,
            perm.order() == oldperm.order(),
            perm.page_info().unwrap().spec_type() == oldperm.page_info().unwrap().spec_type(),
    {
        let oldinfo = PageInfoDb::new(
            self.npages,
            self.start_idx,
            self.base_ptr,
            self.reserved.insert(idx, oldperm),
        );
        let tracked PageInfoInner { npages, start_idx, base_ptr, mut reserved } = self;
        reserved.tracked_insert(idx, perm);
        let info = PageInfoDb::new(self.npages, self.start_idx, self.base_ptr, reserved);

        assert forall|i| start_idx <= i < start_idx + npages implies if i != idx {
            #[trigger] info@[i] == oldinfo@[i]
        } else {
            info@[i] == perm && perm.ptr() == oldinfo@[i].ptr()
        } by {}

        assert forall|i| start_idx <= i < start_idx + npages implies (#[trigger] info.restrict(
            i,
        )).wf() by {
            if oldinfo@[i].is_head() {
                oldinfo.lemma_restrict(i);
                assert(oldinfo.restrict(i).wf_unit());
                assert(info@[i].is_head());
                assert(info.restrict(i).is_unit());
                if i > idx {
                    assert(info.restrict(i)@ =~= oldinfo.restrict(i)@);
                } else if i < idx && oldinfo@[idx].is_head() {
                    oldinfo.lemma_head_no_overlap(i, idx);
                    assert(info.restrict(i)@ =~= oldinfo.restrict(i)@);
                } else if i == idx {
                    assert forall|j| i < j < i + info@[i].size() implies info@[j]
                        == oldinfo@[j] by {}
                    assert(info.restrict(i).wf_unit());
                } else {
                    assert(info.restrict(i).wf_unit());
                }
            } else {
                assert(info.restrict(i)@.is_empty());
            }
        }
        PageInfoDb { npages, start_idx, base_ptr, reserved }
    }
}

struct PageInfoDb {
    ghost start_idx: usize,
    ghost npages: usize,
    ghost base_ptr: vstd::raw_ptr::PtrData,
    reserved: Map<usize, FracTypedPerm<PageStorageType>>,
}

struct RawDeallocPerm(PageInfoDb);

impl RawDeallocPerm {
    #[verifier::type_invariant]
    #[verifier(opaque)]
    pub closed spec fn wf(&self) -> bool {
        &&& self.0.is_unit()
        &&& self.0.is_readonly_dealloc_shares()
    }

    pub closed spec fn view(&self) -> PageInfoDb {
        self.0
    }

    pub closed spec fn inner_view(&self) -> Map<usize, FracTypedPermData<PageStorageType>> {
        self.0.inner_view()
    }
}

trait ValidPageInfo {
    spec fn is_valid_pginfo(&self) -> bool;

    spec fn page_info(&self) -> Option<PageInfo>;

    spec fn order(&self) -> usize;

    spec fn size(&self) -> usize;

    spec fn is_head(&self) -> bool;

    spec fn is_free(&self) -> bool;

    spec fn ens_write_page_info(&self, new: &Self, pfn: usize, pi: PageInfo) -> bool;
}

impl ValidPageInfo for FracTypedPerm<PageStorageType> {
    spec fn is_valid_pginfo(&self) -> bool {
        &&& self.page_info().is_some()
        &&& self.page_info().unwrap().spec_order() < MAX_ORDER
        &&& self.valid()
        &&& self.total() == MAX_PGINFO_SHARES
    }

    spec fn ens_write_page_info(&self, perm: &Self, pfn: usize, pi: PageInfo) -> bool {
        let old_perm = *self;
        &&& perm@ == old_perm@.update_value(perm.opt_value())
        &&& perm.valid()
        &&& perm.page_info() == Some(pi)
    }

    spec fn page_info(&self) -> Option<PageInfo> {
        spec_page_info(self.opt_value())
    }

    spec fn order(&self) -> usize {
        self.page_info().unwrap().spec_order()
    }

    #[verifier(inline)]
    spec fn size(&self) -> usize {
        1usize << self.order()
    }

    spec fn is_head(&self) -> bool {
        !matches!(self.page_info(), Some(PageInfo::Compound(_)))
    }

    spec fn is_free(&self) -> bool {
        matches!(self.page_info(), Some(PageInfo::Free(_)))
    }
}

impl PageInfoDb {
    #[verifier::type_invariant]
    pub closed spec fn wf(&self) -> bool
        decreases self.npages(),
    {
        &&& self.end() <= usize::MAX
        &&& self@.dom() =~= Set::new(|idx| self.start_idx <= idx < self.end())
        &&& self.npages > 0 ==> self.is_head(self.start_idx)
        &&& forall|idx|
            #![trigger self@[idx]]
            self.start_idx <= idx < self.end() ==> {
                &&& self@[idx].is_valid_pginfo()
                &&& self@[idx].ptr() == self.ptr(idx)
                &&& self@[idx].is_head() ==> (idx + self@[idx].size()) <= self.end()
                &&& self@[idx].is_head() && idx + self@[idx].size() < self.end() ==> self@[(idx
                    + self@[idx].size()) as usize].is_head()
                &&& self@[idx].is_head() && !self.is_unit() ==> self.restrict(idx).wf()
            }
        &&& self.is_unit() ==> self.wf_unit()
    }

    pub closed spec fn empty(base_ptr: PtrData) -> PageInfoDb {
        PageInfoDb { npages: 0, start_idx: 0, base_ptr: base_ptr, reserved: Map::empty() }
    }

    pub closed spec fn _info_dom(&self, order: usize) -> Set<usize> {
        self@.dom().filter(|i| self@[i].order() == order)
    }

    pub closed spec fn nr_page(&self, order: usize) -> nat {
        self._info_dom(order).len()
    }

    proof fn lemma_nr_page_pair(&self, order: usize, order2: usize)
        requires
            self.wf(),
            order != order2,
        ensures
            self.nr_page(order) + self.nr_page(order2) <= self.npages(),
    {
        let s1 = self._info_dom(order);
        let s2 = self._info_dom(order2);
        assert(s1.disjoint(s2));
        vstd::set_lib::lemma_set_disjoint_lens(s1, s2);
        let s = s1 + s2;
        assert(s.subset_of(self@.dom()));
        self.lemma_dom_len();
    }

    proof fn lemma_dom_len(&self)
        requires
            self.wf(),
        ensures
            self@.dom().len() == self.npages(),
    {
        axiom_set_usize_range(self.start_idx(), self.end());
    }

    proof fn lemma_nr_page_npages(&self, order: usize)
        requires
            self.wf(),
        ensures
            self.nr_page(order) <= self.npages(),
    {
        self.lemma_dom_len();
        assert(self._info_dom(order).subset_of(self@.dom()));
    }

    spec fn const_nr_page(npages: usize, order: usize) -> usize {
        if order < MAX_ORDER && (1usize << order) == npages {
            npages
        } else {
            0
        }
    }

    proof fn proof_unit_nr_page(&self)
        requires
            self.wf(),
            self.is_unit(),
        ensures
            forall|order| #[trigger]
                self.nr_page(order) == Self::const_nr_page(self.npages(), order),
    {
        assert forall|order| #[trigger]
            self.nr_page(order) == Self::const_nr_page(self.npages(), order) by {
            assert(1usize << self@[self.start_idx()].order() == self.npages());
            if (order < MAX_ORDER && (1usize << order) == self.npages()) {
                assert(order == self@[self.start_idx()].order());
            }
            self.lemma_unit_nr_page(order);
        }
    }

    proof fn lemma_unit_nr_page(&self, order: usize)
        requires
            self.wf(),
            self.is_unit(),
        ensures
            order == self@[self.start_idx()].order() ==> self.nr_page(order) == self.npages(),
            order != self@[self.start_idx()].order() ==> self.nr_page(order) == 0,
    {
        self.lemma_dom_len();
        if order == self@[self.start_idx()].order() {
            assert(self._info_dom(order) =~= self@.dom());
        } else {
            assert(self._info_dom(order).is_empty());
        }
    }

    proof fn lemma_split_restrict_view(&self, idx: usize, left: Self, right: Self)
        requires
            self.wf(),
            left.wf(),
            right.wf(),
            self.ens_split(idx, left, right),
            self.start_idx() <= idx < self.start_idx() + self.npages(),
            self@[idx].is_head(),
        ensures
            left.restrict_view() == self.restrict_view().restrict(Set::new(|k: usize| k < idx)),
            right.restrict_view() == self.restrict_view().restrict(Set::new(|k: usize| k >= idx)),
            self.restrict_view() == left.restrict_view().union_prefer_right(right.restrict_view()),
    {
        assert(self.restrict_view().dom() =~= left.restrict_view().dom()
            + right.restrict_view().dom());
        assert forall|i|
            self.restrict_view().dom().contains(i) implies #[trigger] self.restrict_view()[i]
            == if i < idx {
            left.restrict_view()[i]
        } else {
            right.restrict_view()[i]
        } by {
            self.lemma_split_restrict(idx, left, right, i);
        }
        assert forall|i|
            left.restrict_view().dom().contains(i) implies #[trigger] left.restrict_view()[i]
            == self.restrict_view()[i] by {
            self.lemma_split_restrict(idx, left, right, i);
        }
        assert forall|i|
            right.restrict_view().dom().contains(i) implies #[trigger] right.restrict_view()[i]
            == self.restrict_view()[i] by {
            self.lemma_split_restrict(idx, left, right, i);
        }
        assert(left.restrict_view() =~= self.restrict_view().restrict(
            Set::new(|k: usize| k < idx),
        ));
        assert(right.restrict_view() =~= self.restrict_view().restrict(
            Set::new(|k: usize| k >= idx),
        ));
        assert(self.restrict_view() =~= left.restrict_view().union_prefer_right(
            right.restrict_view(),
        ))
    }

    proof fn lemma_split_restrict(&self, idx: usize, left: Self, right: Self, i: usize)
        requires
            self.wf(),
            left.wf(),
            right.wf(),
            self.ens_split(idx, left, right),
            self.start_idx() <= idx < self.start_idx() + self.npages(),
            self.start_idx() <= i < self.start_idx() + self.npages(),
            self@[i].is_head(),
            self@[idx].is_head(),
        ensures
            self.restrict(i) == if i < idx {
                left.restrict(i)
            } else {
                right.restrict(i)
            },
    {
        if i < idx {
            self.lemma_head_no_overlap(i, idx);
            assert(self.restrict(i)@ =~= left.restrict(i)@);
        } else {
            assert(self.restrict(i)@ =~= right.restrict(i)@);
        }

    }

    proof fn lemma_split_nr_page(&self, idx: usize, left: Self, right: Self, order: usize)
        requires
            self.wf(),
            self.ens_split(idx, left, right),
        ensures
            self.nr_page(order) == left.nr_page(order) + right.nr_page(order),
    {
        let s1 = left._info_dom(order);
        let s2 = right._info_dom(order);
        let s = self._info_dom(order);
        vstd::set_lib::lemma_set_disjoint_lens(s1, s2);
        assert(s1 + s2 =~= s);
    }

    proof fn proof_split_nr_page(&self, idx: usize, left: Self, right: Self)
        requires
            self.wf(),
            self.ens_split(idx, left, right),
        ensures
            forall|order: usize| #[trigger]
                self.nr_page(order) == left.nr_page(order) + right.nr_page(order),
    {
        assert forall|order: usize| #[trigger]
            self.nr_page(order) == left.nr_page(order) + right.nr_page(order) by {
            self.lemma_split_nr_page(idx, left, right, order);
        }
    }

    /*** Basic spec functions ***/
    pub closed spec fn view(&self) -> Map<usize, FracTypedPerm<PageStorageType>> {
        self.reserved
    }

    pub closed spec fn restrict_view(&self) -> Map<usize, PageInfoDb> {
        Map::new(|k| self@[k].is_head() && self.start_idx() <= k < self.end(), |k| self.restrict(k))
    }

    pub closed spec fn restrict(&self, idx: usize) -> PageInfoDb {
        let info = self.page_info(idx).unwrap();
        match info {
            PageInfo::Compound(_) => { PageInfoDb::empty(self.base_ptr) },
            _ => {
                let npages = 1usize << self@[idx].order();
                PageInfoDb {
                    npages,
                    start_idx: idx,
                    base_ptr: self.base_ptr,
                    reserved: self@.restrict(Set::new(|k| idx <= k < idx + npages)),
                }
            },
        }
    }

    pub closed spec fn base_ptr(&self) -> *const PageStorageType {
        vstd::raw_ptr::ptr_from_data(self.base_ptr)
    }

    pub closed spec fn start_idx(&self) -> usize {
        self.start_idx
    }

    pub closed spec fn npages(&self) -> usize {
        self.npages
    }

    #[verifier(inline)]
    spec fn end(&self) -> int {
        self.start_idx + self.npages
    }

    /** Constructors **/
    proof fn tracked_empty(base_ptr: PtrData) -> (tracked ret: PageInfoDb)
        ensures
            ret == PageInfoDb::empty(base_ptr),
    {
        let tracked reserved = Map::tracked_empty();
        PageInfoDb { npages: 0, start_idx: 0, base_ptr, reserved }
    }

    /*** Useful spec functions ***/
    pub open spec fn unit_size() -> usize {
        size_of::<PageStorageType>()
    }

    pub open spec fn inner_view(&self) -> Map<usize, FracTypedPermData<PageStorageType>> {
        self@.map_values(|v: FracTypedPerm<PageStorageType>| v@)
    }

    pub open spec fn data_view(&self) -> Map<usize, FracTypedPermData<PageStorageType>> {
        self@.map_values(|v: FracTypedPerm<PageStorageType>| v@.data_view())
    }

    #[verifier(inline)]
    spec fn ptr(&self, idx: usize) -> *const PageStorageType {
        spec_ptr_add(self.base_ptr(), idx)
    }

    pub closed spec fn page_info(&self, idx: usize) -> Option<PageInfo> {
        self@[idx].page_info()
    }

    #[verifier(inline)]
    spec fn is_head(&self, idx: usize) -> bool {
        self@[idx].is_head()
    }

    broadcast proof fn lemma_head_no_overlap(&self, i: usize, j: usize)
        requires
            self.wf(),
            self.is_head(i),
            self.is_head(j),
            self.start_idx() <= i < j < self.start_idx() + self.npages(),
        ensures
            #![trigger self@[i], self@[j]]
            i + self@[i].size() <= j,
    {
        self.lemma_restrict(i);
        self.lemma_restrict(j);
    }

    proof fn lemma_wf_recursive(&self)
        requires
            self.wf(),
        ensures
            forall|idx|
                #![trigger self@[idx]]
                self.start_idx() <= idx < self.start_idx() + self.npages() ==> self.restrict(
                    idx,
                ).wf(),
    {
        assert forall|idx|
            #![trigger self@[idx]]
            self.start_idx() <= idx < self.start_idx() + self.npages() implies self.restrict(
            idx,
        ).wf() by {
            if self.is_head(idx) {
                self.lemma_restrict(idx);
            }
        }
    }

    proof fn lemma_restrict(&self, idx: usize)
        requires
            self.wf(),
            self.is_head(idx),
            self.start_idx() <= idx < self.start_idx() + self.npages(),
        ensures
            self.restrict(idx).wf(),
            self.restrict(idx).is_unit(),
            self.restrict(idx)@.dom() =~= Set::new(|k| idx <= k < idx + self@[idx].size()),
            forall|i|
                #![trigger self@[i]]
                #![trigger self.restrict(idx)@[i]]
                idx <= i < idx + self@[idx].size() ==> self.restrict(idx)@[i] == self@[i],
    {
        if self.is_unit() {
            assert(idx == self.start_idx);
            assert(self.npages == self@[idx].size());
            assert(self.restrict(idx)@ =~= self@);
            assert(self.restrict(idx).wf());
        } else {
            assert(self.restrict(idx).wf());
        }
    }

    pub closed spec fn writable(&self) -> bool {
        forall|idx: usize|
            self.start_idx <= idx < self.end() ==> (#[trigger] self@[idx]).shares()
                == self@[idx].total()
    }

    #[verifier::opaque]
    pub closed spec fn is_readonly_allocator_shares(&self) -> bool {
        forall|idx: usize|
            self.start_idx <= idx < self.end() ==> #[trigger] self@[idx].shares()
                == ALLOCATOR_PGINFO_SHARES
    }

    #[verifier::opaque]
    pub closed spec fn is_readonly_dealloc_shares(&self) -> bool {
        forall|idx: usize|
            self.start_idx <= idx < self.end() ==> (#[trigger] self@[idx]).shares()
                == DEALLOC_PGINFO_SHARES
    }

    pub closed spec fn new(
        npages: usize,
        start_idx: usize,
        base_ptr: PtrData,
        reserved: Map<usize, FracTypedPerm<PageStorageType>>,
    ) -> Self {
        PageInfoDb { npages, start_idx, base_ptr, reserved }
    }

    proof fn tracked_new_unit(
        order: usize,
        start_idx: usize,
        base_ptr: PtrData,
        tracked reserved: Map<usize, FracTypedPerm<PageStorageType>>,
    ) -> (tracked ret: Self)
        requires
            order < MAX_ORDER,
            start_idx + (1usize << order) <= usize::MAX,
            PageInfoDb::new(1usize << order, start_idx, base_ptr, reserved).wf_unit(),
            reserved.dom() =~= Set::new(|k| start_idx <= k < start_idx + (1usize << order)),
            PageInfoDb::new(1usize << order, start_idx, base_ptr, reserved).wf(),
            reserved[start_idx].order() == order,
        ensures
            ret.is_unit(),
            ret == PageInfoDb::new(1usize << order, start_idx, base_ptr, reserved),
            ret@ == reserved,
            forall|order| #[trigger] ret.nr_page(order) == Self::const_nr_page(ret.npages(), order),
    {
        let tracked ret = PageInfoDb { npages: 1usize << order, start_idx, base_ptr, reserved };
        ret.proof_unit_nr_page();
        ret
    }

    pub open spec fn ens_split(&self, idx: usize, left: Self, right: Self) -> bool {
        &&& left@ =~= self@.restrict(Set::new(|k: usize| k < idx))
        &&& left.base_ptr() == self.base_ptr()
        &&& left.start_idx() == self.start_idx()
        &&& left.npages() == idx - self.start_idx()
        &&& right@ =~= self@.restrict(Set::new(|k: usize| k >= idx))
        &&& right.base_ptr() == self.base_ptr()
        &&& right.start_idx() == idx
        &&& right.npages() + left.npages() == self.npages()
    }

    pub open spec fn ens_merge(&self, left: Self, right: Self) -> bool {
        &&& self@ == left@.union_prefer_right(right@)
        &&& self.base_ptr() == left.base_ptr()
        &&& self.start_idx() == left.start_idx()
        &&& self.npages() == left.npages() + right.npages()
    }

    pub open spec fn ens_merge3(&self, left: Self, mid: Self, right: Self) -> bool {
        &&& self@ == left@.union_prefer_right(mid@).union_prefer_right(right@)
        &&& self.base_ptr() == left.base_ptr()
        &&& self.start_idx() == left.start_idx()
        &&& self.npages() == left.npages() + mid.npages() + right.npages()
    }

    #[verifier(rlimit(4))]
    proof fn tracked_split(tracked self, idx: usize) -> (tracked ret: (PageInfoDb, PageInfoDb))
        requires
            self.is_head(idx),
            self.start_idx() <= idx < self.start_idx() + self.npages(),
        ensures
            self.ens_split(idx, ret.0, ret.1),
            ret.0.restrict_view() == self.restrict_view().restrict(Set::new(|k: usize| k < idx)),
            ret.1.restrict_view() == self.restrict_view().restrict(Set::new(|k: usize| k >= idx)),
            forall|order| #[trigger]
                self.nr_page(order) == ret.0.nr_page(order) + ret.1.nr_page(order),
    {
        use_type_invariant(&self);
        let tracked (left, right) = self._tracked_split(idx);
        use_type_invariant(&left);
        use_type_invariant(&right);
        self.proof_split_nr_page(idx, left, right);
        self.lemma_split_restrict_view(idx, left, right);
        (left, right)
    }

    #[verifier(spinoff_prover)]
    #[verifier(rlimit(4))]
    proof fn _tracked_split(tracked self, idx: usize) -> (tracked ret: (PageInfoDb, PageInfoDb))
        requires
            self.is_head(idx),
            self.start_idx() <= idx < self.start_idx() + self.npages(),
        ensures
            self.ens_split(idx, ret.0, ret.1),
    {
        use_type_invariant(&self);
        self.lemma_restrict(idx);
        let tracked PageInfoDb { npages, start_idx, base_ptr, mut reserved } = self;
        if idx != start_idx {
            self.lemma_head_no_overlap(start_idx, idx);
        }
        let tracked left_reserved = reserved.tracked_remove_keys(
            Set::new(|k| start_idx <= k < idx),
        );
        let left = PageInfoDb::new((idx - start_idx) as usize, start_idx, base_ptr, left_reserved);
        assert forall|i| start_idx <= i < idx && (#[trigger] left@[i]).is_head() implies i
            + left@[i].size() <= idx && left.restrict(i) == self.restrict(i) by {
            self.lemma_head_no_overlap(i, idx);
            assert(left.restrict(i)@ =~= self.restrict(i)@);
        }
        let tracked left = PageInfoDb {
            npages: (idx - start_idx) as usize,
            start_idx: start_idx,
            base_ptr: self.base_ptr,
            reserved: left_reserved,
        };

        let right = PageInfoDb::new((npages - (idx - start_idx)) as usize, idx, base_ptr, reserved);
        assert forall|i|
            right.start_idx <= i < right.start_idx + right.npages && (!right.is_unit()
                && right.is_head(i)) implies #[trigger] right.restrict(i) == self.restrict(i) by {
            assert(right.restrict(i)@ =~= self.restrict(i)@);
            assert(right.restrict(i) == self.restrict(i));
        }
        let tracked right = PageInfoDb {
            npages: (npages - (idx - start_idx)) as usize,
            start_idx: idx,
            base_ptr: self.base_ptr,
            reserved: reserved,
        };

        (left, right)
    }

    #[verifier(spinoff_prover)]
    proof fn tracked_merge_extracted(
        tracked &mut self,
        tracked mid: PageInfoDb,
        tracked right: PageInfoDb,
    )
        requires
            old(self).start_idx() + old(self).npages() == mid.start_idx(),
            right.npages() > 0 ==> mid.start_idx() + mid.npages() == right.start_idx(),
            old(self).base_ptr() == mid.base_ptr(),
            old(self).base_ptr() == right.base_ptr(),
        ensures
            self.ens_merge3(*old(self), mid, right),
            self.restrict_view() === old(self).restrict_view().union_prefer_right(
                mid.restrict_view(),
            ).union_prefer_right(right.restrict_view()),
            forall|order| #[trigger]
                self.nr_page(order) == (old(self).nr_page(order) + mid.nr_page(order)
                    + right.nr_page(order)),
    {
        use_type_invariant(&*self);
        use_type_invariant(&mid);
        let left = *self;
        self.tracked_merge(mid);
        let tmp_self = *self;
        use_type_invariant(&right);
        if right.npages() > 0 {
            self.tracked_merge(right);
        } else {
            assert(right@.is_empty());
            assert(right.restrict_view().is_empty());
            assert(self@ =~= self@.union_prefer_right(right@));
            assert(old(self).restrict_view().union_prefer_right(
                mid.restrict_view(),
            ).union_prefer_right(right.restrict_view()) =~= old(
                self,
            ).restrict_view().union_prefer_right(mid.restrict_view()));
        }

        assert forall|order: usize| #[trigger]
            self.nr_page(order) == old(self).nr_page(order) + mid.nr_page(order) + right.nr_page(
                order,
            ) by {
            assert(tmp_self.nr_page(order) == left.nr_page(order) + mid.nr_page(order));
            assert(self.nr_page(order) == tmp_self.nr_page(order) + right.nr_page(order));
        }
    }

    #[verifier(spinoff_prover)]
    #[verifier(rlimit(4))]
    proof fn tracked_extract(tracked self, idx: usize) -> (tracked ret: (
        PageInfoDb,
        PageInfoDb,
        PageInfoDb,
    ))
        requires
            self.is_head(idx),
            self.start_idx() <= idx < self.start_idx() + self.npages(),
        ensures
            ret.1 == self.restrict(idx),
            ret.1.is_unit(),
            ret.0@ =~= self@.restrict(Set::new(|k: usize| k < idx)),
            ret.0.base_ptr() == self.base_ptr(),
            ret.0.start_idx() == self.start_idx(),
            ret.0.npages() == idx - self.start_idx(),
            ret.2@ =~= self@.restrict(Set::new(|k: usize| k >= idx + self@[idx].size())),
            ret.2.base_ptr() == self.base_ptr(),
            ret.2.npages() > 0 ==> ret.2.start_idx() == idx + self@[idx].size(),
            ret.2.npages() + ret.0.npages() + ret.1.npages() == self.npages(),
            forall|order: usize| #[trigger]
                self.nr_page(order) == ret.0.nr_page(order) + ret.1.nr_page(order) + ret.2.nr_page(
                    order,
                ),
            ret.0.restrict_view() =~= self.restrict_view().restrict(Set::new(|k: usize| k < idx)),
            ret.2.restrict_view() =~= self.restrict_view().restrict(
                Set::new(|k: usize| k >= idx + self@[idx].size()),
            ),
    {
        use_type_invariant(&self);
        let start = self.start_idx();
        let end = self.end();
        let old_self = self;
        assert(self@[idx].is_valid_pginfo());
        assert(self@[idx].order() < MAX_ORDER);
        assert(self@[idx].size() > 0);
        if idx + self@[idx].size() < self.end() {
            let tracked (left, right) = self.tracked_split(idx);
            use_type_invariant(&right);
            assert(right.restrict(idx)@ =~= old_self.restrict(idx)@);
            let tracked (ret, right2) = right.tracked_split((idx + self@[idx].size()) as usize);
            assert(ret@ =~= right.restrict(idx)@);
            assert(ret.npages() == self@[idx].size());
            (left, ret, right2)
        } else {
            let tracked (left, right) = self.tracked_split(idx);
            use_type_invariant(&right);
            assert(right.npages() == self@[idx].size());
            assert(idx + self@[idx].size() == end);
            assert(right@ =~= self.restrict(idx)@);
            let empty = PageInfoDb::tracked_empty(self.base_ptr);
            assert(empty@.is_empty());
            assert(empty.restrict_view().is_empty());
            (left, right, PageInfoDb::tracked_empty(self.base_ptr))
        }
    }

    proof fn tracked_get(tracked self) -> (tracked ret: PageInfoInner)
        ensures
            PageInfoDb::new(ret.npages, ret.start_idx, ret.base_ptr, ret.reserved).wf(),
    {
        use_type_invariant(&self);
        let tracked PageInfoDb { npages, start_idx, base_ptr, reserved } = self;
        let tracked ret = PageInfoInner { npages, start_idx, base_ptr, reserved };
        ret
    }

    proof fn tracked_borrow(tracked &self, idx: usize) -> (tracked ret: &FracTypedPerm<
        PageStorageType,
    >)
        requires
            self.start_idx() <= idx < self.start_idx() + self.npages(),
        ensures
            *ret == self@[idx],
            ret.is_valid_pginfo(),
            ret.ptr() == self.ptr(idx),
    {
        use_type_invariant(&self);
        self.reserved.tracked_borrow(idx)
    }

    proof fn tracked_remove(tracked self, idx: usize) -> (tracked ret: (
        FracTypedPerm<PageStorageType>,
        PageInfoInner,
    ))
        requires
            self.is_head(idx),
            self.start_idx() <= idx < self.start_idx() + self.npages(),
        ensures
            ret.0 == self@[idx],
            ret.0.valid(),
            ret.1.npages == self.npages(),
            ret.1.start_idx == self.start_idx(),
            ret.1.base_ptr == self.base_ptr()@,
            ret.1.reserved == self@.remove(idx),
            PageInfoDb::new(
                ret.1.npages,
                ret.1.start_idx,
                ret.1.base_ptr,
                ret.1.reserved.insert(idx, ret.0),
            ).wf(),
    {
        use_type_invariant(&self);
        let tracked PageInfoDb { npages, start_idx, base_ptr, mut reserved } = self;
        let tracked ret = reserved.tracked_remove(idx);
        assert(reserved.insert(idx, ret) =~= self.reserved);
        (ret, PageInfoInner { npages, start_idx, base_ptr, reserved })
    }

    proof fn tracked_merge(tracked &mut self, tracked other: Self)
        requires
            old(self).start_idx() + old(self).npages() == other.start_idx(),
            old(self).base_ptr() == other.base_ptr(),
        ensures
            forall|order| #[trigger]
                self.nr_page(order) == (old(self).nr_page(order) + other.nr_page(order)),
            self.ens_merge(*old(self), other),
            self.restrict_view() == old(self).restrict_view().union_prefer_right(
                other.restrict_view(),
            ),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        self._tracked_merge(other);
        use_type_invariant(&*self);
        let idx = other.start_idx();
        let left = *old(self);
        self.proof_split_nr_page(idx, left, other);
        if other.npages() > 0 {
            self.lemma_split_restrict_view(idx, left, other);
        } else {
            assert(other@.is_empty());
            assert(self@ =~= old(self)@);
            assert(self.restrict_view() =~= old(self).restrict_view().union_prefer_right(
                other.restrict_view(),
            ));
        }
    }

    #[verifier(spinoff_prover)]
    #[verifier(rlimit(4))]
    proof fn _tracked_merge(tracked &mut self, tracked other: Self)
        requires
            old(self).start_idx() + old(self).npages() == other.start_idx(),
            old(self).base_ptr() == other.base_ptr(),
        ensures
            self.ens_merge(*old(self), other),
    {
        let old_self = *self;
        let tracked mut tmp = PageInfoDb::tracked_empty(self.base_ptr);
        tracked_swap(self, &mut tmp);
        use_type_invariant(&tmp);
        use_type_invariant(&other);
        let tracked PageInfoDb { mut npages, start_idx, base_ptr, mut reserved } = tmp;
        npages = (npages + other.npages()) as usize;
        reserved.tracked_union_prefer_right(other.reserved);
        let new = PageInfoDb::new(npages, start_idx, base_ptr, reserved);
        assert forall|i| start_idx <= i < start_idx + npages implies (reserved[i]).ptr()
            == #[trigger] new.ptr(i) && if (!new.is_unit() && new.is_head(i)) {
            new.restrict(i).wf()
        } else {
            true
        } by {
            if i >= start_idx + old(self).npages {
                assert(other.reserved[i].ptr() == new.ptr(i));
                assert(new.restrict(i)@ =~= other.restrict(i)@);
            } else {
                assert(old(self).reserved[i].ptr() == new.ptr(i));
                assert(new.restrict(i)@ =~= old(self).restrict(i)@);
            }
        }
        if (new.is_unit()) {
            if (old(self).npages() > 0) {
                assert(old(self).is_unit());
                assert(old(self)@ =~= new@);
            }
            if (other.npages() > 0) {
                assert(other.is_unit());
                assert(other@ =~= new@);
            }
        }
        *self = PageInfoDb { npages, start_idx, base_ptr, reserved };
    }

    #[verifier(spinoff_prover)]
    #[verifier(rlimit(4))]
    proof fn tracked_alloc(tracked &mut self, idx: usize) -> (tracked ret: RawDeallocPerm)
        requires
            old(self)@[idx].is_head(),
            !old(self)@[idx].is_free(),
            old(self).start_idx() <= idx < old(self).start_idx() + old(self).npages(),
            old(self).restrict(idx).writable(),
        ensures
            ret.inner_view() =~= old(self).restrict(idx).inner_view().map_values(
                |v: FracTypedPermData<PageStorageType>| v.update_shares(DEALLOC_PGINFO_SHARES),
            ),
            self.base_ptr() == old(self).base_ptr(),
            self.start_idx() == old(self).start_idx(),
            self.npages() == old(self).npages(),
            self.restrict(idx).is_readonly_allocator_shares(),
            ret@.is_readonly_dealloc_shares(),
            forall|order: usize| #[trigger] self.nr_page(order) == old(self).nr_page(order),
    {
        reveal(PageInfoDb::is_readonly_allocator_shares);
        reveal(PageInfoDb::is_readonly_dealloc_shares);
        let old_self = *old(self);
        let tracked mut tmp = PageInfoDb::tracked_empty(self.base_ptr);
        tracked_swap(self, &mut tmp);
        let tracked (mut left, mut mid, right) = tmp.tracked_extract(idx);
        *self = left;
        use_type_invariant(&mid);
        mid.proof_unit_nr_page();
        let order = mid@[idx].order();
        let tracked PageInfoDb { npages, start_idx, base_ptr, mut reserved } = mid;
        let allocated_npages = self@[idx].size();
        let tracked allocated_reserved = tracked_map_shares(&mut reserved, DEALLOC_PGINFO_SHARES);
        let tracked new_mid = PageInfoDb::tracked_new_unit(order, start_idx, base_ptr, reserved);
        self.tracked_merge_extracted(new_mid, right);
        assert(!new_mid.writable());
        //new_mid.proof_unit_nr_page();
        assert(self.restrict(idx)@ =~= new_mid@);
        let tracked ret = PageInfoDb::tracked_new_unit(
            order,
            start_idx,
            base_ptr,
            allocated_reserved,
        );
        assert(ret.is_unit());
        reveal(RawDeallocPerm::wf);
        RawDeallocPerm(ret)
    }

    pub closed spec fn is_unit(&self) -> bool {
        let info = self.page_info(self.start_idx).unwrap();
        let order = info.spec_order();

        &&& self.npages > 0
        &&& self.npages == 1usize << order
        &&& !matches!(info, PageInfo::Compound(_))
    }

    pub closed spec fn page_type(&self) -> PageType {
        self.page_info(self.start_idx).unwrap().spec_type()
    }

    pub closed spec fn marked_compound(&self, head_idx: usize, order: usize) -> bool {
        let n = 1usize << order;
        &&& order < MAX_ORDER
        &&& forall|i|
            #![trigger self@[i]]
            head_idx < i < head_idx + n ==> self.page_info(i) == Some(
                PageInfo::Compound(CompoundInfo { order }),
            )
    }

    pub closed spec fn wf_unit(&self) -> bool {
        let info = self.page_info(self.start_idx).unwrap();
        &&& self.npages > 0
        &&& match info {
            PageInfo::Reserved(_) => true,
            PageInfo::Compound(ci) => { false },
            PageInfo::Slab(_) | PageInfo::File(_) => true,
            PageInfo::Allocated(ai) => { self.marked_compound(self.start_idx, ai.order) },
            PageInfo::Free(fi) => { self.marked_compound(self.start_idx, fi.order) },
        }
        &&& matches!(info, PageInfo::Free(_)) ==> self.writable()
    }
}

} // verus!
