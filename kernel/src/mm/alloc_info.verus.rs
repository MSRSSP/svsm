use verify_proof::frac_ptr::tracked_map_merge_right_shares;
use verify_proof::frac_ptr::tracked_map_shares;
use verify_proof::set::{lemma_set_usize_range, set_usize_range};
use vstd::raw_ptr::PtrData;

verus! {

type PInfoPerm = FracTypedPerm<PageStorageType>;

#[allow(missing_debug_implementations)]
pub struct PageInfoUnique {
    pub ptr_data: PtrData,
    pub shares: nat,
    pub total: nat,
}

impl PageInfoUnique {
    spec fn update_shares(&self, shares: nat) -> PageInfoUnique {
        PageInfoUnique { ptr_data: self.ptr_data, shares, total: self.total }
    }

    spec fn base_ptr(&self) -> *const PageStorageType {
        vstd::raw_ptr::ptr_from_data(self.ptr_data)
    }

    #[verifier(inline)]
    spec fn ptr(&self, idx: usize) -> *const PageStorageType {
        spec_ptr_add(self.base_ptr(), idx)
    }
}

uninterp spec fn dummy_ptr() -> PtrData;

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

trait ValidPageInfo {
    spec fn is_valid_pginfo(&self) -> bool;

    spec fn page_info(&self) -> Option<PageInfo>;

    spec fn page_storage(&self) -> Option<PageStorageType>;

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
    }

    spec fn ens_write_page_info(&self, perm: &Self, pfn: usize, pi: PageInfo) -> bool {
        let old_perm = *self;
        &&& perm@ == old_perm@.update_value(perm.opt_value())
        &&& perm.is_valid_pginfo()
        &&& perm.page_info() == Some(pi)
    }

    spec fn page_info(&self) -> Option<PageInfo> {
        spec_page_info(self.opt_value())
    }

    spec fn page_storage(&self) -> Option<PageStorageType> {
        spec_page_storage_type(self.opt_value())
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

struct PageInfoDb {
    ghost unit_start: usize,  // only for unit
    ghost id: PageInfoUnique,
    reserved: Map<usize, FracTypedPerm<PageStorageType>>,
}

impl PageInfoDb {
    pub closed spec fn id(&self) -> PageInfoUnique {
        self.id
    }

    pub closed spec fn unit_start(&self) -> usize {
        self.unit_start
    }

    pub closed spec fn order(&self) -> usize {
        self.unit_head().order()
    }

    pub closed spec fn npages(&self) -> nat {
        self.dom().len()
    }

    /*** Basic spec functions ***/
    pub closed spec fn view(&self) -> Map<usize, FracTypedPerm<PageStorageType>> {
        self.reserved
    }

    /*** Useful spec functions ***/
    #[verifier(inline)]
    pub open spec fn dom(&self) -> Set<usize> {
        self@.dom()
    }

    #[verifier(inline)]
    spec fn base_ptr(&self) -> *const PageStorageType {
        self.id().base_ptr()
    }

    #[verifier(inline)]
    spec fn ptr(&self, idx: usize) -> *const PageStorageType {
        self.id().ptr(idx)
    }

    #[verifier::inline]
    pub open spec fn share_total(&self) -> (nat, nat) {
        (self.id().shares, self.id().total)
    }

    #[verifier(inline)]
    spec fn end(&self) -> int {
        self.unit_start + (1usize << self@[self.unit_start()].order())
    }

    #[verifier(inline)]
    spec fn page_info(&self, idx: usize) -> Option<PageInfo> {
        self@[idx].page_info()
    }

    #[verifier(inline)]
    spec fn is_head(&self, idx: usize) -> bool {
        self@[idx].is_head()
    }

    spec fn _is_unit(
        reserved: Map<usize, FracTypedPerm<PageStorageType>>,
        unit_start: usize,
    ) -> bool {
        let item = reserved[unit_start];
        let order = item.order();
        let npages = reserved.dom().len();
        let end = unit_start + (1usize << order);
        &&& end <= usize::MAX + 1
        &&& npages > 0
        &&& reserved.dom() =~= set_usize_range(unit_start, end)
        &&& item.is_head()
    }

    #[verifier(inline)]
    spec fn is_unit(&self) -> bool {
        &&& Self::_is_unit(self@, self.unit_start)
    }

    #[verifier(inline)]
    spec fn unit_head(&self) -> FracTypedPerm<PageStorageType>
        recommends
            self.is_unit(),
    {
        self@[self.unit_start]
    }

    #[verifier(inline)]
    spec fn dom_at(&self, idx: usize) -> Set<usize> {
        set_usize_range(idx, idx + self@[idx].size())
    }

    pub closed spec fn writable(&self) -> bool {
        self.id().shares == self.id().total > DEALLOC_PGINFO_SHARES
    }

    spec fn is_readonly_allocator_shares(&self) -> bool {
        AllocatorUnit::wf_share_total(self.id().shares, self.id().total)
    }

    pub closed spec fn marked_compound(
        reserved: Map<usize, FracTypedPerm<PageStorageType>>,
        head_idx: usize,
        order: usize,
    ) -> bool {
        let n = 1usize << order;
        &&& order < MAX_ORDER
        &&& forall|i|
            #![trigger reserved[i]]
            head_idx < i < head_idx + n ==> reserved[i].page_info() == Some(
                PageInfo::Compound(CompoundInfo { order }),
            )
    }

    spec fn wf_basic_at(
        item: FracTypedPerm<PageStorageType>,
        idx: usize,
        id: PageInfoUnique,
    ) -> bool {
        &&& item.is_valid_pginfo()
        &&& item.shares() == id.shares
        &&& item.total() == id.total
        &&& item.ptr() == id.ptr(idx)
    }

    #[verifier(inline)]
    spec fn wf_basic(&self, idx: usize) -> bool {
        Self::wf_basic_at(self@[idx], idx, self.id())
    }

    spec fn wf_follows(&self, idx: usize) -> bool {
        let next = idx + self@[idx].size();
        &&& self@[idx].is_head() ==> self.dom_at(idx).subset_of(self@.dom())
        &&& !self@[idx].is_head() ==> idx > 0 && self@.dom().contains((idx - 1) as usize)
        &&& (self@[idx].is_head() && next <= usize::MAX && self@.dom().contains(next as usize))
            ==> self@[next as usize].is_head()
    }

    spec fn new_unit_requires(
        reserved: Map<usize, FracTypedPerm<PageStorageType>>,
        id: PageInfoUnique,
        unit_start: usize,
        order: usize,
    ) -> bool {
        let item = reserved[unit_start];
        let info = item.page_info().unwrap();
        let end = (1usize << order) + unit_start;
        &&& Self::_is_unit(reserved, unit_start)
        &&& item.order() == order
        &&& item.shares() == id.shares
        &&& item.total() == id.total
        &&& forall|idx: usize|
            #![trigger reserved[idx]]
            unit_start <= idx < end ==> Self::wf_basic_at(reserved[idx], idx, id)
        &&& match info {
            PageInfo::Reserved(_) => true,
            PageInfo::Compound(ci) => { false },
            PageInfo::Slab(_) | PageInfo::File(_) => true,
            PageInfo::Allocated(ai) => { Self::marked_compound(reserved, unit_start, order) },
            PageInfo::Free(fi) => { Self::marked_compound(reserved, unit_start, order) },
        }
    }

    pub closed spec fn wf_unit(&self) -> bool {
        &&& Self::new_unit_requires(
            self@,
            self.id(),
            self.unit_start,
            self.order(),
        )
        //&&& self.npages() == 1usize << self.order()

    }

    pub closed spec fn remove(&self, idx: usize) -> PageInfoDb {
        PageInfoDb {
            unit_start: self.unit_start,
            id: self.id,
            reserved: self@.remove_keys(self.dom_at(idx)),
        }
    }

    #[verifier(opaque)]
    pub closed spec fn restrict(&self, idx: usize) -> PageInfoDb {
        if self@[idx].is_head() {
            PageInfoDb {
                unit_start: idx,
                id: self.id(),
                reserved: self@.restrict(self.dom_at(idx)),
            }
        } else {
            PageInfoDb::empty(self.id)
        }
    }

    #[verifier::type_invariant]
    pub closed spec fn wf(&self) -> bool {
        &&& forall|idx: usize|
            #![trigger self@[idx]]
            self@.dom().contains(idx) && self@[idx].is_head() ==> {
                &&& idx + self@[idx].size() <= usize::MAX + 1
            }
        &&& !self.is_unit() ==> forall|idx: usize|
            #![trigger self@[idx]]
            self@.dom().contains(idx) ==> {
                &&& self.wf_follows(idx)
                &&& self@[idx].is_head() ==> self.restrict(idx).wf_unit()
                &&& self.wf_basic(idx)
            }
        &&& self.is_unit() ==> self.wf_unit()
    }

    pub closed spec fn empty(id: PageInfoUnique) -> PageInfoDb {
        PageInfoDb { unit_start: 0, id, reserved: Map::empty() }
    }

    pub closed spec fn _info_dom(&self, order: usize) -> Set<usize> {
        self@.dom().filter(|i| self@[i].order() == order)
    }

    #[verifier(opaque)]
    pub closed spec fn nr_page(&self, order: usize) -> nat {
        self._info_dom(order).len()
    }

    proof fn tracked_nr_page_pair(tracked &self, order: usize, order2: usize)
        requires
            order != order2,
        ensures
            self.nr_page(order) + self.nr_page(order2) <= self.npages(),
    {
        use_type_invariant(self);
        self.lemma_nr_page_pair(order, order2);
    }

    proof fn lemma_nr_page_pair(&self, order: usize, order2: usize)
        requires
            self.wf(),
            order != order2,
        ensures
            self.nr_page(order) + self.nr_page(order2) <= self.dom().len(),
    {
        reveal(PageInfoDb::nr_page);
        let s1 = self._info_dom(order);
        let s2 = self._info_dom(order2);
        assert(s1.disjoint(s2));
        vstd::set_lib::lemma_set_disjoint_lens(s1, s2);
        let s = s1 + s2;
        assert(s.subset_of(self@.dom()));
    }

    proof fn lemma_nr_page_npages(&self, order: usize)
        requires
            self.wf(),
        ensures
            self.nr_page(order) <= self.npages(),
    {
        reveal(PageInfoDb::nr_page);
        assert(self._info_dom(order).subset_of(self@.dom()));
    }

    spec fn const_nr_page(npages: nat, order: usize) -> nat {
        if order < MAX_ORDER && (1usize << order) == npages {
            npages
        } else {
            0
        }
    }

    proof fn tracked_unit_nr_pages(tracked &self)
        requires
            self.is_unit(),
        ensures
            forall|order| #[trigger]
                self.nr_page(order) == Self::const_nr_page(self.npages(), order),
            self.npages() == 1usize << (self@[self.unit_start()].order()),
    {
        use_type_invariant(self);
        self.proof_unit_nr_page();
    }

    proof fn proof_unit_nr_page(&self)
        requires
            self.wf(),
            self.is_unit(),
        ensures
            forall|order| #[trigger]
                self.nr_page(order) == Self::const_nr_page(self.npages(), order),
            self.npages() == 1usize << (self@[self.unit_start()].order()),
    {
        reveal(PageInfoDb::nr_page);

        assert(1usize << self@[self.unit_start()].order() == self.npages()) by {
            lemma_set_usize_range(
                self.unit_start,
                self.unit_start + (1usize << self@[self.unit_start()].order()),
            );
        }
        assert forall|order| #[trigger]
            self.nr_page(order) == Self::const_nr_page(self.npages(), order) by {
            if (order < MAX_ORDER && (1usize << order) == self.npages()) {
                assert(order == self@[self.unit_start()].order());
            }
            self.lemma_unit_nr_page(order);
        }
    }

    proof fn tracked_unit_nr_page(tracked &self, order: usize)
        requires
            self.is_unit(),
        ensures
            self.nr_page(order) == Self::const_nr_page(self.npages(), order),
            self.npages() == 1usize << (self@[self.unit_start()].order()),
    {
        use_type_invariant(self);
        self.lemma_unit_nr_page(order);
    }

    proof fn lemma_unit_nr_page(&self, order: usize)
        requires
            self.wf(),
            self.is_unit(),
        ensures
            self.nr_page(order) == Self::const_nr_page(self.npages(), order),
            self.npages() == 1usize << (self@[self.unit_start()].order()),
    {
        reveal(PageInfoDb::nr_page);
        if order == self@[self.unit_start()].order() {
            assert(self._info_dom(order) =~= self@.dom());
        } else {
            assert(self._info_dom(order).is_empty());
        }
        lemma_set_usize_range(self.unit_start, self.unit_start + (1usize << self.order()));
    }

    proof fn lemma_restrict(&self, idx: usize)
        requires
            self.wf(),
            self.is_head(idx),
            self@.dom().contains(idx),
        ensures
            self.restrict(idx).wf(),
            self.restrict(idx).is_unit(),
            self.restrict(idx)@.dom() =~= self.dom_at(idx),
            forall|i|
                #![trigger self@[i]]
                #![trigger self.restrict(idx)@[i]]
                idx <= i < idx + self@[idx].size() ==> self.restrict(idx)@[i] == self@[i],
    {
        reveal(PageInfoDb::restrict);
        if self.is_unit() {
            assert(idx == self.unit_start);
            assert(self.restrict(idx)@ =~= self@);
            assert(self.restrict(idx).wf());
        } else {
            assert(self.restrict(idx).is_unit());
            assert(self.restrict(idx).wf_unit());
        }
    }

    spec fn new(
        unit_start: usize,
        id: PageInfoUnique,
        reserved: Map<usize, FracTypedPerm<PageStorageType>>,
    ) -> Self {
        PageInfoDb { unit_start, id, reserved }
    }

    pub open spec fn ens_split_inner(&self, left: Self, right: Self) -> bool {
        &&& left.dom().disjoint(right.dom())
        &&& left@ =~= self@.restrict(left.dom())
        &&& right@ =~= self@.restrict(right.dom())
        &&& left.dom() + right.dom() =~= self.dom()
        &&& left.id() == self.id()
        &&& right.id() == self.id()
    }

    pub open spec fn ens_split(&self, left: Self, right: Self) -> bool {
        &&& left.dom().disjoint(right.dom())
        &&& left@ == self@.restrict(left.dom())
        &&& right@ == self@.restrict(right.dom())
        &&& left.dom() + right.dom() == self.dom()
        &&& left.id() == self.id()
        &&& right.id() == self.id()
    }

    /** Constructors **/
    proof fn tracked_empty(id: PageInfoUnique) -> (tracked ret: PageInfoDb)
        ensures
            ret == PageInfoDb::empty(id),
    {
        let tracked reserved = Map::tracked_empty();
        PageInfoDb { unit_start: 0, id, reserved }
    }

    proof fn proof_split_nr_page(&self, left: Self, right: Self)
        requires
            self.wf(),
            self.ens_split_inner(left, right),
        ensures
            forall|order: usize| #[trigger]
                self.nr_page(order) == left.nr_page(order) + right.nr_page(order),
    {
        assert forall|order: usize| #[trigger]
            self.nr_page(order) == left.nr_page(order) + right.nr_page(order) by {
            self.lemma_split_nr_page(left, right, order);
        }
    }

    proof fn lemma_split_nr_page(&self, left: Self, right: Self, order: usize)
        requires
            self.wf(),
            self.ens_split_inner(left, right),
        ensures
            self.nr_page(order) == left.nr_page(order) + right.nr_page(order),
    {
        reveal(PageInfoDb::nr_page);
        let s1 = left._info_dom(order);
        let s2 = right._info_dom(order);
        let s = self._info_dom(order);
        vstd::set_lib::lemma_set_disjoint_lens(s1, s2);
        assert(s1 + s2 =~= s);
    }

    proof fn lemma_remove(&self, i: usize)
        requires
            self.wf(),
            self.dom().contains(i),
            self.is_head(i),
        ensures
            self.remove(i).npages() == self.npages() - self@[i].size(),
            forall|j|
                self.is_head(j) && i != j && self.dom().contains(j) ==> #[trigger] self.remove(
                    i,
                ).restrict(j) == self.restrict(j),
    {
        let left = self.remove(i);
        assert forall|j|
            self.is_head(j) && i != j && self.dom().contains(j) implies #[trigger] left.restrict(j)
            == self.restrict(j) by {
            self.lemma_remove_restrict(i, j);
        }
        let s = self.dom_at(i);
        assert(left.dom() + s =~= self@.dom());
        vstd::set_lib::lemma_set_disjoint_lens(left.dom(), s);
        lemma_set_usize_range(i, i + self@[i].size());
    }

    spec fn merge(&self, other: Self) -> Self {
        PageInfoDb {
            unit_start: self.unit_start,
            id: self.id,
            reserved: self@.union_prefer_right(other@),
        }
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_merge_wf(&self, other: Self)
        requires
            self.wf(),
            other.wf(),
            other.is_unit(),
            self.id() == other.id(),
            self.dom().disjoint(other.dom()),
        ensures
            self.merge(other).wf(),
    {
        reveal(PageInfoDb::restrict);
        let new = self.merge(other);

        if !new.is_unit() {
            assert forall|idx: usize| #![trigger new@[idx]] new@.dom().contains(idx) implies {
                &&& new.wf_follows(idx)
            } by {
                let next = idx + new@[idx].size();
                let item = new@[next as usize];
                assert(other@[other.unit_start].is_head());
                if (new@[idx].is_head() && next <= usize::MAX && new@.dom().contains(
                    next as usize,
                )) {
                    if other.unit_start <= next < other.end() {
                        if (!item.is_head()) {
                            assert(new@[next as usize] == other@[next as usize]);
                            assert(next > other.unit_start);
                            assert(self.dom().contains((next - 1) as usize));
                        }
                    } else if other.unit_start <= idx < other.end() {
                        assert(item.is_head());
                    }
                }
            }
            assert forall|idx: usize|
                #![trigger new@[idx]]
                new@.dom().contains(idx) && new@[idx].is_head() implies {
                new.restrict(idx).wf_unit()
            } by {
                if self.dom().contains(idx) {
                    self.lemma_restrict(idx);
                    assert(self.restrict(idx).wf());
                    assert(self.restrict(idx)@ =~= new.restrict(idx)@);
                } else {
                    assert(other.dom().contains(idx));
                    other.lemma_restrict(idx);
                    assert(other.restrict(idx).wf());
                    assert(other.restrict(idx)@ =~= new.restrict(idx)@);
                }
            }
        } else {
            if new.unit_start() != other.unit_start() {
                assert(other.dom().subset_of(new.dom()));
                assert(other@[other.unit_start()].is_head());
                assert(new@[other.unit_start()].is_head());
            }
            assert(new@ =~= other@);
        }
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_remove_wf(&self, i: usize)
        requires
            self.wf(),
            self.dom().contains(i),
            self.is_head(i),
        ensures
            self.remove(i).wf(),
    {
        reveal(PageInfoDb::restrict);
        self.lemma_restrict(i);
        lemma_set_usize_range(i, i + self@[i].size());
        broadcast use lemma_set_usize_range;

        self.lemma_remove(i);
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_remove_restrict(&self, i: usize, j: usize)
        requires
            self.wf(),
            self.dom().contains(i),
            self.dom().contains(j),
            self.is_head(i),
            self.is_head(j),
            i != j,
        ensures
            self.remove(i).restrict(j) == self.restrict(j),
    {
        reveal(PageInfoDb::restrict);
        self.lemma_head_no_overlap(i, j);
        assert(self.remove(i).restrict(j)@ =~= self.restrict(j)@);
    }

    broadcast proof fn lemma_head_no_overlap(&self, i: usize, j: usize)
        requires
            self.wf(),
            self.is_head(i),
            self.is_head(j),
            i != j,
            self.dom().contains(i),
            self.dom().contains(j),
        ensures
            #![trigger self@[i], self@[j]]
            i + self@[i].size() <= j || i >= j + self@[j].size(),
    {
        reveal(PageInfoDb::restrict);
        self.lemma_restrict(i);
        self.lemma_restrict(j);
    }

    proof fn lemma_wf_recursive(&self)
        requires
            self.wf(),
        ensures
            forall|idx| #![trigger self@[idx]] self.dom().contains(idx) ==> self.restrict(idx).wf(),
    {
        reveal(PageInfoDb::restrict);
        assert forall|idx| #![trigger self@[idx]] self.dom().contains(idx) implies self.restrict(
            idx,
        ).wf() by {
            if self.is_head(idx) {
                self.lemma_restrict(idx);
            }
        }
    }

    proof fn tracked_new_unit(
        order: usize,
        unit_start: usize,
        id: PageInfoUnique,
        tracked reserved: Map<usize, FracTypedPerm<PageStorageType>>,
    ) -> (tracked ret: Self)
        requires
            order < MAX_ORDER,
            unit_start + (1usize << order) <= usize::MAX + 1,
            reserved.dom() =~= Set::new(|k| unit_start <= k < unit_start + (1usize << order)),
            reserved[unit_start].is_head(),
            reserved[unit_start].order() == order,
            PageInfoDb::new_unit_requires(reserved, id, unit_start, order),
        ensures
            ret.is_unit(),
            ret == PageInfoDb::new(unit_start, id, reserved),
            ret@ == reserved,
            ret.npages() == (1usize << order),
            forall|order| #[trigger] ret.nr_page(order) == Self::const_nr_page(ret.npages(), order),
    {
        reveal(PageInfoDb::restrict);
        lemma_set_usize_range(unit_start, unit_start + (1usize << order));
        let tracked ret = PageInfoDb { unit_start, id, reserved };
        ret.proof_unit_nr_page();
        ret
    }

    proof fn tracked_remove_unit(tracked &mut self, idx: usize) -> (tracked unit: PageInfoDb)
        requires
            old(self).dom().contains(idx),
            old(self).is_head(idx),
        ensures
            old(self).ens_split(*self, unit),
            self@ == old(self)@.remove_keys(unit@.dom()),
            self.id() == old(self).id(),
            self.npages() == old(self).npages() - old(self)@[idx].size(),
            unit.is_unit(),
            unit.unit_start() == idx,
            forall|order: usize| #[trigger]
                old(self).nr_page(order) == self.nr_page(order) + unit.nr_page(order),
    {
        use_type_invariant(&*self);
        reveal(PageInfoDb::restrict);
        self.lemma_restrict(idx);
        self.lemma_remove(idx);
        self.lemma_remove_wf(idx);
        let order = self@[idx].order();
        let s = self.dom_at(idx);
        let tracked ret = self.reserved.tracked_remove_keys(s);
        assert(ret.dom() == s);
        assert(order == ret[idx].order());
        let tracked ret = PageInfoDb::tracked_new_unit(order, idx, self.id(), ret);
        assert(old(self).ens_split_inner(*self, ret));
        old(self).proof_split_nr_page(*self, ret);
        ret
    }

    proof fn tracked_remove_and_merge_shares(tracked &mut self, tracked unit: &mut PageInfoDb)
        requires
            old(self).dom().contains(old(unit).unit_start()),
            old(unit).is_unit(),
            old(unit).id().ptr_data == old(self).id().ptr_data,
        ensures
            unit.is_unit(),
            unit.npages() == old(unit).npages(),
            unit.unit_start() == old(unit).unit_start(),
            unit.id() == old(unit).id().update_shares(
                old(unit).id().shares + old(self).id().shares,
            ),
            unit.unit_head()@ == old(unit).unit_head()@.update_shares(unit.id().shares),
            self@ == old(self)@.remove_keys(unit@.dom()),
            self.id() == old(self).id(),
            forall|order: usize| #[trigger] old(unit).nr_page(order) == unit.nr_page(order),
            forall|order: usize| #[trigger]
                old(self).nr_page(order) == self.nr_page(order) + unit.nr_page(order),
    {
        let idx = unit.unit_start();
        use_type_invariant(&*self);
        use_type_invariant(&*unit);

        assert(self@[idx].ptr() == unit@[idx].ptr());
        self.reserved.tracked_borrow(idx).is_same(unit.reserved.tracked_borrow(idx));

        assert(self@[idx].valid());
        assert(unit@[idx].valid());
        unit.tracked_unit_nr_pages();
        let order = unit@[idx].order();
        let tracked unit2 = self.tracked_remove_unit(idx);
        unit2.tracked_unit_nr_pages();
        let tracked mut tmp = PageInfoDb::tracked_empty(arbitrary());
        tracked_swap(unit, &mut tmp);
        let tracked PageInfoDb { unit_start, mut reserved, mut id } = tmp;
        tracked_map_merge_right_shares(&mut reserved, unit2.reserved);
        id.shares = id.shares + unit2.id().shares;
        *unit = PageInfoDb::tracked_new_unit(order, unit_start, id, reserved);
    }

    #[verifier(spinoff_prover)]
    proof fn tracked_insert_shares(tracked &mut self, tracked unit: &mut PageInfoDb)
        requires
            old(unit).is_unit(),
            0 < old(self).id().shares < old(unit).id().shares,
            old(self).dom().disjoint(old(unit).dom()),
            old(self).id() == old(unit).id().update_shares(old(self).id().shares),
        ensures
            unit.is_unit(),
            unit.unit_head()@ == old(unit).unit_head()@.update_shares(unit.id().shares),
            unit.id() == old(unit).id().update_shares(
                (old(unit).id().shares - old(self).id().shares) as nat,
            ),
            unit.unit_start() == old(unit).unit_start(),
            self.id() == old(self).id(),
            self@.dom() == old(self)@.dom() + old(unit)@.dom(),
            self@ =~= old(self)@.union_prefer_right(self@.restrict(unit@.dom())),
            forall|order: usize| #[trigger] old(unit).nr_page(order) == unit.nr_page(order),
            forall|order: usize| #[trigger]
                self.nr_page(order) == old(self).nr_page(order) + unit.nr_page(
                    order,
                ),
    //self.restrict(unit.unit_start()).unit_head()@ == old(unit).unit_head()@.update_shares(self.id().shares),

    {
        use_type_invariant(&*unit);
        unit.tracked_unit_nr_pages();
        let tracked new_unit = unit.tracked_split_shares(self.id().shares);
        assert(old(unit).dom() == new_unit.dom());
        use_type_invariant(&*self);
        use_type_invariant(&new_unit);
        self.lemma_merge_wf(new_unit);
        new_unit.tracked_unit_nr_pages();
        unit.tracked_unit_nr_pages();
        self.reserved.tracked_union_prefer_right(new_unit.reserved);
        self.proof_split_nr_page(*old(self), new_unit);
        assert(self@.dom() =~= old(self)@.dom() + old(unit)@.dom());
    }

    proof fn tracked_split_shares(tracked &mut self, shares: nat) -> (tracked unit: PageInfoDb)
        requires
            old(self).is_unit(),
            0 < shares < old(self).id().shares,
        ensures
            self.is_unit(),
            self.unit_head()@ == old(self).unit_head()@.update_shares(self.id().shares),
            unit.unit_head()@ == old(self).unit_head()@.update_shares(shares),
            self.unit_start() == old(self).unit_start() == unit.unit_start(),
            self.id() == old(self).id().update_shares((old(self).id().shares - shares) as nat),
            unit.is_unit(),
            unit.id() == old(self).id().update_shares(shares),
            forall|order: usize| #[trigger]
                old(self).nr_page(order) == self.nr_page(order) == unit.nr_page(order),
    {
        use_type_invariant(&*self);
        self.proof_unit_nr_page();
        let idx = self.unit_start();
        let order = self@[idx].order();
        let tracked mut tmp = PageInfoDb::tracked_empty(arbitrary());
        tracked_swap(self, &mut tmp);
        let tracked PageInfoDb { unit_start, mut reserved, mut id } = tmp;
        let tracked new_reserved = tracked_map_shares(&mut reserved, shares);
        let mut ret_id = id;
        ret_id.shares = shares;
        id.shares = (id.shares - shares) as nat;
        *self = PageInfoDb::tracked_new_unit(order, unit_start, id, reserved);
        use_type_invariant(&*self);
        self.proof_unit_nr_page();
        PageInfoDb::tracked_new_unit(order, unit_start, ret_id, new_reserved)
    }
}

} // verus!
/*
spec fn ens_split_restrict(&self, idx: usize, left: Self, right: Self) -> bool {
        forall|i|
            #![trigger self.restrict(i)]
            self.unit_start() <= i < self.end() ==> self.restrict(i) == if i < idx {
                left.restrict(i)
            } else {
                right.restrict(i)
            }
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_split_restrict_view(&self, idx: usize, left: Self, right: Self)
        requires
            self.wf(),
            left.wf(),
            right.wf(),
            self.ens_split(idx, left, right),
            self.unit_start() <= idx < self.unit_start() + self.npages(),
            self@[idx].is_head(),
        ensures
            self.ens_split_restrict(idx, left, right),
    {
        reveal(PageInfoDb::restrict);
        assert forall|i|
            #![trigger self.restrict(i)]
            self.unit_start() <= i < self.end() implies self.restrict(i) == if i < idx {
            left.restrict(i)
        } else {
            right.restrict(i)
        } by {
            if self@[i].is_head() {
                self.lemma_split_restrict(idx, left, right, i);
            }
        }
    }

    proof fn lemma_split_restrict(&self, idx: usize, left: Self, right: Self, i: usize)
        requires
            self.wf(),
            left.wf(),
            right.wf(),
            self.ens_split(idx, left, right),
            self.unit_start() <= idx < self.unit_start() + self.npages(),
            self.unit_start() <= i < self.unit_start() + self.npages(),
            self@[i].is_head(),
            self@[idx].is_head(),
        ensures
            self.restrict(i) == if i < idx {
                left.restrict(i)
            } else {
                right.restrict(i)
            },
    {
        reveal(PageInfoDb::restrict);
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
        reveal(PageInfoDb::nr_page);
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

    pub open spec fn ens_split(&self, idx: usize, left: Self, right: Self) -> bool {
        &&& left@ =~= self@.restrict(Set::new(|k: usize| k < idx))
        &&& left.id() == self.id()
        &&& left.unit_start() == self.unit_start()
        &&& left.npages() == idx - self.unit_start()
        &&& right@ =~= self@.restrict(Set::new(|k: usize| k >= idx))
        &&& right.id() == self.id()
        &&& right.unit_start() == idx
        &&& right.npages() + left.npages() == self.npages()
    }

    pub open spec fn ens_merge(&self, left: Self, right: Self) -> bool {
        //&&& self@ == left@.union_prefer_right(right@)
        &&& self@ =~= Map::new(
            |k: usize| self.unit_start() <= k < self.unit_start() + self.npages(),
            |k: usize|
                if k < right.unit_start() {
                    left@[k]
                } else {
                    right@[k]
                },
        )
        &&& self.id() == left.id()
        &&& self.unit_start() == left.unit_start()
        &&& self.npages() == left.npages() + right.npages()
    }

    pub open spec fn ens_merge3(&self, left: Self, mid: Self, right: Self) -> bool {
        &&& self@ =~= Map::new(
            |k: usize| self.unit_start() <= k < self.unit_start() + self.npages(),
            |k: usize|
                if k < mid.unit_start() {
                    left@[k]
                } else if k < mid.unit_start() + mid.npages() {
                    mid@[k]
                } else {
                    right@[k]
                },
        )
        &&& self.id() == left.id()
        &&& self.unit_start() == left.unit_start()
        &&& self.npages() == left.npages() + mid.npages() + right.npages()
    }

    #[verifier(rlimit(4))]
    proof fn tracked_split(tracked self, idx: usize) -> (tracked ret: UnitPageInfo)
        requires
            self.is_head(idx),
            self.unit_start() <= idx < self.unit_start() + self.npages(),
        ensures
            self.ens_split(idx, ret.0, ret.1),
            self.ens_split_restrict(idx, ret.0, ret.1),
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
    #[verifier(rlimit(6))]
    proof fn _tracked_split(tracked self, idx: usize) -> (tracked ret: (PageInfoDb, PageInfoDb))
        requires
            self.is_head(idx),
            self.unit_start() <= idx < self.unit_start() + self.npages(),
        ensures
            self.ens_split(idx, ret.0, ret.1),
    {
        reveal(PageInfoDb::restrict);
        use_type_invariant(&self);
        self.lemma_restrict(idx);
        let tracked PageInfoDb { npages, unit_start, id, mut reserved } = self;
        if idx != unit_start {
            self.lemma_head_no_overlap(unit_start, idx);
        }
        let tracked left_reserved = reserved.tracked_remove_keys(
            Set::new(|k| unit_start <= k < idx),
        );
        let left = PageInfoDb::new((idx - unit_start) as usize, unit_start, id, left_reserved);
        assert forall|i| unit_start <= i < idx && (#[trigger] left@[i]).is_head() implies i
            + left@[i].size() <= idx && left.restrict(i) == self.restrict(i) by {
            self.lemma_head_no_overlap(i, idx);
            assert(left.restrict(i)@ =~= self.restrict(i)@);
        }
        let tracked left = PageInfoDb {
            npages: (idx - unit_start) as usize,
            unit_start: unit_start,
            id: self.id,
            reserved: left_reserved,
        };

        let right = PageInfoDb::new((npages - (idx - unit_start)) as usize, idx, id, reserved);
        assert forall|i|
            right.unit_start <= i < right.unit_start + right.npages && (!right.is_unit()
                && right.is_head(i)) implies #[trigger] right.restrict(i) == self.restrict(i) by {
            assert(right.restrict(i)@ =~= self.restrict(i)@);
            assert(right.restrict(i) == self.restrict(i));
        }
        let tracked right = PageInfoDb {
            npages: (npages - (idx - unit_start)) as usize,
            unit_start: idx,
            id: self.id,
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
            old(self).unit_start() + old(self).npages() == mid.unit_start(),
            right.npages() > 0 ==> mid.unit_start() + mid.npages() == right.unit_start(),
            old(self).id() == mid.id(),
            old(self).id() == right.id(),
        ensures
            self.ens_merge3(*old(self), mid, right),
            forall|i|
                #![trigger self.restrict(i)]
                self.unit_start() <= i < self.end() ==> self.restrict(i) == if i < mid.unit_start() {
                    old(self).restrict(i)
                } else if mid.unit_start() <= i < mid.unit_start() + mid.npages() {
                    mid.restrict(i)
                } else {
                    right.restrict(i)
                },
            forall|order| #[trigger]
                self.nr_page(order) == (old(self).nr_page(order) + mid.nr_page(order)
                    + right.nr_page(order)),
    {
        reveal(PageInfoDb::restrict);
        reveal(PageInfoDb::nr_page);
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
            assert(self@ =~= self@.union_prefer_right(right@));
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
    #[verifier(rlimit(6))]
    proof fn tracked_extract(tracked self, idx: usize) -> (tracked ret: (
        PageInfoDb,
        PageInfoDb,
        PageInfoDb,
    ))
        requires
            self.is_head(idx),
            self.unit_start() <= idx < self.unit_start() + self.npages(),
        ensures
            ret.1 == self.restrict(idx),
            ret.1.is_unit(),
            ret.1.id() == self.id(),
            ret.1.npages() == self@[idx].size(),
            ret.1.unit_start() == idx,
            ret.0@ =~= self@.restrict(Set::new(|k: usize| k < idx)),
            ret.0.id() == self.id(),
            ret.0.unit_start() == self.unit_start(),
            ret.0.npages() == idx - self.unit_start(),
            ret.2@ =~= self@.restrict(Set::new(|k: usize| k >= idx + self@[idx].size())),
            ret.2.id() == self.id(),
            ret.2.npages() > 0 ==> ret.2.unit_start() == idx + self@[idx].size(),
            ret.2.npages() + ret.0.npages() + ret.1.npages() == self.npages(),
            forall|order: usize| #[trigger]
                self.nr_page(order) == ret.0.nr_page(order) + ret.1.nr_page(order) + ret.2.nr_page(
                    order,
                ),
            forall|i|
                #![trigger self.restrict(i)]
                self.unit_start() <= i < self.end() ==> self.restrict(i) == if i < idx {
                    ret.0.restrict(i)
                } else if ret.1.unit_start() <= i < ret.1.unit_start() + ret.1.npages() {
                    ret.1.restrict(i)
                } else {
                    ret.2.restrict(i)
                },
    {
        //reveal(PageInfoDb::restrict);
        reveal(PageInfoDb::nr_page);
        use_type_invariant(&self);
        let start = self.unit_start();
        let end = self.end();
        let old_self = self;
        assert(self@[idx].is_valid_pginfo());
        assert(self@[idx].order() < MAX_ORDER);
        assert(self@[idx].size() > 0);
        let tracked (left, right) = self.tracked_split(idx);
        use_type_invariant(&right);
        let tracked (mid, right) = if idx + self@[idx].size() < self.end() {
            assert(right.restrict(idx)@ =~= old_self.restrict(idx)@);
            let tracked (mid, right2) = right.tracked_split((idx + self@[idx].size()) as usize);
            assert(mid == right.restrict(idx)) by {
                reveal(PageInfoDb::restrict);
                assert(mid@ =~= right.restrict(idx)@)
            }
            assert(mid.npages() == self@[idx].size());
            assert forall|i|
                #![trigger self.restrict(i)]
                self.unit_start() < i < self.end() implies self.restrict(i) == if i < idx {
                left.restrict(i)
            } else if mid.unit_start() <= i < mid.unit_start() + mid.npages() {
                mid.restrict(i)
            } else {
                right2.restrict(i)
            } by {
                let r = right.restrict(i);
            }
            (mid, right2)
        } else {
            assert(right.npages() == self@[idx].size());
            assert(idx + self@[idx].size() == end);
            assert(right@ =~= self.restrict(idx)@) by {
                reveal(PageInfoDb::restrict);
            }
            let tracked empty = PageInfoDb::tracked_empty(self.id);
            assert(empty@.is_empty());
            (right, empty)
        };
        assert(mid == self.restrict(idx)) by {
            reveal(PageInfoDb::restrict);
        }
        (left, mid, right)
    }

    proof fn tracked_borrow(tracked &self, idx: usize) -> (tracked ret: &FracTypedPerm<
        PageStorageType,
    >)
        requires
            self.unit_start() <= idx < self.unit_start() + self.npages(),
        ensures
            *ret == self@[idx],
            ret.is_valid_pginfo(),
            ret.ptr() == self.ptr(idx),
    {
        use_type_invariant(&self);
        self.reserved.tracked_borrow(idx)
    }

    proof fn tracked_merge(tracked &mut self, tracked other: Self)
        requires
            old(self).unit_start() + old(self).npages() == other.unit_start(),
            old(self).id() == other.id(),
        ensures
            forall|order| #[trigger]
                self.nr_page(order) == (old(self).nr_page(order) + other.nr_page(order)),
            self.ens_merge(*old(self), other),
            self.ens_split_restrict(other.unit_start(), *old(self), other),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        self._tracked_merge(other);
        use_type_invariant(&*self);
        let idx = other.unit_start();
        let left = *old(self);
        self.proof_split_nr_page(idx, left, other);
        if other.npages() > 0 {
            self.lemma_split_restrict_view(idx, left, other);
        } else {
            assert(other@.is_empty());
            assert(self@ =~= old(self)@);
        }
    }

    #[verifier(spinoff_prover)]
    #[verifier(rlimit(8))]
    proof fn _tracked_merge(tracked &mut self, tracked other: Self)
        requires
            old(self).unit_start() + old(self).npages() == other.unit_start(),
            old(self).id() == other.id(),
        ensures
            self.ens_merge(*old(self), other),
    {
        reveal(PageInfoDb::restrict);
        let old_self = *self;
        let tracked mut tmp = PageInfoDb::tracked_empty(self.id);
        tracked_swap(self, &mut tmp);
        use_type_invariant(&tmp);
        use_type_invariant(&other);
        let tracked PageInfoDb { mut npages, unit_start, id, mut reserved } = tmp;
        npages = (npages + other.npages()) as usize;
        reserved.tracked_union_prefer_right(other.reserved);
        let new = PageInfoDb::new(npages, unit_start, id, reserved);
        assert forall|i| unit_start <= i < unit_start + npages implies (reserved[i]).ptr()
            == #[trigger] new.ptr(i) && if (!new.is_unit() && new.is_head(i)) {
            new.restrict(i).wf()
        } else {
            true
        } by {
            if i >= unit_start + old(self).npages {
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
        *self = PageInfoDb { npages, unit_start, id, reserved };
    }

    #[verifier(spinoff_prover)]
    #[verifier(rlimit(4))]
    proof fn tracked_dealloc(tracked &mut self, perm: Self)
        requires
            old(self).is_unit(),
            perm.is_unit(),
            old(self).id() == perm.id(),
            old(self).unit_start() == perm.unit_start(),
            old(self).npages() == perm.npages(),
        ensures
            self.writable(),
            self.is_unit(),
            self.id() == old(self).id(),
            self.unit_start() == old(self).unit_start(),
            self.npages() == old(self).npages(),
            forall|order: usize| self.nr_page(order) == old(self).nr_page(order),
    {
    }

    #[verifier(spinoff_prover)]
    #[verifier(rlimit(4))]
    proof fn tracked_alloc(tracked &mut self, idx: usize) -> (tracked ret: RawDeallocPerm)
        requires
            old(self)@[idx].is_head(),
            !old(self)@[idx].is_free(),
            old(self).unit_start() <= idx < old(self).unit_start() + old(self).npages(),
            old(self).restrict(idx).writable(),
        ensures
            self.id() == old(self).id(),
            self.unit_start() == old(self).unit_start(),
            self.npages() == old(self).npages(),
            self.restrict(idx).is_readonly_allocator_shares(),
            ret@.is_readonly_dealloc_shares(),
            forall|order: usize| #[trigger] self.nr_page(order) == old(self).nr_page(order),
    {
        reveal(PageInfoDb::restrict);
        reveal(PageInfoDb::is_readonly_allocator_shares);
        reveal(PageInfoDb::is_readonly_dealloc_shares);
        let old_self = *old(self);
        let tracked mut tmp = PageInfoDb::tracked_empty(self.id);
        tracked_swap(self, &mut tmp);
        let tracked (mut left, mut mid, right) = tmp.tracked_extract(idx);
        *self = left;
        use_type_invariant(&mid);
        mid.proof_unit_nr_page();
        let order = mid@[idx].order();
        let tracked PageInfoDb { npages, unit_start, id, mut reserved } = mid;
        let allocated_npages = self@[idx].size();
        let tracked allocated_reserved = tracked_map_shares(&mut reserved, DEALLOC_PGINFO_SHARES);
        let tracked new_mid = PageInfoDb::tracked_new_unit(order, unit_start, id, reserved);
        self.tracked_merge_extracted(new_mid, right);
        assert(!new_mid.writable());
        //new_mid.proof_unit_nr_page();
        assert(self.restrict(idx)@ =~= new_mid@);
        let tracked ret = PageInfoDb::tracked_new_unit(
            order,
            unit_start,
            id,
            allocated_reserved,
        );
        assert(ret.is_unit());
        reveal(RawDeallocPerm::wf);
        RawDeallocPerm(ret)
    }
}

*/
