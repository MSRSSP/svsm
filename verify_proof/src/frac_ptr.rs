use state_machines_macros::*;

use vstd::prelude::*;
use vstd::raw_ptr::PointsTo;
use vstd::tokens::InstanceId;
use vstd::simple_pptr::MemContents;

use crate::frac_perm::FracPerm;

verus! {
use vstd::multiset::Multiset;
tokenized_state_machine!(addr_unique {
    fields {
        #[sharding(map)]
        pub addr_to: Map<int, Option<InstanceId>>,
        #[sharding(map)]
        pub to_addr: Map<InstanceId, Option<int>>,

        #[sharding(multiset)]
        pub ptr_readers: Multiset<(int, InstanceId)>,
    }

    #[invariant]
    pub fn ptr_readers_agrees(&self) -> bool {
        forall |addr, id| #[trigger]self.ptr_readers.contains((addr, id)) ==>
            self.addr_to[addr] === Some(id) && self.to_addr[id] === Some(addr)
    }

    #[invariant]
    pub fn dom_cover_all(&self) -> bool {
        self.addr_to.dom() =~= Set::full() &&
        self.to_addr.dom() =~= Set::full()
    }

    #[invariant]
    pub fn unique_id(&self) -> bool {
        forall |addr: int| (#[trigger]self.addr_to[addr]).is_some() ==>
            self.to_addr[self.addr_to[addr].unwrap()] == Some(addr)
    }

    transition! {
        check_ids(addr: int, id1: InstanceId, id2: InstanceId) {
            have ptr_readers >= {(addr, id1)};
            have ptr_readers >= {(addr, id2)};
            birds_eye let c1 = pre.ptr_readers.contains(((addr, id1)));
            birds_eye let c2 = pre.ptr_readers.contains(((addr, id2)));
            birds_eye let id = pre.addr_to[addr];
            assert Some(id2) == id;
            assert Some(id1) == id;
        }
    }

    #[inductive(check_ids)]
    fn check_ids_inductive(pre: Self, post: Self, addr: int, id1: InstanceId, id2: InstanceId) {
        assert(pre.ptr_readers.contains((addr, id1)));
        assert(pre.ptr_readers.contains((addr, id2)));
        assert(pre.addr_to[addr] == Some(id1));
        assert(pre.addr_to[addr] == Some(id2));
        assert(id1 == id2);
    }

    init!{
        empty() {
            init addr_to = Map::new(|addr| true, |addr|None);
            init to_addr = Map::new(|id| true, |addr|None);
            init ptr_readers = Multiset::empty();
        }
    }

    #[inductive(empty)]
    fn empty_inductive(post: Self) {
        assert(post.addr_to =~= Map::new(|addr| true, |addr|None));
    }

    transition!{
        update(addr: int, id: InstanceId) {
            remove addr_to -= [addr => None];
            remove to_addr -= [id => None];
            add addr_to += [ addr => Some(id) ];
            add to_addr += [ id => Some(addr) ];
        }
    }

    #[inductive(update)]
    fn update_inductive(pre: Self, post: Self, addr: int, id: InstanceId) {
        assert forall |addr: int| (#[trigger]post.addr_to[addr]).is_some()
        implies
            post.to_addr[post.addr_to[addr].unwrap()] == Some(addr)
        by {}
    }
}
);

// A single inst + addr_unique::addr_to, addr_unique::to_addr are created at entry.
pub struct UniqueByPtr {
    tracked inst: addr_unique::Instance,
    tracked id: addr_unique::ptr_readers,
    addr_id_map: Option<(addr_unique::addr_to, addr_unique::to_addr)>,
}

impl UniqueByPtr {
    // inst is only created once at the begining and thus all share the same inst_id;
    pub uninterp spec fn spec_uniq_inst_id() -> InstanceId;

    pub closed spec fn wf(&self) -> bool {
        &&& self.inst.id() == UniqueByPtr::spec_uniq_inst_id()
        &&& self.id.instance_id() == UniqueByPtr::spec_uniq_inst_id()
        &&& if let Some((id_map, addr_map)) = self.addr_id_map {
            &&& id_map.instance_id() == UniqueByPtr::spec_uniq_inst_id()
            &&& addr_map.instance_id() == UniqueByPtr::spec_uniq_inst_id()
        } else {
            true
        }
    }

    pub closed spec fn view(&self) -> (int, InstanceId) {
        self.id.element()
    }
}

pub struct FracTypedPerm<T> {
    p: Map<int, FracPerm<PointsTo<T>>>,
    unique: UniqueByPtr,
}

impl<T> FracTypedPerm<T> {
    pub closed spec fn view(&self) -> FracPerm<PointsTo<T>> {
        self.p[0]
    }

    pub closed spec fn shares(&self) -> nat {
        self@.shares()
    }

    pub closed spec fn total(&self) -> nat {
        self@.total()
    }

    pub closed spec fn points_to(&self) -> PointsTo<T> {
        self@@.unwrap()
    }

    #[verifier::inline]
    pub open spec fn ptr(&self) -> *mut T {
        self.points_to().ptr()
    }

    #[verifier::inline]
    pub open spec fn addr(&self) -> int {
        self.ptr() as int
    }

    #[verifier::inline]
    pub open spec fn opt_value(&self) -> MemContents<T> {
        self.points_to().opt_value()
    }

    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.points_to().is_init()
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.points_to().is_uninit()
    }

    #[verifier::inline]
    pub open spec fn value(&self) -> T {
        self.points_to().value()
    }
}

impl<T> FracTypedPerm<T> {
    #[verifier::type_invariant]
    pub closed spec fn wf(&self) -> bool {
        &&& self@.wf()
        &&& self.unique.wf()
        &&& self@.valid() ==> (self.addr(), self@.id()) == self.unique@
    }

    pub closed spec fn valid(&self) -> bool {
        &&& self@.valid()
        &&& self.wf()
        &&& self.p.dom() =~= set![0]
    }

    proof fn has_same_id(tracked &self, tracked other: &Self) 
    requires
        self.valid(),
        other.valid(),
        self.addr() == other.addr(),
    ensures
        self@.id() == other@.id(),
    {
        self.unique.inst.check_ids(self.addr(), self@.id(), other@.id(), &self.unique.id, &other.unique.id);
    }

    pub proof fn extract(tracked &mut self) -> (tracked ret: PointsTo<T>)
    requires
        old(self).valid(),
        old(self).shares() == old(self).total(),
    ensures
        ret == old(self).points_to(),
        !self.valid(),
        self.wf(),
    {
        let tracked p = self.p.tracked_remove(0);
        let tracked (ret, p) = p.extract();
        self.p.tracked_insert(0, p);
        ret
    }

    pub proof fn borrow(tracked &self) -> (tracked ret: &PointsTo<T>)
    requires
        self.valid(),
    {
        self.p.tracked_borrow(0).borrow()
    }

    pub proof fn merge(tracked &mut self, tracked other: Self)
    requires
        old(self).valid(),
        other.valid(),
        old(self).addr() == other.addr(),
        old(self).shares() + other.shares() <= old(self).total(),
    ensures
        self.wf(),
        self.addr() == old(self).addr(),
    {
        let tracked mut other = other;
        self.has_same_id(&other);
        self.p.tracked_borrow(0).is_same(&other.p.tracked_borrow(0));
        let tracked p1 = self.p.tracked_remove(0);
        let tracked p2 = other.p.tracked_remove(0);
        let tracked p = p1.merge(p2);
        self.p.tracked_insert(0, p);
    }
}
}
