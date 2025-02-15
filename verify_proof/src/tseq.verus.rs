use builtin_macros::*;

verus! {
use vstd::prelude::*;
#[allow(missing_debug_implementations)]
#[verifier::accept_recursive_types(T)]
pub tracked struct TrackedSeq<T> {
    map: Map<int, T>,
    ghost size: nat,
}

impl<T> TrackedSeq<T> {
    #[verifier::type_invariant]
    pub closed spec fn wf(&self) -> bool {
        forall|i| 0 <= i < self.size ==> self.map.dom().contains(i)
    }

    pub closed spec fn to_seq(&self) -> Seq<T> {
        Seq::new(self.size as nat, |i| self.map[i])
    }

    #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<T> {
        self.to_seq()
    }

    #[verifier(inline)]
    pub open spec fn last(&self) -> T {
        self@.last()
    }

    #[verifier(inline)]
    pub open spec fn len(&self) -> nat {
        self@.len()
    }

    pub proof fn tracked_empty() -> (tracked ret: TrackedSeq<T>)
        ensures
            ret.wf(),
            ret@.len() == 0,
    {
        TrackedSeq { map: Map::tracked_empty(), size: 0 }
    }

    pub proof fn tracked_push(tracked &mut self, tracked v: T)
        ensures
            self@ =~= old(self)@.push(v),
            self@.len() == old(self)@.len() + 1,
    {
        use_type_invariant(&*self);
        self.map.tracked_insert(self.size as int, v);
        self.size = self.size + 1;
    }

    pub proof fn tracked_pop(tracked &mut self) -> (tracked ret: T)
        requires
            old(self)@.len() > 0,
        ensures
            ret === old(self).last(),
            self@.len() == old(self)@.len() - 1,
            self@ =~= old(self)@.take(old(self)@.len() - 1),
    {
        use_type_invariant(&*self);
        let oldmap = self.map;
        self.size = (self.size - 1) as nat;
        assert(oldmap =~= self.map);
        self.map.tracked_remove(self.size as int)
    }
}

} // verus!
