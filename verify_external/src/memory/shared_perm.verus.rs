use vstd::prelude::*;
verus! {
/// A tracked struct for readonly data.
/// The ownership of T is owned by all created read-only nodes.
///
/// ** creating read-only nodes **
///
/// Initial state: Node 0 is the exclusive live readonly node.
/// ```
///        1 (live)
/// ```
///
/// Step 1: Call `copy` on Node 0. Node 0 is freed, and two child nodes 1 and 2 are created.
/// ```
///        1 (freed)
///        /     \
///    1/2 (live) 1/2 (live)
/// ```
///
/// Step 2: Call `copy` on Node 1. Node 1 is freed, and two child nodes 3 and 4 are created.
/// ```
///        1 (freed)
///        /     \
///    1/2 (freed) 1/2 (live)
///    /    \
///  1/4 (live) 1/4 (live)
/// ```
///
/// **Recovery process:**
/// - To recover node1, call `drop(Node3, Node4)`. Node3 and Node4 are freed, and Node1 is recovered as live.
/// ```
///        1 (freed)
///        /     \
///    1/2 (live) 1/2 (live)
///    /    \
///  1/4 (freed) 1/4 (freed)
/// ```
///
/// - To recover node Node0, call `deref(Node1, Node2)`. B and C are dereferenced, and A is recovered as live.
/// ```
///        0 (live)
///        /     \
///    1/2 (live) 1/2 (live)
///    /    \
///  1/4 (freed) 1/4 (freed)
///
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[allow(missing_debug_implementations)]
pub tracked struct SharedPerm<T> {
    phantom: core::marker::PhantomData<T>,
    no_copy: NoCopy,
}

#[allow(missing_debug_implementations)]
pub struct SharedView<T> {
    pub perm: T,
    pub shares: int, // number of shares
}

#[allow(missing_debug_implementations)]
impl<T> SharedView<T> {
    pub open spec fn new(perm: T) -> Self {
        SharedView { perm, shares: 1 }
    }

    pub open spec fn children(&self) -> (Self, Self) {
        (
            SharedView {
                perm: self.perm, shares: self.shares * 2
            },
            SharedView {
                perm: self.perm, shares: self.shares * 2
            }
        )
    }

    pub open spec fn parent(&self) -> Self {
        SharedView { perm: self.perm, shares: self.shares / 2 }
    }
}

impl<T> SharedPerm<T> {
    pub spec fn view(&self) -> SharedView<T>;

    #[verifier::type_invariant]
    pub open spec fn inv(&self) -> bool {
        &&& self@.shares / 2 * 2 == self@.shares
        &&& self@.shares * 2 / 2 == self@.shares
    }

    // Convert T to a read-only T
    #[verifier(external_body)]
    pub proof fn tracked_new(tracked val: T) -> (tracked ret: SharedPerm<T>)
        ensures
            ret@ == SharedView::new(val),
    {
        unimplemented!()
    }

    // If self.shares == 1, it indicates an exclusive share of T.
    #[verifier(external_body)]
    pub proof fn tracked_reveal(tracked self) -> (tracked ret: T)
        requires
            self@.shares == 1,
        ensures
            ret == self@.perm,
    {
        unimplemented!()
    }

    // Divide the share into two.
    #[verifier(external_body)]
    pub proof fn tracked_share(&mut self) -> (tracked ret: SharedPerm<T>)
        ensures
            (self@, ret@) === old(self)@.children(),
    {
        unimplemented!()
    }

    // Unshare ref1 and ref2 shares and merge them into one share.
    #[verifier(external_body)]
    pub proof fn tracked_unshare(
        tracked ref1: Self,
        tracked ref2: Self,
    ) -> (tracked ret: Self)
        requires
            ref1@.parent() == ref2@.parent(),
            ref1@.perm == ref2@.perm,
        ensures
            ret@ === ref1@.parent(),
    {
        unimplemented!()
    }

    // A share have read access.
    #[verifier(external_body)]
    pub proof fn tracked_ref<'a>(tracked &self) -> (tracked pt: &'a T)
        ensures
            *pt == self@.perm,
    {
        unimplemented!()
    }
}

pub type SharedTypedPerm<T> = SharedPerm<TypedPerm<T>>;

proof fn tracked_perm_is_same<T>(tracked p1: &TypedPerm<T>, tracked p2: &TypedPerm<T>)
requires
    p1.addr() == p2.addr()
ensures
    p1 == p2,
{
    admit()
}

impl<T> SharedPerm<TypedPerm<T>> {
    // SharedPerm is readonly and thus they must pointing the same content.
    pub proof fn is_same(tracked &self, tracked other: &Self)
        requires
            self@.perm.addr() == other@.perm.addr()
        ensures
            self@.perm === other@.perm,
    {
        tracked_perm_is_same(self.tracked_ref(), other.tracked_ref())
    }
}

} // verus!
