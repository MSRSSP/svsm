use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verify_proof::frac_ptr::FracTypedPerm;
#[cfg(verus_keep_ghost)]
use vstd::simple_pptr::MemContents;

verus!{
pub trait PtrSpec {
    spec fn spec_addr(&self) -> int;
}

impl<T> PtrSpec for *const T {
    open spec fn spec_addr(&self) -> int {
        self@.addr as int
    }
}

impl<T> PtrSpec for *mut T {
    open spec fn spec_addr(&self) -> int {
        self@.addr as int
    }
}
}

#[verus_verify]
pub trait SafePtrWithFracTypedPerm<T>: PtrSpec + Sized {
    #[verus_spec(v =>
        with Tracked(perm): Tracked<&'a FracTypedPerm<T>>
        requires
            perm.addr() == self.spec_addr(),
            perm.is_init(),
        ensures
            v == perm.value(),
        opens_invariants none
        no_unwind
    )]
    fn v_borrow<'a>(self) ->  &'a T;
}

#[verus_verify]
impl<T> SafePtrWithFracTypedPerm<T> for *const T {
    /// Trusted API to borrow a reference to the value at the pointer.
    /// This is safe with verification because we have passed the tracked memory permission.
    #[inline(always)]
    #[verus_verify(external_body)]
    #[verus_spec(v =>
        with Tracked(perm): Tracked<&'a FracTypedPerm<T>>
    )]
    fn v_borrow<'a>(self) ->  &'a T {
        unsafe { &*self }
    }
}

#[verus_verify]
pub trait SafeMutPtrWithFracTypedPerm<T>: PtrSpec + Sized {
    #[verus_spec(v =>
        with Tracked(perm): Tracked<&mut FracTypedPerm<T>>
        requires
            old(perm).addr() == self.spec_addr(),
        opens_invariants none
        no_unwind
    )]
    fn v_write(self, v: T);
}

#[verus_verify]
impl<T> SafeMutPtrWithFracTypedPerm<T> for *mut T {
    /// Trusted API to borrow a reference to the value at the pointer.
    /// This is safe with verification because we have passed the tracked memory permission.
    #[inline(always)]
    #[verus_verify(external_body)]
    #[verus_spec(
        with Tracked(perm): Tracked<&mut FracTypedPerm<T>>
        ensures
            perm.ptr() == self,
            perm.opt_value() == MemContents::Init(v),
    )]
    fn v_write(self, v: T) {
        unsafe { 
            self.write(v);
        }
    }
}
