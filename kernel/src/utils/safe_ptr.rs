use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verify_proof::frac_ptr::FracTypedPerm;
#[cfg(verus_keep_ghost)]
use vstd::simple_pptr::MemContents;

verus! {
pub trait PtrSpec<T> {
    spec fn spec_ptr(&self) -> *const T;
}

impl<T> PtrSpec<T> for *const T {
    open spec fn spec_ptr(&self) -> *const T {
        *self
    }
}

impl<T> PtrSpec<T> for *mut T {
    open spec fn spec_ptr(&self) -> *const T {
        *self as *const T
    }
}
}

#[verus_verify]
pub trait SafePtrWithFracTypedPerm<T>: PtrSpec<T> + Sized {
    #[verus_spec(v =>
        with Tracked(perm): Tracked<&'a FracTypedPerm<T>>
        requires
            perm.ptr() == self.spec_ptr(),
            perm.is_init(),
            perm.valid(),
        ensures
            v == perm.value(),
        opens_invariants none
        no_unwind
    )]
    unsafe fn v_borrow<'a>(self) -> &'a T;
}

#[verus_verify]
impl<T> SafePtrWithFracTypedPerm<T> for *const T {
    /// Trusted API to borrow a reference to the value at the pointer.
    /// This is safe with verification because we have passed the tracked memory permission.
    #[inline(always)]
    #[verus_spec(v =>
        with Tracked(perm): Tracked<&'a FracTypedPerm<T>>
    )]
    unsafe fn v_borrow<'a>(self) -> &'a T {
        proof_decl!{
            let tracked ptr_perm = perm.borrow();
        }
        vstd::raw_ptr::ptr_ref(self, verus_exec_expr!(Tracked(&ptr_perm)))
    }
}

#[verus_verify]
pub trait SafeMutPtrWithFracTypedPerm<T>: PtrSpec<T> + Sized {
    #[verus_spec(v =>
        with Tracked(perm): Tracked<&mut FracTypedPerm<T>>
        requires
            old(perm).ptr() == self.spec_ptr(),
            old(perm).writable(),
            old(perm).valid(),
        opens_invariants none
        no_unwind
    )]
    unsafe fn v_write(self, v: T);
}

#[verus_verify]
impl<T> SafeMutPtrWithFracTypedPerm<T> for *mut T {
    /// Trusted API to borrow a reference to the value at the pointer.
    /// Safety: without providing the tracked memory permission, this is unsafe.
    /// This is safe with verification because we have passed the tracked memory permission.
    #[inline(always)]
    #[verus_spec(
        with Tracked(perm): Tracked<&mut FracTypedPerm<T>>
        ensures
            perm@ == old(perm)@.update_value(MemContents::Init(v)),
    )]
    unsafe fn v_write(self, v: T) {
        proof_decl!{
            let tracked mut ptr_perm = perm.extract();
            ptr_perm.leak_contents();
        }
        vstd::raw_ptr::ptr_mut_write(self, verus_exec_expr!(Tracked(&mut ptr_perm)), v);
        proof!{
            perm.update(ptr_perm);
        }
    }
}
