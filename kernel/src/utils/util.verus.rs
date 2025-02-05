pub use util_align_down::lemma_align_down;
pub use util_align_up::lemma_align_up;
use verify_external::convert::*;
use verify_external::external_axiom;
use verify_external::ops::*;

verus! {

pub open spec fn align_requires(align: u64) -> bool {
    &&& verify_proof::bits::is_pow_of_2(align)
}

pub open spec fn spec_align_up(val: int, align: int) -> int {
    let r = val % align;
    &&& if r == 0 {
        val
    } else {
        (val - r + align)
    }
}

#[verifier(inline)]
pub open spec fn align_up_spec<T>(val: T, align: T) -> T where
    T: Add<Output = T> + Sub<Output = T> + BitAnd<Output = T> + Not<Output = T> + From<u8> + Copy,
 {
    from_spec(spec_align_up(from_spec(val), from_spec(align)))
}

pub open spec fn spec_align_down(val: int, align: int) -> int {
    val - val % align
}

#[verifier(inline)]
pub open spec fn align_down_spec<T>(val: T, align: T) -> T where
    T: Sub<Output = T> + Not<Output = T> + BitAnd<Output = T> + From<u8> + Copy,
 {
    from_spec(spec_align_down(from_spec(val), from_spec(align)))
}

broadcast group align_proof {
    verify_proof::bits::lemma_bit_u64_not_is_sub,
    verify_proof::bits::lemma_bit_u64_shl_values,
    verify_proof::bits::lemma_bit_u64_and_mask,
    verify_proof::bits::lemma_bit_u64_and_mask_is_mod,
    verify_proof::bits::lemma_bit_u32_not_is_sub,
    verify_proof::bits::lemma_bit_u32_shl_values,
    verify_proof::bits::lemma_bit_u32_and_mask,
    verify_proof::bits::lemma_bit_u32_and_mask_is_mod,
    verify_proof::bits::lemma_bit_usize_not_is_sub,
    verify_proof::bits::lemma_bit_usize_shl_values,
    verify_proof::bits::lemma_bit_usize_and_mask,
    verify_proof::bits::lemma_bit_usize_and_mask_is_mod,
}

pub open spec fn align_down_requires<T>(args: (T, T)) -> bool where
    T: Sub<Output = T> + BitAnd<Output = T>,
 {
    let (val, align) = args;
    let one = from_spec::<_, T>(1u8);
    &&& spec_sub_requires(align, one)
    &&& forall|v1: T, v2: T| #[trigger] spec_bitand_requires(v1, v2)
}

#[verifier(inline)]
pub open spec fn _align_down_ens<T>(val: T, align: T, ret: T, mask: T, unmask: T) -> bool {
    &&& spec_sub_ensures(align, from_spec::<_, T>(1u8), mask)
    &&& #[trigger] spec_not_ensures(mask, unmask)
    &&& spec_bitand_ensures(val, unmask, ret)
}

pub open spec fn align_down_ens<T>(args: (T, T), ret: T) -> bool {
    let (val, align) = args;
    exists|mask: T, unmask: T| _align_down_ens(val, align, ret, mask, unmask)
}

pub open spec fn align_up_requires<T>(args: (T, T)) -> bool where
    T: Sub<Output = T> + BitAnd<Output = T> + Add<Output = T>,
 {
    let (val, align) = args;
    let one = from_spec::<_, T>(1u8);
    &&& align_down_requires(args)
    &&& forall|mask: T| #[trigger]
        spec_sub_ensures(align, one, mask) ==> spec_add_requires(val, mask)
}

#[verifier(inline)]
pub open spec fn _align_up_ens<T>(val: T, align: T, ret: T, mask: T, unmask: T, tmpval: T) -> bool {
    &&& spec_sub_ensures(align, from_spec::<_, T>(1u8), mask)
    &&& #[trigger] spec_not_ensures(mask, unmask)
    &&& spec_add_ensures(val, mask, tmpval)
    &&& #[trigger] spec_bitand_ensures(tmpval, unmask, ret)
}

pub open spec fn align_up_ens<T>(args: (T, T), ret: T) -> bool {
    let (val, align) = args;
    exists|mask: T, unmask: T, tmpval: T| _align_up_ens(val, align, ret, mask, unmask, tmpval)
}

pub open spec fn impl_align_up_choose<T>(args: (T, T), ret: T) -> (T, T, T) {
    let (val, align) = args;
    choose|mask: T, unmask: T, tmpval: T| _align_up_ens(val, align, ret, mask, unmask, tmpval)
}

pub open spec fn is_aligned_requires<T>(args: (T, T)) -> bool where
    T: Sub<Output = T> + BitAnd<Output = T> + PartialEq,
 {
    let (val, align) = args;
    let one = from_spec::<_, T>(1u8);
    &&& spec_sub_requires(align, one)
    &&& forall|mask: T| #[trigger]
        spec_sub_ensures(align, one, mask) ==> spec_bitand_requires(val, mask)
    &&& forall|v1: T, v2: T| #[trigger] T::eq.requires((&v1, &v2))
}

#[verifier(inline)]
pub open spec fn _is_aligned_ens<T>(val: T, align: T, ret: bool, mask: T, b: T) -> bool where
    T: Sub<Output = T> + BitAnd<Output = T> + PartialEq + From<u8>,
 {
    &&& spec_sub_ensures(align, from_spec::<_, T>(1u8), mask)
    &&& #[trigger] spec_bitand_ensures(val, mask, b)
    &&& spec_partial_eq_ensures(&b, &from_spec::<_, T>(0u8), ret)
}

pub open spec fn is_aligned_ens<T>(args: (T, T), ret: bool) -> bool where
    T: Sub<Output = T> + BitAnd<Output = T> + PartialEq + From<u8>,
 {
    let (val, align) = args;
    exists|mask: T, b: T|
        #![trigger spec_bitand_ensures(val, mask, b)]
        { _is_aligned_ens(val, align, ret, mask, b) }
}

pub open spec fn spec_is_aligned<T>(addr: T, align: T) -> bool where
    T: Sub<Output = T> + BitAnd<Output = T> + PartialEq + From<u8>,
 {
    from_spec::<_, u64>(addr) % from_spec::<_, u64>(align) == 0
}

pub trait TT: Sized + FromSpec<u8> {
    proof fn lemma_is_aligned(val: Self, align: Self, ret: bool)
        requires
            true,
        ensures
            true,
    ;
}

pub trait IntegerAligned: Add<Output = Self> + Sub<Output = Self> + BitAnd<Output = Self> + Not<
    Output = Self,
> + From<u8> + Copy + FromSpec<u8> + FromSpec<int> + FromSpec<u64> + SpecSubOp<Self> + SpecAddOp<
    Self,
> + SpecBitAndOp<Self> + SpecNotOp + SpecPartialEqOp<Self> + core::cmp::PartialEq {
    proof fn lemma_is_aligned(val: Self, align: Self, ret: bool)
        requires
            from_spec::<Self, u64>(align) > 0,
            verify_proof::bits::is_pow_of_2(from_spec::<_, u64>(align) as u64),
            is_aligned_requires((val, align)),
            is_aligned_ens((val, align), ret),
        ensures
            ret == spec_is_aligned(val, align),
    ;

    proof fn lemma_align_down(val: Self, align: Self, ret: Self)
        requires
            from_spec::<Self, u64>(align) > 0,
            verify_proof::bits::is_pow_of_2(from_spec::<_, u64>(align) as u64),
            align_down_requires((val, align)),
            align_down_ens((val, align), ret),
        ensures
            ret == align_down_spec(val, align),
    ;

    proof fn lemma_align_up(val: Self, align: Self, ret: Self)
        requires
            from_spec::<Self, u64>(align) > 0,
            verify_proof::bits::is_pow_of_2(from_spec::<_, u64>(align) as u64),
            align_up_ens((val, align), ret),
            align_up_requires((val, align)),
        ensures
            ret == align_up_spec(val, align),
    ;
}

pub broadcast proof fn proof_align_down<T: IntegerAligned>(val: T, align: T)
    requires
        from_spec::<T, u64>(align) > 0,
        verify_proof::bits::is_pow_of_2(from_spec::<_, u64>(align) as u64),
        #[trigger] align_down_requires((val, align)),
    ensures
        forall|ret| #[trigger]
            align_down_ens((val, align), ret) ==> ret === align_down_spec(val, align),
{
    assert forall|ret: T| #[trigger] align_down_ens((val, align), ret) implies ret
        === align_down_spec(val, align) by { T::lemma_align_down(val, align, ret) }
}

pub broadcast proof fn proof_align_up<T: IntegerAligned>(val: T, align: T)
    requires
        from_spec::<T, u64>(align) > 0,
        verify_proof::bits::is_pow_of_2(from_spec::<_, u64>(align) as u64),
        align_up_requires((val, align)),
    ensures
        #![trigger align_up_requires((val, align))]
        forall|ret| #[trigger]
            align_up_ens((val, align), ret) ==> ret === align_up_spec(val, align),
{
    assert forall|ret: T| #[trigger] align_up_ens((val, align), ret) implies ret === align_up_spec(
        val,
        align,
    ) by {
        T::lemma_align_up(val, align, ret);
    }
}

} // verus!
include!("util.proof.verus.rs");
