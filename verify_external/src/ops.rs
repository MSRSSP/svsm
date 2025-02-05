use vstd::prelude::*;

//include!{"ops.verus.rs"}
verus! {
pub broadcast group ops_def_group {
    axiom_add_requires,
    axiom_add,
    axiom_sub_requires,
    axiom_sub,
    axiom_bitand_requires,
    axiom_bitand,
    axiom_partial_eq,
    axiom_not,
}
}
macro_rules! def_uop_spec {
    ($trait:path, $extrait: ident, $fun:ident, $spec_trait:ident, $spec_ensures:ident, $axiom_fn:ident) => {
        builtin_macros::verus! {
            pub open spec fn $spec_ensures<T, Output>(v: T, ret: Output) -> bool;

            #[verifier::external_trait_specification]
            pub trait $extrait {
                type ExternalTraitSpecificationFor: $trait;

                type Output;
                fn $fun(self) -> (ret: Self::Output)
                where Self: Sized
                ensures $spec_ensures::<_, Self::Output>(self, ret),
                ;
            }

            pub trait $spec_trait: Sized {
                type Output;
                open spec fn $spec_ensures(v: Self, ret: Self::Output) -> bool {true}
            }

            pub broadcast proof fn $axiom_fn<T>(v: T, ret: T::Output)
            where
                T: crate::ops::$spec_trait
            ensures
                T::$spec_ensures(v, ret) == #[trigger]$spec_ensures(v, ret),
            {
                admit()
            }
        }
    };
}

def_uop_spec!(
    core::ops::Not,
    ExNot,
    not,
    SpecNotOp,
    spec_not_ensures,
    axiom_not
);

macro_rules! def_bin_ops_spec {
    ($trait:path, $extrait: ident, $fun:ident, $spec_trait:ident, $spec_requires:ident, $spec_ensures:ident, $axiom_requires:ident, $axiom_fn:ident) => {
        builtin_macros::verus!{
            pub open spec fn $spec_ensures<T, Rhs, Output>(v: T, rhs: Rhs, ret: Output)-> bool;

            pub open spec fn $spec_requires<T, Rhs>(v: T, rhs: Rhs) -> bool;

            pub trait $spec_trait<Rhs>: Sized {
                type Output;
                open spec fn $spec_ensures(v: Self, rhs: Rhs, ret: Self::Output) -> bool {true}
                open spec fn $spec_requires(v: Self, rhs: Rhs) -> bool {true}
            }

            #[verifier::external_trait_specification]
            pub trait $extrait<Rhs> {
                type ExternalTraitSpecificationFor: $trait<Rhs>;

                type Output;
                fn $fun(self, rhs: Rhs) -> (ret: Self::Output)
                where Self: Sized
                requires $spec_requires(self, rhs),
                ensures $spec_ensures(self, rhs, ret)
                ;
            }

            pub broadcast proof fn $axiom_fn<T, Rhs>(v: T, rhs: Rhs, ret: T::Output)
            where
                T: $spec_trait<Rhs>
            ensures
                (#[trigger]$spec_ensures(v, rhs, ret)) == T::$spec_ensures(v, rhs, ret)
            {
                admit()
            }

            pub broadcast proof fn $axiom_requires<T, Rhs>(v: T, rhs: Rhs)
            where
                T: crate::ops::$spec_trait<Rhs>
            ensures
                (#[trigger]$spec_requires(v, rhs)) == T::$spec_requires(v, rhs),
            {
                admit()
            }
        }
    };
}

def_bin_ops_spec!(
    core::ops::Add,
    ExAdd,
    add,
    SpecAddOp,
    spec_add_requires,
    spec_add_ensures,
    axiom_add_requires,
    axiom_add
);
def_bin_ops_spec!(
    core::ops::Sub,
    ExSub,
    sub,
    SpecSubOp,
    spec_sub_requires,
    spec_sub_ensures,
    axiom_sub_requires,
    axiom_sub
);

def_bin_ops_spec!(
    core::ops::Rem,
    ExRem,
    rem,
    SpecRemOp,
    spec_rem_requires,
    spec_rem_ensures,
    axiom_rem_requires,
    axiom_rem
);
def_bin_ops_spec!(
    core::ops::Mul,
    ExMul,
    mul,
    SpecMulOp,
    spec_mul_requires,
    spec_mul_ensures,
    axiom_mul_requires,
    axiom_mul
);
def_bin_ops_spec!(
    core::ops::Div,
    ExDiv,
    div,
    SpecDivOp,
    spec_div_requires,
    spec_div_ensures,
    axiom_div_requires,
    axiom_div
);
def_bin_ops_spec!(
    core::ops::BitAnd,
    ExBitAdd,
    bitand,
    SpecBitAndOp,
    spec_bitand_requires,
    spec_bitand_ensures,
    axiom_bitand_requires,
    axiom_bitand
);

def_bin_ops_spec!(
    core::ops::Shl,
    ExShl,
    shl,
    SpecShlOp,
    spec_shl_requires,
    spec_shl_ensures,
    axiom_shl_requires,
    axiom_shl
);

def_bin_ops_spec!(
    core::ops::Shr,
    ExShr,
    shr,
    SpecShrOp,
    spec_shr_requires,
    spec_shr_ensures,
    axiom_shr_requires,
    axiom_shr
);

macro_rules! def_bop_spec {
    ($typ:ty, $rtyp:ty, $otyp: ty, $op:tt, $spec_ensures:ident, $spec_requires:ident, $spec_tr:ident) => {
        verus! {
            impl $spec_tr<$rtyp> for $typ {
                type Output = $otyp;

                #[verifier(inline)]
                open spec fn $spec_requires(v: Self, rhs: $rtyp) -> bool {
                    (v $op rhs) as $otyp == (v $op rhs)
                }

                #[verifier(inline)]
                open spec fn $spec_ensures(v: Self, rhs: $rtyp, ret: $otyp) -> bool {
                    ret == (v $op rhs)
                }
            }
        }
    };
}

macro_rules! def_bop_specs {
    ($spec_tr:ident, $spec_ensures:ident, $spec_requires:ident,$op:tt, [$($typ:ty)*])  => {
        $(
            def_bop_spec!($typ, $typ, $typ, $op, $spec_ensures, $spec_requires, $spec_tr);
        )*
    }
}

macro_rules! def_uop_axiom {
    ($spec_tr: ident, $spec_ensures:ident, $typ:ty, $otyp: ty, $op:tt) => {
        verus! {
            impl $spec_tr for $typ {
                type Output = $otyp;

                #[verifier(inline)]
                open spec fn $spec_ensures(v: $typ, ret: $otyp) -> bool {
                    ret == ($op v)
                }
            }
        }
    };
}

macro_rules! def_uop_axioms {
    ($tr: ident, $fun:ident, $op:tt, [$($typ:ty)*])  => {
        $(
            def_uop_axiom!($tr, $fun, $typ, $typ, $op);
        )*
    }
}

def_bop_specs!(SpecAddOp, spec_add_ensures, spec_add_requires, +, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);
def_bop_specs!(SpecSubOp, spec_sub_ensures, spec_sub_requires, -, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(SpecRemOp, spec_rem_ensures, spec_rem_requires, %, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(SpecBitAndOp, spec_bitand_ensures,spec_bitand_requires, &, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_uop_axioms!(SpecNotOp, spec_not_ensures, !, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

verus! {
pub trait SpecPartialEqOp<T: ?Sized> {
    spec fn spec_partial_eq_ensures(lsh: &Self, rhs: &T, ret: bool) -> bool;
}

pub open spec fn spec_partial_eq_ensures<T1: ?Sized, T2: ?Sized>(v1: &T1, rhs: &T2, ret: bool) -> bool;

pub broadcast proof fn axiom_partial_eq<T1: ?Sized + SpecPartialEqOp<T2>, T2: ?Sized>(v: &T1, rhs: &T2, ret: bool)
ensures
    T1::spec_partial_eq_ensures(v, rhs, ret) == #[trigger]spec_partial_eq_ensures(v, rhs, ret)
{
    admit()
}

#[verifier::external_trait_specification]
pub trait ExPartialEq<Rhs> where Rhs: ?Sized {
    type ExternalTraitSpecificationFor: core::cmp::PartialEq<Rhs>;

    // Required method
    fn eq(&self, other: &Rhs) -> (ret: bool)
    ensures
        self::spec_partial_eq_ensures(self, other, ret);

    // Provided method
    fn ne(&self, other: &Rhs) -> (ret: bool)
    ensures
        self::spec_partial_eq_ensures(self, other, !ret);
}
}

macro_rules! def_partial_eq_for{
    ($($ty: ty)*) => {verus!{
        $(
            impl SpecPartialEqOp<$ty> for $ty {
                open spec fn spec_partial_eq_ensures(lhs: &$ty, rhs: &$ty, ret: bool) -> bool {
                    (*lhs == *rhs) == ret
                }
            }
        )*
    }}
}
def_partial_eq_for!(
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
);

verus! {
    pub proof fn test(v1: usize, v2: usize)
    requires v1 > v2,
    ensures
        spec_sub_requires(v1, v2),
        (from_spec::<_, u32>(1u8) == 1u32)
    {
        broadcast use crate::external_axiom;
    }
}

verus! {
    proof fn _lemma_align_up_requires(addr: usize, align: usize)
    requires
        addr + align - 1 <= usize::MAX,
        align > 0,
    ensures
        true
    {
        assert forall |mask: usize|
            #[trigger] crate::ops::spec_sub_ensures(align, 1usize, mask)
        implies
            spec_add_requires::<usize, usize>(addr, mask)
        by {
            broadcast use crate::ops::axiom_add_requires, axiom_sub;
            assert(crate::ops::spec_sub_ensures(align, 1usize, mask));
            assert(mask == align - 1);
            assert((addr + mask) as usize == addr + mask);

            assert(spec_add_requires::<usize, usize>(addr, mask));
            //crate::ops::axiom_add_requires(addr, mask);
        }
    }
}

use crate::convert::*;
verus! {
pub open spec fn align_requires(align: u64) -> bool {
    true
}


pub open spec fn impl_is_aligned_requires<T>(args: (T, T)) -> bool where
 {
    let (val, align) = args;
    let one = from_spec::<_, T>(1u8);
    &&& spec_sub_requires(align, one)
    &&& forall|mask: T| #[trigger]
        spec_sub_ensures(align, one, mask) ==> spec_bitand_requires(val, mask)
}

#[verifier(inline)]
pub open spec fn _impl_is_aligned_ensures<T>(
    val: T,
    align: T,
    ret: bool,
    mask: T,
    b: T,
) -> bool{
    &&& spec_sub_ensures(align, from_spec::<_, T>(1u8), mask)
    &&& #[trigger]spec_bitand_ensures(val, mask, b)
    &&& spec_partial_eq_ensures(&b, &from_spec::<_, T>(0u8), ret)
}

pub open spec fn impl_is_aligned_ensures<T>(args: (T, T), ret: bool) -> bool
{
    let (val, align) = args;
    exists|mask: T, b: T|
        #![trigger spec_bitand_ensures(val, mask, b)]
        { _impl_is_aligned_ensures(val, align, ret, mask, b) }
}

pub open spec fn impl_is_aligned_choose<T>(val: T, align: T, ret: bool) -> (mask_b: (T, T))
{
    choose|mask: T, b: T|
        #![trigger spec_bitand_ensures(val, mask, b)]
        _impl_is_aligned_ensures(val, align, ret, mask, b)
}

pub open spec fn spec_is_aligned<T>(addr: T, align: T) -> bool
 {
    from_spec::<_, u64>(addr) % from_spec::<_, u64>(align) == 0
}


pub trait TT: Sized + FromSpec<u8> {
    proof fn lemma_is_aligned(val: Self, align: Self, ret: bool)
        requires
            true
        ensures
            true;
}

//use crate::convert::FromSpec;
impl TT for u32 {
    proof fn lemma_is_aligned(val: u32, align: u32, ret: bool)
        ensures
            true,
    {
        broadcast use crate::convert::axiom_from_spec;
        //axiom_from_spec::<_, u32>(0u8);
        assert(from_spec::<u8, u32>(0u8) == u32::from_spec(0u8));
    }
}

proof fn lemma_is_aligned(val: u32, align: u32, ret: bool)
        ensures
            true,
    {
        broadcast use crate::external_axiom;
        assert(from_spec::<_, u32>(0u8) == 0);
    }

} // verus!
