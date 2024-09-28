use vstd::prelude::*;

verus! {
    pub const MAX_U64: u64 = 0xffff_ffff_ffff_ffff;
    pub const MAX_USIZE: usize = 0xffff_ffff_ffff_ffff;
}

macro_rules! bit_shl_properties {
    ($typ:ty, $size:expr) => {
        paste::paste! {verus!{
            proof fn [<proof_$typ _bit_shl_monotonic_inc>](offset1: $typ, offset2: $typ)
            requires
                0 <= offset1 < $size,
                0 <= offset2 < $size,
                offset1 < offset2,
            ensures
                ((1 as $typ) << offset1) < ((1 as $typ) << offset2)
            {
                assert(((1 as $typ) << offset1) < ((1 as $typ) << offset2)) by (bit_vector)
                requires  0 <= offset1 < $size,
                0 <= offset2 < $size,
                offset1 < offset2,
            }

            pub proof fn [<proof_ $typ _shl_bound>](offset: $typ) -> (ret: $typ)
            requires 0 <= offset < $size
            ensures
                ret == (1 as $typ) << offset,
                1 <= ret < 0x1000_0000_0000_0000_0000,
            {
                assert(((1 as $typ) << offset) >= 1) by(bit_vector)
                requires  0 <= offset < $size;
                (1 as $typ) << offset
            }
        }}
    };
}

bit_shl_properties! {usize, 64}

verus! {
    #[verifier(bit_vector)]
    pub proof fn proof_usize_bitor_bound(a: usize, b: usize)
    ensures
        (a | b) == (b | a),
        0 <= (a | b) <= MAX_USIZE,
        (a | b) & b == b,
        (a | b) > a,
        (a | b) > b,
        (a | b) & !b == a & !b,
        (a | b) <= a + b
    {}

    pub proof fn proof_usize_bitor_bound_auto()
    ensures
        forall |a: usize, b: usize|
            #[trigger] (a | b) == (b | a) &&
            0 <= (a | b) <= MAX_USIZE &&
            (a | b) & b == b &&
            (a | b) >= a &&
            (a | b) >= b &&
            (a | b) & !b == a & !b &&
            (a | b) <= a + b
    {
        assert forall |a: usize, b: usize|
        (#[trigger] (a | b) == (b | a) &&
        0 <= (a | b) <= MAX_USIZE &&
        (a | b) & b == b &&
        (a | b) >= a &&
        (a | b) >= b &&
        (a | b) & !b == a & !b &&
        (a | b) <= a + b) by {
            proof_usize_bitor_bound(a, b);
        }
    }

    #[verifier(bit_vector)]
    pub proof fn proof_usize_bitnot_auto()
        ensures
            forall |a: usize| #[trigger] !(!a) == a,
            forall |a: usize| #[trigger] (!a) & a == 0,
            !0u64 == 0xffffffffffffffffu64,
            forall |a: usize| #[trigger] (!a) == sub(MAX_USIZE, a),
    {}
}
