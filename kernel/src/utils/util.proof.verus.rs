verus! {

// put expensive proofs into another module.
mod util_align_up {
    use super::*;
    use vstd::arithmetic::div_mod::{
        lemma_add_mod_noop,
        lemma_mod_self_0,
        lemma_mod_twice,
        lemma_small_mod,
        lemma_sub_mod_noop,
    };
    use verify_proof::bits::is_pow_of_2;

    #[verifier::rlimit(4)]
    pub proof fn lemma_align_up(x: u64, align: u64) -> (ret: u64)
        requires
            is_pow_of_2(align as u64),
            x + align - 1 <= u64::MAX,
        ensures
            ret == add(x, sub(align, 1)) & !sub(align, 1),
            ret == spec_align_up(x as int, align as int),
    {
        broadcast use align_proof;

        let mask = (align - 1) as u64;
        let y = (x + mask) as u64;
        verify_proof::bits::lemma_bit_u64_and_mask(y, !mask);
        verify_proof::bits::lemma_bit_u64_and_mask_is_mod(y, mask);
        let ret = add(x, sub(align, 1)) & !sub(align, 1);

        assert(y & !mask == sub(y, y & mask));
        let align = align as int;
        let x = x as int;
        let r = ((x + align) - 1) % align;
        if x % align == 0 {
            lemma_mod_self_0(align);
            lemma_add_mod_noop(x, align - 1, align);
            lemma_small_mod((align - 1) as nat, align as nat);
            lemma_mod_twice(x, align);
            assert(r == align - 1);
        } else {
            lemma_mod_self_0(align);
            lemma_sub_mod_noop(x + align, 1, align);
            lemma_sub_mod_noop(x % align, 1, align);
            lemma_add_mod_noop(x, align, align);
            lemma_mod_twice(x, align);
            lemma_small_mod(1, align as nat);
            assert(r == (x % align - 1) % align);
            lemma_small_mod((x % align - 1) as nat, align as nat);
            assert(r == (x % align - 1) as int);
        }
        ret
    }

    pub proof fn lemma_align_up_u32(x: u32, align: u32) -> (ret: u32)
        requires
            is_pow_of_2(align as u64),
            x + align - 1 <= u32::MAX,
        ensures
            ret == add(x, sub(align, 1)) & !sub(align, 1),
            ret == spec_align_up(x as int, align as int),
    {
        assert(align > 0) by {
            broadcast use verify_proof::bits::lemma_bit_u64_shl_values;

        }
        let mask = sub(align, 1);
        let r = add(x, sub(align, 1));
        let ret = add(x, sub(align, 1)) & !sub(align, 1);
        verify_proof::bits::lemma_bit_u32_and_mask(r, mask);
        verify_proof::bits::lemma_bit_u32_and_mask(r, !mask);
        verify_proof::bits::lemma_bit_u64_and_mask(r as u64, mask as u64);
        verify_proof::bits::lemma_bit_u64_and_mask(r as u64, !sub(align as u64, 1));
        lemma_align_up(x as u64, align as u64);
        ret
    }

}

mod util_align_down {
    use super::*;

    pub proof fn lemma_align_down(x: u64, align: u64)
        requires
            align_requires(align),
        ensures
            (x & !((align - 1) as u64)) == spec_align_down(x as int, align as int),
    {
        broadcast use align_proof;

        let mask: u64 = sub(align, 1);
        assert(x == (x & !mask) + (x & mask));
    }

    pub proof fn lemma_align_down_u32(x: u32, align: u32)
        requires
            align_requires(align as u64),
        ensures
            (x & !((align - 1) as u32)) == spec_align_down(x as int, align as int),
    {
        assert(align > 0) by {
            broadcast use verify_proof::bits::lemma_bit_u64_shl_values;

        }
        let mask = sub(align, 1);
        verify_proof::bits::lemma_bit_u32_and_mask(x, mask);
        verify_proof::bits::lemma_bit_u32_and_mask(x, !mask);
        verify_proof::bits::lemma_bit_u64_and_mask(x as u64, mask as u64);
        verify_proof::bits::lemma_bit_u64_and_mask(x as u64, !sub(align as u64, 1));
        lemma_align_down(x as u64, align as u64);
    }

}

} // verus!
verus! {

mod util_integer_align {
    use super::*;

    impl IntegerAligned for u64 {
        proof fn lemma_is_aligned(val: u64, align: u64, ret: bool) {
            broadcast use align_proof, external_axiom;

            assert(ret == (val & sub(align, 1) == 0));
        }

        proof fn lemma_align_down(val: Self, align: Self, ret: Self) {
            broadcast use external_axiom;

            util_align_down::lemma_align_down(val, align);
            axiom_from_spec::<_, int>(val);  // ? a trigger missing from verus.
        }

        proof fn lemma_align_up(val: Self, align: Self, ret: Self) {
            broadcast use external_axiom;

            util_align_up::lemma_align_up(val, align);
        }
    }

    impl IntegerAligned for usize {
        proof fn lemma_is_aligned(val: usize, align: usize, ret: bool) {
            u64::lemma_is_aligned(val as u64, align as u64, ret)
        }

        proof fn lemma_align_down(val: Self, align: Self, ret: Self) {
            u64::lemma_align_down(val as u64, align as u64, ret as u64)
        }

        proof fn lemma_align_up(val: Self, align: Self, ret: Self) {
            u64::lemma_align_up(val as u64, align as u64, ret as u64)
        }
    }

    impl IntegerAligned for u32 {
        proof fn lemma_is_aligned(val: u32, align: u32, ret: bool) {
            broadcast use align_proof;

            assert(ret == (val & (align - 1) as u32 == 0));
        }

        proof fn lemma_align_down(val: Self, align: Self, ret: Self) {
            broadcast use external_axiom;

            util_align_down::lemma_align_down_u32(val, align);
        }

        proof fn lemma_align_up(val: Self, align: Self, ret: Self) {
            broadcast use external_axiom;

            util_align_up::lemma_align_up_u32(val, align);
        }
    }

}

} // verus!
