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

    #[verifier::rlimit(10)]
    pub broadcast proof fn lemma_align_up(x: u64, align: u64)
        requires
            align_requires(align),
            x + align - 1 <= u64::MAX,
        ensures
            #[trigger] add(x, sub(align, 1)) & !sub(align, 1) == spec_align_up(
                x as int,
                align as int,
            ),
    {
        broadcast use align_proof;

        let mask = (align - 1) as u64;
        let y = (x + mask) as u64;
        verify_proof::bits::lemma_bit_u64_and_mask(y, !mask);
        verify_proof::bits::lemma_bit_u64_and_mask_is_mod(y, mask);

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
    }

}

mod util_align_down {
    use super::*;

    pub broadcast proof fn lemma_align_down(x: u64, align: u64)
        requires
            align_requires(align),
        ensures
            #[trigger] (x & !((align - 1) as u64)) == spec_align_down(x as int, align as int),
    {
        broadcast use align_proof;

        let mask: u64 = sub(align, 1);
        assert(x == (x & !mask) + (x & mask));
    }

}

} // verus!
verus! {

mod util_integer_align {
    use super::*;

    impl IntegerAligned for u64 {
        proof fn lemma_is_aligned(val: u64, align: u64, ret: bool) {
            broadcast use align_proof, verify_external::external_axiom;

            assert(ret == (val & sub(align, 1) == 0));
            verify_proof::bits::lemma_bit_u64_and_mask_is_mod(val, (align - 1) as u64);
        }

        proof fn lemma_align_down(val: Self, align: Self, ret: Self) {
            broadcast use align_proof, verify_external::external_axiom;
            //let (mask, notmask) = impl_align_down_choose((val, align), ret);
            //assert(_impl_align_down_ensures(val, align, ret, mask, notmask));

            let mask = (align - 1) as u64;
            assert(ret == (val & !((align - 1) as u64)));
            util_align_down::lemma_align_down(val, align);
            assert(ret == spec_align_down(val as int, align as int));
            axiom_from_spec::<_, int>(val);
            axiom_from_spec::<_, int>(align);
        }

        proof fn lemma_align_up(val: Self, align: Self, ret: Self) {
            broadcast use verify_external::external_axiom;

            let mask = (align - 1) as u64;
            let r = (val + mask) as u64;
            assert(ret == (r & !mask));
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
            //let (mask, b) = impl_is_aligned_choose(val, align, ret);
            //assert(_impl_is_aligned_ensures(val, align, ret, mask, b));

            assert(ret == (val & (align - 1) as u32 == 0));
        }

        proof fn lemma_align_down(val: Self, align: Self, ret: Self) {
            broadcast use verify_external::external_axiom;
            //let (mask, notmask) = impl_align_down_choose((val, align), ret);

            let mask = (align - 1) as u32;
            //assert(_impl_align_down_ensures(val, align, ret, mask, notmask));
            assert(ret == (val & !((align - 1) as u32)));
            verify_proof::bits::lemma_bit_u32_and_mask(val, mask);
            verify_proof::bits::lemma_bit_u32_and_mask(val, !mask);
            verify_proof::bits::lemma_bit_u64_and_mask(val as u64, mask as u64);
            verify_proof::bits::lemma_bit_u64_and_mask(val as u64, !(mask as u64));
            util_align_down::lemma_align_down(val as u64, align as u64);
        }

        proof fn lemma_align_up(val: Self, align: Self, ret: Self) {
            broadcast use verify_external::external_axiom;
            //let (mask, notmask, r) = impl_align_up_choose((val, align), ret);
            //assert(_impl_align_up_ensures(val, align, ret, mask, notmask, r));

            let mask = (align - 1) as u32;
            let r = (val + mask) as u32;
            assert(ret == (r & !mask));
            verify_proof::bits::lemma_bit_u32_and_mask(r, mask);
            verify_proof::bits::lemma_bit_u32_and_mask(r, !mask);
            verify_proof::bits::lemma_bit_u64_and_mask(r as u64, mask as u64);
            verify_proof::bits::lemma_bit_u64_and_mask(r as u64, !(mask as u64));
            util_align_up::lemma_align_up(val as u64, align as u64);
        }
    }

}

} // verus!
