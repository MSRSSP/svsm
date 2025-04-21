use vstd::prelude::*;
use vstd::set_lib::set_int_range;

verus! {

pub open spec fn set_usize_range(start: usize, end: int) -> Set<usize> {
    Set::new(|i| start <= i < end)
}

pub broadcast proof fn lemma_set_usize_range(start: usize, end: int)
    requires
        start <= end,
        end <= usize::MAX + 1,
    ensures
        (#[trigger] set_usize_range(start, end)).finite(),
        set_usize_range(start, end).len() == end - start,
    decreases end - start,
{
    if end > start {
        let e2 = (end - 1) as usize;
        let s1 = set_usize_range(start, end);
        let s2 = set_usize_range(start, e2 as int);
        lemma_set_usize_range(start, e2 as int);
        assert(s1 =~= s2.insert(e2));
    } else {
        assert(set_usize_range(start, end) =~= Set::empty());
    }
}

pub broadcast proof fn lemma_set_usize_finite(s: Set<usize>)
    ensures
        #[trigger] s.finite(),
{
    let maxset = set_usize_range(0, usize::MAX + 1);
    lemma_set_usize_range(0, usize::MAX + 1);
    assert(s.subset_of(maxset));
}

#[verifier(inline)]
pub open spec fn spec_int_range_disjoint(start1: int, end1: int, start2: int, end2: int) -> bool {
    (end1 <= start2 || end2 <= start1)
}

pub broadcast proof fn lemma_int_range_disjoint(start1: int, end1: int, start2: int, end2: int)
    ensures
        (#[trigger] set_int_range(start1, end1)).disjoint(#[trigger] set_int_range(start2, end2))
            <==> (spec_int_range_disjoint(start1, end1, start2, end2) || !(start1 < end1 && start2
            < end2)),
{
    let s1 = set_int_range(start1, end1);
    let s2 = set_int_range(start2, end2);

    if end1 <= start2 || end2 <= start1 {
        assert forall|a| s1.contains(a) implies !s2.contains(a) by {}
    } else if start1 < end1 && start2 < end2 {
        assert(s1.contains(start1));
        assert(s2.contains(start2));
        assert(s1.contains(start2) || s2.contains(start1));
    }
}

pub broadcast proof fn lemma_int_range(lo: int, hi: int)
    requires
        lo <= hi,
    ensures
        (#[trigger] set_int_range(lo, hi)).finite(),
        set_int_range(lo, hi).len() == hi - lo,
{
    vstd::set_lib::lemma_int_range(lo, hi);
}

pub broadcast proof fn lemma_len_filter<A>(s: Set<A>, f: spec_fn(A) -> bool)
    requires
        s.finite(),
    ensures
        (#[trigger] s.filter(f)).finite(),
        s.filter(f).len() <= s.len(),
{
    s.lemma_len_filter(f)
}

pub broadcast proof fn lemma_len_subset<A>(s1: Set<A>, s2: Set<A>)
    requires
        s2.finite(),
        #[trigger] s1.subset_of(s2),
    ensures
        s1.len() <= s2.len(),
        s1.finite(),
{
    vstd::set_lib::lemma_len_subset(s1, s2)
}

pub broadcast proof fn lemma_set_filter_disjoint_len<A>(
    s: Set<A>,
    f: spec_fn(A) -> bool,
    s2: Set<A>,
)
    requires
        s.finite(),
        s2.subset_of(s),
        #[trigger] s.filter(f).disjoint(s2),
    ensures
        s.filter(f).len() + s2.len() <= s.len(),
        s.filter(f).len() + s2.len() == (s.filter(f) + s2).len(),
{
    s.lemma_len_filter(f);
    lemma_len_subset(s2, s);
    let s1 = s.filter(f);
    let new = s1 + s2;
    vstd::set_lib::lemma_set_disjoint_lens(s1, s2);
    lemma_len_subset(new, s);

}

} // verus!
