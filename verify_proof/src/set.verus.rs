use vstd::prelude::*;
use vstd::set_lib::set_int_range;

verus! {

pub open spec fn seq_sets_to_set<A>(next: Seq<Set<A>>) -> Set<A>
    decreases next.len(),
{
    let i = next.len() - 1;
    if next.len() > 0 {
        seq_sets_to_set(next.take(i)) + next[i]
    } else {
        Set::empty()
    }
}

pub open spec fn seq_sets_are_disjoint<A>(seq: Seq<Set<A>>) -> bool {
    forall|i, j| 0 <= i < j < seq.len() ==> seq[i].disjoint(seq[j])
}

pub proof fn lemma_sets_to_set_fixed_len<A>(seq: Seq<Set<A>>, n: nat)
    requires
        forall|i| 0 <= i < seq.len() ==> (#[trigger] seq[i]).len() == n && seq[i].finite(),
        seq_sets_are_disjoint(seq),
    ensures
        seq_sets_to_set(seq).len() == seq.len() * n,
    decreases seq.len(),
{
    let len = seq.len();
    if len > 0 {
        lemma_sets_to_set_fixed_len(seq.take(len - 1), n);
        let prev = seq_sets_to_set(seq.take(len - 1));
        lemma_sets_to_set_take_one(seq, len - 1);
        lemma_sets_to_set_finite_iff(seq.take(len - 1));
        vstd::set_lib::lemma_set_disjoint_lens(prev, seq.last());
        assert(len * n == (len - 1) * n + n) by (nonlinear_arith);
    } else {
        assert(0 * n == 0);
    }
}

pub proof fn lemma_sets_to_set_take_one<A>(seq: Seq<Set<A>>, idx: int)
    requires
        0 <= idx < seq.len(),
        forall|i, j| 0 <= i < j < seq.len() ==> seq[i].disjoint(seq[j]),
    ensures
        seq_sets_to_set(seq.take(idx)).disjoint(seq[idx]),
{
    let sub = seq.take(idx);
    assert forall|a| #[trigger] seq_sets_to_set(sub).contains(a) implies !seq[idx].contains(a) by {
        lemma_sets_to_set_contains(sub, a);
        let i = choose|i: int| 0 <= i < sub.len() && #[trigger] sub[i].contains(a);
        assert(sub[i].contains(a));
        assert(0 <= i < idx);
        assert(seq[i].disjoint(seq[idx]) || seq[idx].disjoint(seq[i]));
    }
}

pub proof fn lemma_sets_to_set_finite_iff<A>(seq: Seq<Set<A>>)
    ensures
        (forall|i| 0 <= i < seq.len() ==> #[trigger] seq[i].finite()) <==> seq_sets_to_set(
            seq,
        ).finite(),
    decreases seq.len(),
{
    let all_finites = forall|i| 0 <= i < seq.len() ==> #[trigger] seq[i].finite();
    let len = seq.len();
    if len > 0 {
        lemma_sets_to_set_finite_iff(seq.take(len - 1));
        let sub = seq.take(len - 1);
        let sub_finites = forall|i| 0 <= i < sub.len() ==> #[trigger] sub[i].finite();
        if (sub_finites && seq[len - 1].finite()) {
            assert forall|i| 0 <= i < seq.len() implies #[trigger] seq[i].finite() by {
                assert(seq[len - 1].finite());
                if i < len - 1 {
                    assert(sub[i].finite());
                }
            }
        }
        assert(all_finites ==> sub_finites && seq[len - 1].finite());
        vstd::set_lib::lemma_set_union_finite_iff(seq_sets_to_set(sub), seq[len - 1]);
        assert((forall|i| 0 <= i < seq.len() ==> #[trigger] seq[i].finite()) <==> seq_sets_to_set(
            seq,
        ).finite());
    } else {
        assert(all_finites);
        assert(seq_sets_to_set(seq).is_empty());
        assert((forall|i| 0 <= i < seq.len() ==> #[trigger] seq[i].finite()) <==> seq_sets_to_set(
            seq,
        ).finite());
    }
}

pub proof fn lemma_sets_to_set_contains<A>(seq: Seq<Set<A>>, a: A)
    requires
        seq_sets_to_set(seq).contains(a),
    ensures
        exists|i: int| (0 <= i < seq.len() && #[trigger] seq[i].contains(a)),
    decreases seq.len(),
{
    let len = seq.len();
    if len > 0 {
        if seq_sets_to_set(seq.take(len - 1)).contains(a) {
            lemma_sets_to_set_contains(seq.take(len - 1), a);
        } else {
            assert(seq[len - 1].contains(a));
        }
    }
}

#[verifier(inline)]
pub open spec fn spec_int_range_disjoint(start1: int, end1: int, start2: int, end2: int) -> bool {
    (end1 <= start2 || end2 <= start1)
}

pub broadcast proof fn lemma_int_range_disjoint(start1: int, end1: int, start2: int, end2: int)
    ensures
        (#[trigger] set_int_range(start1, end1)).disjoint(#[trigger] set_int_range(start2, end2))
            <==> spec_int_range_disjoint(start1, end1, start2, end2),
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

} // verus!
