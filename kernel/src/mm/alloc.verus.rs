verus! {

use vstd::prelude::*;
use vstd::set_lib::set_int_range;
use vstd::raw_ptr::{MemContents, PointsTo, PointsToRaw};
use verify_proof::tracked_exec_arbirary;

pub type RawMemPerm = PointsToRaw;

pub type TypedMemPerm<T> = PointsTo<T>;

tracked struct MemoryRegionPerms<const N: usize> {
    tracked avail: Map<int, Map<int, RawMemPerm>>,  //bucket -> perm list
    tracked reserved: Map<int, TypedMemPerm<PageInfo>>,  //pfn -> pginfo
    ghost next: Seq<Seq<int>>,  // bucket -> page_list
    ghost page_count: nat,
    ghost start_phys: int,
    ghost start_virt: int,
}

pub trait AllocatorManagedMemory {
    spec fn is_range_for_alloc(&self, start: int, end: int) -> bool;
}

proof fn tracked_empty_maps<K, T>(n: int) -> (tracked ret: Map<int, Map<K, T>>)
    ensures
        ret.dom() =~= set_int_range(0, n),
        forall|i| 0 <= i < n ==> ret[i] =~~= Map::<K, T>::empty(),
    decreases n,
{
    if n <= 0 {
        Map::tracked_empty()
    } else {
        let tracked mut prev = tracked_empty_maps(n - 1);
        prev.tracked_insert(n - 1, Map::tracked_empty());
        prev
    }
}

#[verifier(inline)]
spec fn spec_empty_seqs(max_order: int) -> Seq<Seq<int>> {
    Seq::new(max_order as nat, |k| Seq::empty())
}

impl AllocatorManagedMemory for RawMemPerm {
    // TODO: defines the memory property and content
    // e.g., allocator-managed memory is private
    open spec fn is_range_for_alloc(&self, start: int, end: int) -> bool {
        self.is_range(start, end)
    }
}

spec fn spec_page_count(next: Seq<Seq<int>>, max_order: int) -> int
    decreases max_order,
{
    if max_order <= 0 {
        0
    } else {
        let prev_next = next.remove(max_order - 1);
        spec_page_count(prev_next, max_order - 1) + next[max_order - 1].len()
    }
}

impl<const N: usize> MemoryRegionPerms<N> {
    pub closed spec fn page_count(&self) -> nat {
        self.page_count
    }

    pub closed spec fn start_virt(&self) -> int {
        self.start_virt
    }

    pub closed spec fn start_phys(&self) -> int {
        self.start_phys
    }

    spec fn get_pfn(&self, vaddr: int) -> int {
        (vaddr - self.start_virt) / PAGE_SIZE as int
    }

    spec fn get_virt(&self, pfn: int) -> int {
        self.start_virt + (pfn * PAGE_SIZE)
    }

    pub closed spec fn next_page(&self, i: int) -> int {
        if self.next[i].len() == 0 {
            0
        } else {
            self.next[i].last()
        }
    }

    spec fn wf_dom(&self) -> bool {
        let avail = self.avail;
        let next = self.next;
        let reserved = self.reserved;
        let page_count = self.page_count;
        &&& next.len() == N
        &&& avail.dom() =~= set_int_range(0, N as int)
        &&& reserved.dom() =~= set_int_range(0, page_count as int)
    }

    spec fn spec_page_info(&self, vaddr: int) -> MemContents<PageInfo> {
        let pfn = self.get_pfn(vaddr);
        let reserved = self.reserved;
        reserved[pfn].opt_value()
    }

    spec fn is_free_with_order(&self, vaddr: int) -> int {
        if self.spec_page_info(vaddr).is_init() {
            let pi = self.spec_page_info(vaddr).value();
            match pi {
                PageInfo::Free(FreeInfo { next_page, order }) => { order as int },
                _ => { -1 },
            }
        } else {
            -1
        }
    }

    spec fn wf_bucket(&self, bucket: int) -> bool {
        let avail = self.avail[bucket];
        let next = self.next[bucket];
        &&& avail.dom() =~= set_int_range(
            0,
            next.len() as int,
        )
        // PFN  > 0
        &&& forall|i| 0 <= i < next.len() ==> next[i] > 0
        &&& forall|i|
            0 <= i < next.len() ==> avail[i].is_range_for_alloc(
                self.get_virt(next[i]),
                (1usize << bucket as usize) as int,
            )
    }

    spec fn wf_info(&self) -> bool {
        let reserved = self.reserved;
        let avail = self.avail;
        let next = self.next;
        &&& self.page_count >= spec_page_count(next, N as int)
        &&& forall|i| 0 <= i < N ==> self.wf_bucket(i)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_dom()
        &&& self.wf_info()
    }

    proof fn lemma_new_is_empty(max_order: int)
        requires
            max_order >= 0,
        ensures
            spec_page_count(spec_empty_seqs(max_order), max_order) == 0,
        decreases max_order,
    {
        let next = spec_empty_seqs(max_order);
        if max_order > 0 {
            let prev_next = spec_empty_seqs(max_order - 1);
            Self::lemma_new_is_empty(max_order - 1);
            assert(prev_next =~= next.remove(max_order - 1));
            assert(next[max_order - 1].len() == 0);
        } else {
            assert(spec_page_count(next, max_order) == 0);
        }
    }

    pub proof fn tracked_new() -> (tracked ret: MemoryRegionPerms<N>)
        ensures
            ret.wf(),
            ret.start_virt() == 0,
            ret.start_phys() == 0,
            ret.page_count() == 0,
            forall|i| 0 <= i < N ==> ret.next_page(i) == 0,
        decreases N,
    {
        Self::lemma_new_is_empty(N as int);
        let tracked ret = MemoryRegionPerms {
            avail: tracked_empty_maps(N as int),
            reserved: Map::tracked_empty(),
            next: spec_empty_seqs(N as int),
            page_count: 0,
            start_phys: 0,
            start_virt: 0,
        };
        assert forall|i| 0 <= i < ret.page_count implies ret.reserved.dom().contains(i) by {};
        ret
    }

    spec fn ensures_has_free_pages(&self, new: Self, ret: bool, order: int) -> bool {
        // No available if no slot >= order
        &&& !ret ==> forall|i| order <= i < N ==> self.next[i].len() == 0
        &&& !ret ==> *self === new
        &&& if self.next[order].len() > 0 {
            *self === new && ret
        } else {
            ret == (new.next[order].len() > 0)
        }
    }
}

impl MemoryRegion {
    spec fn view(&self) -> MemoryRegionPerms<MAX_ORDER> {
        self.perms@
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        let perms = self@;
        &&& perms.wf()
        &&& perms.start_phys() == self.start_phys@
        &&& perms.start_virt() == self.start_virt@
        &&& perms.page_count() == self.page_count
        &&& forall|i| 0 <= i < perms.next.len() ==> self.next_page[i] == perms.next_page(i)
    }
}

} // verus!
