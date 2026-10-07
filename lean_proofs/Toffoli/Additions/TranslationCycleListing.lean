import Toffoli.Additions.CycleAddition

namespace Toffoli
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- If a permutation is one cycle on the whole field, its chosen disjoint
covering list has exactly one entry. Singleton fixed points are covered too. -/
theorem cycle_listing_length_one (σ : Equiv.Perm K)
    (hσ : σ.IsCycleOn Set.univ) : (permutationCycleLists σ).length = 1 := by
  obtain ⟨hn, hcover, _, hne, hc⟩ := Classical.choose_spec (exists_cycle_listing σ)
  have hcount : ∀ labels ∈ permutationCycleLists σ, labels.count (0 : K) = 1 := by
    intro labels hl
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil labels (hne labels hl)
    have hu : {x | x ∈ labels} = (Set.univ : Set K) :=
      ((hc labels hl).range_zpow hx).symm.trans (hσ.range_zpow (by trivial))
    have hz : (0 : K) ∈ labels := by
      simpa only [← hu, Set.mem_setOf_eq] using Set.mem_univ (0 : K)
    exact List.count_eq_one_of_mem ((List.nodup_flatten.mp hn).1 labels hl) hz
  have hzero : (permutationCycleLists σ).flatten.count (0 : K) = 1 :=
    List.count_eq_one_of_mem hn (hcover 0)
  have htotal := congrArg List.sum (List.map_congr_left hcount)
  simpa only [← List.count_flatten, List.map_const', List.sum_replicate_nat,
    Nat.mul_one, hzero] using htotal.symm

end Toffoli
