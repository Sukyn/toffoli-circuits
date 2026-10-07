import Toffoli.Additions.CycleListingNontrivial

namespace Toffoli
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every finite permutation has disjoint, nonempty cycle lists covering the
whole type. Singleton fixed points are included, as in the paper. -/
theorem exists_cycle_listing (σ : Equiv.Perm α) :
    ∃ cycles : List (List α), cycles.flatten.Nodup ∧
      (∀ x, x ∈ cycles.flatten) ∧ cycleFamilyPermutation cycles = σ ∧
      (∀ labels ∈ cycles, labels ≠ []) ∧
      (∀ labels ∈ cycles, σ.IsCycleOn {x | x ∈ labels}) := by
  classical
  obtain ⟨cycles, hn, hm, hp, he, hc⟩ := exists_nontrivial_cycle_listing σ
  let fixed := (Finset.univ \ σ.support).toList
  have hfixed (x : α) : x ∈ fixed ↔ σ x = x := by
    simp [fixed, Equiv.Perm.mem_support]
  have hflat : (fixed.map (fun x => [x])).flatten = fixed := List.flatMap_singleton' fixed
  refine ⟨cycles ++ fixed.map (fun x => [x]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.flatten_append, hflat, List.nodup_append']
    refine ⟨hn, Finset.nodup_toList _, List.disjoint_left.mpr ?_⟩
    intro x hx hy
    exact Equiv.Perm.mem_support.mp ((hm x).mp hx) ((hfixed x).mp hy)
  · intro x
    rw [List.flatten_append, hflat, List.mem_append]
    by_cases hx : x ∈ σ.support
    · exact Or.inl ((hm x).mpr hx)
    · exact Or.inr ((hfixed x).mpr (Equiv.Perm.notMem_support.mp hx))
  · simpa [cycleFamilyPermutation, List.map_append, List.reverse_append,
      List.prod_append, List.map_map, Function.comp_def] using hp
  · intro labels hl
    rcases List.mem_append.mp hl with hl | hl
    · exact he labels hl
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hl
      simp
  · intro labels hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hc labels hl
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      simpa using Equiv.Perm.isCycleOn_singleton.mpr ((hfixed x).mp hx)

end Toffoli
