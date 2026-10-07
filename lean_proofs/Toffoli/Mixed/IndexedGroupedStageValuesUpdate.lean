import Toffoli.Mixed.IndexedGroupedLadderModel

namespace Toffoli

/-- A preparation changes none of the later factors or dirty inputs when its
destination is excluded from those stages. -/
theorem indexed_grouped_stage_values_update {K : Type*} [CommMonoid K] {n : ℕ}
    (stages : List (Finset (Fin n) × Fin n)) (x : Controls K n)
    (dirty : Fin n) (value : K)
    (houtside : ∀ stage ∈ stages, dirty ∉ stage.1 ∧ dirty ≠ stage.2) :
    indexedGroupedStageValues stages (Function.update x dirty value) =
      indexedGroupedStageValues stages x := by
  unfold indexedGroupedStageValues
  apply List.map_congr_left
  intro stage hstage
  obtain ⟨hfactors, hdirty⟩ := houtside stage hstage
  exact Prod.ext (Finset.prod_update_of_notMem hfactors x value)
    (Function.update_of_ne hdirty.symm _ _)

end Toffoli
