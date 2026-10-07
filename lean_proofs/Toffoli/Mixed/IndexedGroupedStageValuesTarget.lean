import Toffoli.Mixed.IndexedGroupedLadderModel
import Toffoli.Foundations.IndexedTargetControl

namespace Toffoli

/-- Updating the parent target preserves every grouped factor and dirty input
that excludes that target. -/
theorem indexed_grouped_stage_values_target {K : Type*} [CommMonoid K] [Add K] {n : ℕ}
    (stages : List (Finset (Fin n) × Fin n)) (target : IndexedTarget n)
    (htarget : ∀ stage ∈ stages,
      (∀ i ∈ stage.1, target ≠ some i) ∧ target ≠ some stage.2)
    (amount : K) (x : Controls K n) (t : K) :
    indexedGroupedStageValues stages (indexedTargetAdd target amount (x, t)).1 =
      indexedGroupedStageValues stages x := by
  unfold indexedGroupedStageValues
  apply List.map_congr_left
  intro stage hstage
  obtain ⟨hfactors, hdirty⟩ := htarget stage hstage
  apply Prod.ext
  · exact Finset.prod_congr rfl (fun i hi =>
      indexed_target_add_control target amount x t i (hfactors i hi))
  · exact indexed_target_add_control target amount x t stage.2 hdirty

end Toffoli
