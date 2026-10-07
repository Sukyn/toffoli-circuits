import Toffoli.Additions.CycleAmountsCongr

namespace Toffoli
variable {K : Type*} [Field K]

/-- A cycle family reads its amounts only on the listed labels. -/
theorem cycleFamilyWithAmounts_congr (cycles : List (List K))
    (first second : K → K) (h : ∀ x ∈ cycles.flatten, first x = second x) :
    cycleFamilyWithAmounts cycles first = cycleFamilyWithAmounts cycles second := by
  -- It is enough to compare the circuits for each listed cycle.
  apply List.flatMap_congr
  intro labels hlabels
  cases labels with
  | nil => rfl
  | cons a labels =>
    apply cycleTransfersWithAmounts_congr
    intro x hx
    exact h x (List.mem_flatten.mpr ⟨a :: labels, hlabels, List.mem_cons_of_mem a hx⟩)

end Toffoli
