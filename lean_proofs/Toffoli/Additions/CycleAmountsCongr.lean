import Toffoli.Additions.CycleAmounts

namespace Toffoli
variable {K : Type*} [Field K]

/-- Only amounts at non-anchor labels affect a star-transfer sequence. -/
theorem cycleTransfersWithAmounts_congr (a : K) (labels : List K)
    (first second : K → K) (h : ∀ x ∈ labels, first x = second x) :
    cycleTransfersWithAmounts a labels first =
      cycleTransfersWithAmounts a labels second := by
  induction labels with
  | nil => rfl
  | cons b rest ih =>
    simp only [cycleTransfersWithAmounts]
    rw [h b (by simp), ih (fun x hx => h x (by simp [hx]))]

end Toffoli
