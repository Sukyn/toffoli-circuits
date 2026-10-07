import Toffoli.Additions.CycleAmounts
import Toffoli.Additions.CyclePermutationModel

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- Each block swaps the anchor with a leaf and adds its transfer increment.
Leaves may repeat; only the anchor must be absent from the leaf list. -/
theorem cycleTransfersWithAmounts_correct (a : K) (labels : List K)
    (amounts : K → K) (ha : a ∉ labels) (x t : K) :
    (cycleTransfersWithAmounts a labels amounts).eval (x, t) =
      (cyclePermutation a labels x, t + cycleAmountsIncrement a labels amounts x) := by
  induction labels generalizing x t with
  | nil => simp [cycleTransfersWithAmounts, cycleAmountsIncrement,
      cyclePermutation, Circuit.eval]
  | cons b rest ih =>
    have ⟨hab, hrest⟩ : a ≠ b ∧ a ∉ rest := by simpa using ha
    simp only [cycleTransfersWithAmounts, Circuit.eval, List.foldl_append]
    change (cycleTransfersWithAmounts a rest amounts).eval
      ((cycleTransferBlock a b (amounts b)).eval (x, t)) = _
    rw [(cycleTransferBlock_spec a b (amounts b) hab x t).1, ih hrest]
    simp [cyclePermutation, cycleAmountsIncrement, Equiv.Perm.mul_apply, add_assoc]

end Toffoli
