import Toffoli.Additions.CycleAmounts

namespace Toffoli
variable {K : Type*} [Field K]

/-- Outside the listed labels every swap is inactive, so each pair of SUMs
cancels. This does not require the labels to be distinct. -/
theorem cycleWithAmounts_outside (labels : List K) (amounts : K → K)
    (x t : K) (hx : x ∉ labels) :
    (cycleWithAmounts labels amounts).eval (x, t) = (x, t) := by
  cases labels with
  | nil => rfl
  | cons a rest =>
    change (cycleTransfersWithAmounts a rest amounts).eval (x, t) = (x, t)
    induction rest with
    | nil => rfl
    | cons b rest ih =>
      simp only [List.mem_cons, not_or] at hx
      have hx' : x ∉ a :: rest := by simpa using And.intro hx.1 hx.2.2
      simpa [cycleTransfersWithAmounts, cycleTransferBlock, Circuit.eval,
        List.foldl_append, Gate.eval, Equiv.swap_apply_def, hx.1, hx.2.1]
        using ih hx'

end Toffoli
