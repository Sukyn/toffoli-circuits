import Toffoli.Additions.CycleAmounts

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- A transfer sequence adds nothing outside its listed cycle. -/
theorem cycleAmountsIncrement_outside (a : K) (labels : List K)
    (amounts : K → K) (x : K) (hx : x ∉ a :: labels) :
    cycleAmountsIncrement a labels amounts x = 0 := by
  induction labels with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.mem_cons, not_or] at hx
    have hx' : x ∉ a :: rest := by simpa using And.intro hx.1 hx.2.2
    simp [cycleAmountsIncrement, transferIncrement, Equiv.swap_apply_def,
      hx.1, hx.2.1, ih hx']

end Toffoli
