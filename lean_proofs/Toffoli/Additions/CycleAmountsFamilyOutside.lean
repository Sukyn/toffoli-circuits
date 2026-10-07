import Toffoli.Additions.CycleAmountsCircuitOutside

namespace Toffoli
variable {K : Type*} [Field K]

/-- Cycle circuits leave every unlisted control value untouched, even when
the listed cycles overlap. -/
theorem cycleFamilyWithAmounts_outside (cycles : List (List K))
    (amounts : K → K) (x t : K)
    (hx : x ∉ cycles.flatten) :
    (cycleFamilyWithAmounts cycles amounts).eval (x, t) = (x, t) := by
  induction cycles with
  | nil => rfl
  | cons labels rest ih =>
    have hx' : x ∉ labels ∧ x ∉ rest.flatten := by simpa using hx
    simp only [cycleFamilyWithAmounts, List.flatMap_cons, Circuit.eval, List.foldl_append]
    change (cycleFamilyWithAmounts rest amounts).eval
      ((cycleWithAmounts labels amounts).eval (x, t)) = _
    rw [cycleWithAmounts_outside labels amounts x t hx'.1, ih hx'.2]

end Toffoli
