import Toffoli.Foundations.CoordinateLiftExecution

namespace Toffoli

/-- Lifting `c` to control `i` adds `f (x i)` to the target. It restores
control `i` and leaves the other controls untouched. -/
theorem coordinate_lift_realizes {K : Type*} [Field K] {n : ℕ}
    (c : Circuit K) (f : K → K) (hc : c.Realizes f) (i : Fin n) :
    (c.lift i).Realizes (fun x => f (x i)) := by
  intro x t
  rw [coordinate_lift_execution, hc]
  simp

end Toffoli
