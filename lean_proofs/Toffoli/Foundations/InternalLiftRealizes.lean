import Toffoli.Foundations.InternalLiftExecution

namespace Toffoli

/-- A one-control addition can prepare another control as temporary
workspace. The source, remaining controls, and outer target are preserved. -/
theorem internal_lift_realizes {K : Type*} [Field K] {n : ℕ}
    (c : Circuit K) (f : K → K) (hc : c.Realizes f)
    (i j : Fin n) (hij : i ≠ j) (x : Controls K n) (t : K) :
    (c.internalLift i j hij).eval (x, t) =
      (Function.update x j (x j + f (x i)), t) := by
  rw [internal_lift_execution, hc]
  simp

end Toffoli
