import Toffoli.Foundations.CoordinateLiftGate

namespace Toffoli

/-- Lifting commutes with the execution of a whole gate list. In particular,
intermediate changes to the selected control have their original semantics. -/
theorem coordinate_lift_execution {K : Type*} [Field K] {n : ℕ}
    (c : Circuit K) (i : Fin n) (x : Controls K n) (t : K) :
    (c.lift i).eval (x, t) =
      (Function.update x i (c.eval (x i, t)).1, (c.eval (x i, t)).2) := by
  classical
  induction c generalizing x t with
  | nil => simp [Circuit.lift, MultiCircuit.eval, Circuit.eval]
  | cons gate rest ih =>
    change (Circuit.lift rest i).eval ((gate.lift i).eval (x, t)) = _
    rw [coordinate_lift_gate, ih]
    simp [Circuit.eval]

end Toffoli
