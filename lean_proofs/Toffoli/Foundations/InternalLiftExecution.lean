import Toffoli.Foundations.InternalLiftGate

namespace Toffoli

/-- Execute the original circuit on coordinates i and j, leaving the other
controls and the outer target unchanged. -/
theorem internal_lift_execution {K : Type*} [Field K] {n : ℕ}
    (c : Circuit K) (i j : Fin n) (hij : i ≠ j) (x : Controls K n) (t : K) :
    (c.internalLift i j hij).eval (x, t) =
      (Function.update (Function.update x i (c.eval (x i, x j)).1)
        j (c.eval (x i, x j)).2, t) := by
  classical
  induction c generalizing x with
  | nil => simp [Circuit.internalLift, MultiCircuit.eval, Circuit.eval]
  | cons gate rest ih =>
    change (Circuit.internalLift rest i j hij).eval ((gate.internalLift i j hij).eval (x, t)) = _
    rw [internal_lift_gate, ih]
    simp [Circuit.eval, Function.update_comm hij, hij]

end Toffoli
