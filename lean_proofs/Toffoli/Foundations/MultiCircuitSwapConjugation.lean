import Toffoli.Foundations.MultiCircuitEvalAppend
import Toffoli.Foundations.CoordinateLiftGate

namespace Toffoli
open scoped Classical

/-- Swap two labels before a computation and swap them back afterwards.
The middle circuit restores its controls, so only its argument changes. -/
theorem multi_circuit_swap_conjugation {K : Type*} [Field K] {n : ℕ}
    (c : MultiCircuit K n) (f : Controls K n → K) (hc : c.Realizes f)
    (i : Fin n) (a b : K) :
    MultiCircuit.Realizes ([MultiGate.swap i a b] ++ c ++ [MultiGate.swap i a b])
      (fun x => f (Function.update x i (Equiv.swap a b (x i)))) := by
  classical
  intro x t
  simp only [multi_circuit_eval_append]
  change ((Gate.swap a b).lift i).eval
    (c.eval (((Gate.swap a b).lift i).eval (x, t))) = _
  rw [coordinate_lift_gate, hc, coordinate_lift_gate]
  simp [Gate.eval]

end Toffoli
