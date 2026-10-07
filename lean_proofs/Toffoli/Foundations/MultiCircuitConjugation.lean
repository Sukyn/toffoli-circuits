import Toffoli.Foundations.MultiCircuitEvalAppend

namespace Toffoli

/-- Compute in affine coordinates, then undo their change. The circuit's
restoration guarantee ensures the final affine map restores every control. -/
theorem multi_circuit_conjugation {K : Type*} [Field K] {n : ℕ}
    (c : MultiCircuit K n) (f : Controls K n → K) (hc : c.Realizes f)
    (e : Controls K n ≃ᵃ[K] Controls K n) :
    MultiCircuit.Realizes ([MultiGate.affine e] ++ c ++ [MultiGate.affine e.symm])
      (fun x => f (e x)) := by
  intro x t
  simp only [multi_circuit_eval_append]
  change (MultiGate.affine e.symm).eval (c.eval ((MultiGate.affine e).eval (x, t))) = _
  simp only [MultiGate.eval, MultiGate.control, MultiGate.increment, add_zero]
  rw [hc]
  simp

end Toffoli
