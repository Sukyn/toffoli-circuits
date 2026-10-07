import Toffoli.Foundations.MultiCircuitEvalAppend

namespace Toffoli

/-- Restored controls let successive multi-control increments add. -/
theorem multi_circuit_realizes_append {K : Type*} [Field K] {n : ℕ}
    (c d : MultiCircuit K n) (f g : Controls K n → K)
    (hc : c.Realizes f) (hd : d.Realizes g) :
    (c ++ d).Realizes (fun x => f x + g x) := by
  intro x t
  rw [multi_circuit_eval_append, hc, hd]
  simp only [add_assoc]

end Toffoli
