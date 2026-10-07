import Toffoli.Foundations.MultiControlModel

namespace Toffoli

/-- Preparing and undoing a linear form adds no transpositions. -/
theorem multi_circuit_conjugation_cost {K : Type*} [Field K] {n : ℕ}
    (c : MultiCircuit K n) (e : Controls K n ≃ᵃ[K] Controls K n) :
    MultiCircuit.cost ([.affine e] ++ c ++ [.affine e.symm]) = c.cost := by
  simp [MultiCircuit.cost, MultiGate.cost]

end Toffoli
