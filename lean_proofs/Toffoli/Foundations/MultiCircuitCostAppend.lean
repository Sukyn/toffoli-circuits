import Toffoli.Foundations.MultiControlModel

namespace Toffoli

/-- Concatenation adds the transposition counts of its two circuits. -/
theorem multi_circuit_cost_append {K : Type*} [Field K] {n : ℕ}
    (c d : MultiCircuit K n) : (c ++ d).cost = c.cost + d.cost := by
  simp [MultiCircuit.cost, List.map_append, List.sum_append]

end Toffoli
