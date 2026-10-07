import Toffoli.Foundations.MultiCircuitRealizesList
import Mathlib.Algebra.BigOperators.Fin

namespace Toffoli

/-- A linear form needs one scaled SUM per coordinate. For example,
μ*(2*x_0+3*x_1) uses coefficients 2*μ and 3*μ on those two wires. -/
theorem multi_linear_addition {K : Type*} [Field K] {n : ℕ}
    (μ : K) (b : Fin n → K) :
    ∃ c : MultiCircuit K n, c.Realizes (fun x => μ * ∑ i, b i * x i) ∧ c.cost = 0 := by
  let term : Fin n → MultiCircuit K n := fun i => [MultiGate.sum i (μ * b i)]
  have hterm (i : Fin n) : (term i).Realizes (fun x => (μ * b i) * x i) := by
    intro x t
    simp [term, MultiCircuit.eval, MultiGate.eval, MultiGate.control, MultiGate.increment]
  refine ⟨(List.finRange n).flatMap term, ?_, ?_⟩
  · have hsum := multi_circuit_realizes_list (List.finRange n) term
      (fun i x => (μ * b i) * x i) (fun i _ => hterm i)
    simpa [← List.ofFn_eq_map, List.sum_ofFn, Finset.mul_sum, mul_assoc] using hsum
  · simp [term, MultiCircuit.cost, ← List.map_eq_flatMap, List.map_map, Function.comp_def,
      MultiGate.cost]

end Toffoli
