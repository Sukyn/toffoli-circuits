import Toffoli.Foundations.MultiConstantAddition
import Toffoli.Foundations.MultiLinearAddition
import Toffoli.Foundations.MultiCircuitRealizesAppend
import Toffoli.Foundations.MultiCircuitCostAppend

namespace Toffoli

/-- A constant followed by a linear accumulator addition uses no transpositions. -/
theorem multi_affine_addition {K : Type*} [Field K] {n : ℕ}
    (i : Fin n) (b : K) (a : Fin n → K) :
    ∃ c : MultiCircuit K n, c.Realizes (fun x => b + ∑ j, a j * x j) ∧ c.cost = 0 := by
  obtain ⟨constant, hconstant, hc⟩ := multi_constant_addition i b
  obtain ⟨linear, hlinear, hl⟩ := multi_linear_addition (1 : K) a
  refine ⟨constant ++ linear, ?_, ?_⟩
  · simpa only [one_mul] using
      multi_circuit_realizes_append _ _ _ _ hconstant hlinear
  · simp [multi_circuit_cost_append, hc, hl]

end Toffoli
