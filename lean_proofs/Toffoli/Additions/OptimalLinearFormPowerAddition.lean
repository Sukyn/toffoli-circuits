import Toffoli.Additions.OptimalPowerAddition
import Toffoli.Additions.LinearFormPreparation
import Toffoli.Foundations.CoordinateLiftRealizes
import Toffoli.Foundations.CoordinateLiftCost
import Toffoli.Foundations.MultiCircuitConjugation
import Toffoli.Foundations.MultiCircuitConjugationCost

namespace Toffoli

/-- Prepare a nonzero linear form, run the shared least-order power circuit,
then undo the preparation. Lifting and affine conjugation preserve its exact
count. A zero coefficient retains the full circuit; its count is a construction
cost and does not assert optimality for the zero function. -/
theorem optimal_linear_form_power_addition {p n : ℕ} [Fact p.Prime]
    (μ : ZMod p) (b : Fin n → ZMod p) (hb : ∃ i, b i ≠ 0)
    (d : ℕ) (hd : 0 < d) (hbound : d < p - 1) :
    ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => μ * (∑ i, b i * x i) ^ d) ∧
      c.cost = (p - 1) - (p - 1) / leastAdmissibleOrder (p - 1) d hd hbound := by
  obtain ⟨i, hi⟩ := hb
  obtain ⟨e, he, _⟩ := linear_form_preparation b i hi
  obtain ⟨c, hc, hcost⟩ := optimal_power_addition μ d hd hbound
  refine ⟨[.affine e] ++ c.lift i ++ [.affine e.symm], ?_, ?_⟩
  · simpa only [he] using multi_circuit_conjugation (c.lift i)
      (fun x => μ * x i ^ d) (coordinate_lift_realizes c _ hc i) e
  · rw [multi_circuit_conjugation_cost, coordinate_lift_cost]
    exact hcost

end Toffoli
