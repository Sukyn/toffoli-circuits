import Toffoli.Polarization.GroupedPolarization

namespace Toffoli

/-- Scaling the power additions scales the resulting product addition.
The preparation and restoration calls, and hence all call counts, stay the same. -/
theorem scaled_grouped_polarization {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (n : ℕ) (hdegree : n + 1 ≤ p - 2) (factors : Fin n → ZMod p)
    (μ x t : ZMod p) :
    let calls := polarizationCircuit (n := n)
      (μ * (((2 : ZMod p) ^ n * ((n + 1).factorial : ZMod p))⁻¹))
    runPolarization factors calls (x, t) = (x, t + μ * x * ∏ i, factors i) ∧
      polarizationPowerCalls calls = 2 ^ n ∧
      ∀ i : Fin n, (polarizationGroupCalls calls).count i = 2 + 2 ^ i.val := by
  -- The unit-coefficient construction already identifies the normalized sum.
  have hunit := congrArg Prod.snd
    (grouped_polarization hp n hdegree factors x 0).1
  simp only [polarization_circuit_run, zero_add] at hunit
  refine ⟨?_, polarization_circuit_calls _⟩
  -- Multiply that identity by μ; no division by μ is needed, even when μ = 0.
  rw [polarization_circuit_run, mul_assoc, hunit, ← mul_assoc]

end Toffoli
