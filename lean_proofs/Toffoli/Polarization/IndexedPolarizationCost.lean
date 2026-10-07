import Toffoli.Polarization.IndexedPolarizationModel
import Toffoli.Foundations.MultiCircuitCostList
import Toffoli.Polarization.PolarizationWeightSum

namespace Toffoli

/-- Compilation adds the chosen cost for every recorded call. Scaling a
subcircuit leaves its cost unchanged, including calls with coefficient zero. -/
theorem indexed_polarization_cost {K : Type*} [Field K] {m n : ℕ}
    (group : Fin m → K → MultiCircuit K n) (power : K → MultiCircuit K n)
    (q : Fin m → ℕ) (r : ℕ)
    (hgroup : ∀ i a, (group i a).cost = q i)
    (hpower : ∀ a, (power a).cost = r)
    (calls : List (PolarizationCall K m)) :
    (compilePolarization group power calls).cost =
      polarizationPowerCalls calls * r +
        ∑ i, (polarizationGroupCalls calls).count i * q i := by
  have hcall (call : PolarizationCall K m) :
      (call.compile group power).cost = PolarizationCall.weight q r call := by
    cases call <;> simp [PolarizationCall.compile, PolarizationCall.weight, hgroup, hpower]
  rw [compilePolarization, multi_circuit_cost_list]
  simpa only [hcall] using polarization_weight_sum calls q r

end Toffoli
