import Toffoli.Foundations.MultiCircuitOccurrenceCost
import Toffoli.Polarization.PolarizationCircuitCalls
import Toffoli.Polarization.PolarizationWeightSum

namespace Toffoli

/-- The paper's polarization weights also give a lower bound when every
occurrence chooses its own primitive implementation. The chunks follow the
preparation, Gray walk, and restoration trace in exactly that order. -/
theorem polarization_occurrence_cost {K : Type*} [Field K] {m n : ℕ}
    (normalization : K) (q : Fin m → ℕ) (r : ℕ)
    (chunks : List (MultiCircuit K n))
    (hcost : List.Forall₂ (fun (call : PolarizationCall K m) (chunk : MultiCircuit K n) =>
      PolarizationCall.weight q r call ≤ MultiCircuit.cost chunk)
      (polarizationCircuit (n := m) normalization) chunks) :
    2 ^ m * r + (∑ i : Fin m, (2 + 2 ^ i.val) * q i) ≤
      MultiCircuit.cost chunks.flatten := by
  have hbound := multi_circuit_occurrence_cost
    (polarizationCircuit (n := m) normalization) chunks (PolarizationCall.weight q r) hcost
  rw [polarization_weight_sum] at hbound
  obtain ⟨hpower, hgroups⟩ := polarization_circuit_calls (n := m) normalization
  simpa only [hpower, hgroups] using hbound

end Toffoli
