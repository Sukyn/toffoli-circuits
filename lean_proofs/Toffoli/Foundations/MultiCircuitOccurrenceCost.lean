import Toffoli.Foundations.MultiCircuitCostList
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Forall2

namespace Toffoli

/-- Lower-bound each occurrence in an ordered call trace, then add the bounds.
`chunks` supplies one primitive circuit per occurrence; repeated equal calls
may use different implementations. Flattening retains their execution order. -/
theorem multi_circuit_occurrence_cost {K I : Type*} [Field K] {n : ℕ}
    (calls : List I) (chunks : List (MultiCircuit K n)) (weight : I → ℕ)
    (hcost : List.Forall₂ (fun call (chunk : MultiCircuit K n) =>
      weight call ≤ MultiCircuit.cost chunk) calls chunks) :
    (calls.map weight).sum ≤ MultiCircuit.cost chunks.flatten := by
  rw [List.flatten_eq_flatMap, multi_circuit_cost_list]
  apply List.Forall₂.sum_le_sum
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using hcost

end Toffoli
