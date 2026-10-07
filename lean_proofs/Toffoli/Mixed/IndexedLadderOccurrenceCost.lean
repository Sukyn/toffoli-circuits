import Toffoli.Mixed.IndexedLadderTraceCost
import Toffoli.Foundations.MultiCircuitCostList

namespace Toffoli

/-- Each signed occurrence has its own primitive chunk. Their lower bounds
add with the ladder weights, even when repeated calls choose different circuits. -/
theorem indexed_ladder_occurrence_cost {K : Type*} [Field K] {n m : ℕ}
    (μ : K) (q : Fin (m + 2) → ℕ)
    (chunks : Fin (indexedLadderTrace m μ).length → MultiCircuit K n)
    (hcost : ∀ i, q ((indexedLadderTrace m μ).get i).1 ≤ (chunks i).cost) :
    (∑ j, (if j.val = 0 ∨ j.val + 1 = m + 2 then 2 else 4) * q j) ≤
      MultiCircuit.cost (List.ofFn chunks).flatten := by
  -- Index both sums by occurrences; the supplied bound applies term by term.
  rw [← indexed_ladder_trace_cost m μ q, List.flatten_eq_flatMap,
    multi_circuit_cost_list]
  conv_lhs => rw [← List.ofFn_get (indexedLadderTrace m μ)]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, id_eq]
  exact Finset.sum_le_sum (fun i _ => hcost i)

end Toffoli
