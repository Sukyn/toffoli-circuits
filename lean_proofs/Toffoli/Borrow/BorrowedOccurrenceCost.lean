import Toffoli.Foundations.MultiCircuitOccurrenceCost
import Toffoli.Borrow.BorrowedCalls

namespace Toffoli

/-- Occurrence-wise lower bounds add with the ladder's endpoint and middle
weights. The chunks follow both preparation and undo passes in the recorded
order; repeated calls may choose different primitive implementations. -/
theorem borrowed_occurrence_cost {K : Type*} [Field K] {n : ℕ}
    (first : ℕ) (middle : List ℕ) (last : ℕ)
    (chunks : List (MultiCircuit K n))
    (hcost : List.Forall₂ (fun call (chunk : MultiCircuit K n) =>
      BorrowedCall.cost call ≤ MultiCircuit.cost chunk)
      (borrowedCalls first middle last) chunks) :
    2 * first + 4 * middle.sum + 2 * last ≤ MultiCircuit.cost chunks.flatten := by
  have hbound := multi_circuit_occurrence_cost
    (borrowedCalls first middle last) chunks BorrowedCall.cost hcost
  simpa only [borrowedCalls_cost] using hbound

end Toffoli
