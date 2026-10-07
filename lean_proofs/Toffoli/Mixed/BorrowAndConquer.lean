import Toffoli.Mixed.MixedProduct
import Toffoli.Mixed.MixedComparison

namespace Toffoli

/-- Borrow-and-conquer gives a circuit on the original wires with cost
`mixedCount p hp d 0`, no greater than either Divide or Borrow. The circuit
has accumulator form at every gate, even when the coefficient is zero. -/
theorem borrow_and_conquer {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hd : 0 < d)
    (μ : ZMod p) :
    ∃ circuit : MultiCircuit (ZMod p) d,
      circuit.Realizes (fun x => μ * ∏ i, x i) ∧
      circuit.cost = mixedCount p hp d 0 ∧
      circuit.cost ≤ min (divideCount p d) (borrowCost (2 * optimalSquareCost p hp) d) ∧
      circuit.AccumulatorLocal Finset.univ none := by
  obtain ⟨circuit, hrun, hcost, hlocal⟩ := mixed_product hp hd μ
  refine ⟨circuit, hrun, hcost, ?_, hlocal⟩
  rw [hcost]
  exact mixed_comparison hp hd 0

end Toffoli
