import Toffoli.Mixed.MixedProduct
import Toffoli.Mixed.MixedLinearBound

namespace Toffoli

/-- The mixed linear bound is realized by a primitive accumulator circuit
on the original d controls and target. The constant is uniform in p and d. -/
theorem mixed_linear_circuit {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hd : 0 < d)
    (μ : ZMod p) :
    ∃ circuit : MultiCircuit (ZMod p) d,
      circuit.Realizes (fun x => μ * ∏ i, x i) ∧ circuit.cost ≤ 40 * p * d ∧
      circuit.AccumulatorLocal Finset.univ none := by
  obtain ⟨circuit, hrun, hcost, hlocal⟩ := mixed_product hp hd μ
  refine ⟨circuit, hrun, ?_, hlocal⟩
  rw [hcost]
  exact mixed_linear_bound hp hd 0

end Toffoli
