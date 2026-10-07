import Toffoli.Mixed.IndexedMixedCost
import Toffoli.Mixed.MixedCountSpec

namespace Toffoli

/-- An attaining mixed tree gives an actual circuit on the original controls
and target, with no extra wires. It restores every control, has the exact
numerical minimum cost, and preserves accumulator locality at every gate. -/
theorem mixed_product {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hd : 0 < d)
    (μ : ZMod p) :
    ∃ circuit : MultiCircuit (ZMod p) d,
      circuit.Realizes (fun x => μ * ∏ i, x i) ∧
      circuit.cost = mixedCount p hp d 0 ∧
      circuit.AccumulatorLocal Finset.univ none := by
  obtain ⟨circuit, hrun, hcost, hlocal⟩ :=
    indexed_mixed_cost hp (mixed_count_spec hp hd 0).1
      (Finset.univ : Finset (Fin d)) Finset.univ
      (by simp) (by simp) (by simp) none (by simp) μ
  exact ⟨circuit, by simpa only [indexedTargetAdd] using hrun, hcost, hlocal⟩

end Toffoli
