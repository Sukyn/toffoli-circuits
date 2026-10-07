import Toffoli.Mixed.IndexedMixedFamily
import Toffoli.Mixed.MixedCircuitFamilyLower
import Toffoli.Mixed.MixedComparison

namespace Toffoli

/-- The workspace-aware recurrence is the exact minimum over primitive
Borrow-and-conquer circuits. On every legal pool it has an attaining family
member, with the required product update and gatewise accumulator form.

The lower bound covers every independent choice at every trace occurrence,
including nonoptimal affine-cycle power leaves. The paper uses `μ = 1`;
the same conclusion holds for every nonzero scalar. -/
theorem mixed_family_minimum {p d b n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hd : 0 < d)
    (controls pool : Finset (Fin n)) (hsubset : controls ⊆ pool)
    (hcontrols : controls.card = d) (hpool : pool.card = d + b)
    (target : IndexedTarget n) (htarget : ∀ i ∈ pool, target ≠ some i)
    (μ : ZMod p) (hμ : μ ≠ 0) :
    ∃ circuit : MultiCircuit (ZMod p) n,
      MixedCircuitFamily d b controls pool target μ circuit ∧
      (∀ x t, circuit.eval (x, t) =
        indexedTargetAdd target (μ * ∏ i ∈ controls, x i) (x, t)) ∧
      circuit.cost = mixedCount p hp d b ∧
      circuit.AccumulatorLocal pool target ∧
      circuit.cost ≤ min (divideCount p d) (borrowCost (2 * optimalSquareCost p hp) d) ∧
      ∀ other, MixedCircuitFamily d b controls pool target μ other →
        circuit.cost ≤ other.cost := by
  obtain ⟨circuit, member, hrun, hcost, hlocal⟩ :=
    indexed_mixed_family hp (mixed_count_spec hp hd b).1
      controls pool hsubset hcontrols hpool target htarget μ
  refine ⟨circuit, member, hrun, hcost, hlocal, ?_, ?_⟩
  · rw [hcost]
    exact mixed_comparison hp hd b
  · intro other hother
    rw [hcost]
    exact mixed_circuit_family_lower hp hother hμ

end Toffoli
