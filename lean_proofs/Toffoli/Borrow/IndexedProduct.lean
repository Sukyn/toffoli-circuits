import Toffoli.Mixed.MixedBinaryLadder
import Toffoli.Mixed.IndexedMixedCost

namespace Toffoli

/-- Compile a nonempty product on any set of controls, borrowing exactly
`d - 2` other wires. The ladder restores all borrowed wires; the target
may itself be an internal wire outside both supplied sets. The coefficient
may be zero without changing the exact count. -/
theorem indexed_product {p n : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (controls borrowed : Finset (Fin n)) (hnonempty : controls.Nonempty)
    (hcard : borrowed.card = controls.card - 2)
    (hdisjoint : Disjoint controls borrowed) (target : IndexedTarget n)
    (htarget : ∀ i ∈ controls ∪ borrowed, target ≠ some i)
    (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      (∀ x t, c.eval (x, t) =
        indexedTargetAdd target (μ * ∏ i ∈ controls, x i) (x, t)) ∧
      c.cost = binaryLadderCost (2 * optimalSquareCost p hp) controls.card := by
  classical
  -- Compile the fixed binary tree; no mixedCount minimization is used.
  have tree := mixed_binary_ladder hp hnonempty.card_pos hcard.ge
  obtain ⟨c, hrun, hcost, _⟩ := indexed_mixed_cost hp tree controls (controls ∪ borrowed)
    Finset.subset_union_left rfl (Finset.card_union_of_disjoint hdisjoint) target htarget μ
  exact ⟨c, hrun, hcost⟩

end Toffoli
