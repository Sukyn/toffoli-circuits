import Toffoli.Mixed.MixedCountSpec
import Toffoli.Mixed.MixedLadderControls
import Toffoli.Divide.DivideStepCostMono

namespace Toffoli

/-- The mixed count is exactly the minimum over polarization and ladder
choices with minimum-cost children. Every such choice is realizable as a
cost tree; conversely, minimizing the children of an attaining tree cannot
increase its cost. -/
theorem mixed_recurrence {p d : ℕ} (hp : 5 ≤ p) (hd : 3 ≤ d) (b : ℕ) :
    IsLeast {q | MixedPolarizationChoice p hp d b q ∨ MixedLadderChoice p hp d b q}
      (mixedCount p hp d b) := by
  obtain ⟨hattained, hleast⟩ := mixed_count_spec hp (show 0 < d by omega) b
  -- Any allowed step with minimum-cost children is itself a construction.
  have hbound (q : ℕ)
      (hchoice : MixedPolarizationChoice p hp d b q ∨ MixedLadderChoice p hp d b q) :
      mixedCount p hp d b ≤ q := by
    apply hleast
    rcases hchoice with ⟨c, hdegree, rfl⟩ | ⟨L, rfl⟩
    · apply MixedCost.polarization hd c hdegree
      intro j
      exact (mixed_count_spec hp (c.one_le_blocksFun j) _).1
    · apply MixedCost.ladder hd L
      intro j
      exact (mixed_count_spec hp (mixed_ladder_controls L j).1 _).1
  refine ⟨?_, fun _ h => hbound _ h⟩
  -- An attaining tree has one of these two outer steps; minimize its children.
  generalize hcount : mixedCount p hp d b = total at hattained
  cases hattained with
  | sum => omega
  | toffoli => omega
  | polarization _ c hdegree costs hchildren =>
    left
    refine ⟨c, hdegree, le_antisymm ?_ ?_⟩
    · simpa only [hcount] using hbound _ (Or.inl ⟨c, hdegree, rfl⟩)
    · apply divide_step_cost_mono
      intro j
      exact (mixed_count_spec hp (c.one_le_blocksFun j) _).2 _ (hchildren j)
  | ladder _ L costs hchildren =>
    right
    refine ⟨L, le_antisymm ?_ ?_⟩
    · simpa only [hcount] using hbound _ (Or.inr ⟨L, rfl⟩)
    · apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_left _
        ((mixed_count_spec hp (mixed_ladder_controls L j).1 _).2 _ (hchildren j))

end Toffoli
