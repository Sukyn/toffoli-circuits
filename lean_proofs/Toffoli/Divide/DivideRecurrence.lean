import Toffoli.Divide.DivideCountSpec
import Toffoli.Divide.DivideStepCostMono

namespace Toffoli

/-- The recursive minimum equals one grouped step with minimum-cost
children, and is no greater than the value for any other grouping. -/
theorem divide_recurrence {p d : ℕ} (hp : 5 ≤ p) (hd : 2 ≤ d) :
    (∃ (c : Composition (d - 1)) (hdegree : c.length + 1 ≤ p - 2),
      divideCount p d = divideStepCost p c hdegree
        (fun j => divideCount p (c.blocksFun j))) ∧
    (∀ (c : Composition (d - 1)) (hdegree : c.length + 1 ≤ p - 2),
      divideCount p d ≤ divideStepCost p c hdegree
        (fun j => divideCount p (c.blocksFun j))) := by
  obtain ⟨hattained, hleast⟩ := divide_count_spec hp (show 0 < d by omega)
  -- Any grouping of minimum-cost children is itself a construction.
  have hbound (c : Composition (d - 1)) (hdegree : c.length + 1 ≤ p - 2) :
      divideCount p d ≤ divideStepCost p c hdegree
        (fun j => divideCount p (c.blocksFun j)) := by
    apply hleast
    apply DivideCost.step hd c hdegree
    intro j
    exact (divide_count_spec hp (c.one_le_blocksFun j)).1
  refine ⟨?_, hbound⟩
  -- Start from an attaining tree and minimize each of its children.
  generalize hcount : divideCount p d = total at hattained
  cases hattained with
  | sum => omega
  | step _ c hdegree costs hchildren =>
    refine ⟨c, hdegree, le_antisymm (hcount ▸ hbound c hdegree) ?_⟩
    apply divide_step_cost_mono
    intro j
    exact (divide_count_spec hp (c.one_le_blocksFun j)).2 _ (hchildren j)

end Toffoli
