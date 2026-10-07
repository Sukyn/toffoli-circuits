import Toffoli.Mixed.MixedBinaryLadder
import Toffoli.Mixed.MixedCountSpec
import Toffoli.Additions.CubicPowerCostBound

namespace Toffoli

/-- Balanced cubic polarization has room for binary-ladder preparations.
Its two groups are called three and four times, respectively; the four
cube additions cost at most 2*(p-1). This is a bound on numerical cost trees. -/
theorem mixed_cubic_bound {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 3 ≤ d) (b : ℕ) :
    mixedCount p hp d b ≤ 2 * (p - 1) +
      3 * binaryLadderCost (2 * optimalSquareCost p hp) (d / 2) +
      4 * binaryLadderCost (2 * optimalSquareCost p hp) ((d - 1) / 2) := by
  let c : Composition (d - 1) := {
    blocks := [d / 2, (d - 1) / 2]
    blocks_pos := by
      intro a ha
      rcases List.mem_pair.mp ha with rfl | rfl <;> omega
    blocks_sum := by
      simp
      omega }
  have hdegree : c.length + 1 ≤ p - 2 := by
    simp only [Composition.length, c, List.length_cons, List.length_nil]
    omega
  let costs (j : Fin c.length) :=
    binaryLadderCost (2 * optimalSquareCost p hp) (c.blocksFun j)

  -- Each group can borrow enough wires from the opposite group.
  have htree : MixedCost p hp d b (divideStepCost p c hdegree costs) := by
    apply MixedCost.polarization hd c hdegree costs
    intro j
    have hsize : c.blocksFun j ≤ d / 2 := by
      have hj := c.blocksFun_mem_blocks j
      change c.blocksFun j ∈ [d / 2, (d - 1) / 2] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      omega
    exact mixed_binary_ladder hp (c.one_le_blocksFun j) (by omega)

  calc
    mixedCount p hp d b ≤ divideStepCost p c hdegree costs :=
      (mixed_count_spec hp (show 0 < d by omega) b).2 _ htree
    _ = 4 * ((p - 1) - (p - 1) /
          leastAdmissibleOrder (p - 1) 3 (by decide) (by omega)) +
        3 * binaryLadderCost (2 * optimalSquareCost p hp) (d / 2) +
        4 * binaryLadderCost (2 * optimalSquareCost p hp) ((d - 1) / 2) := by
      simp [divideStepCost, costs, c, Composition.length, Composition.blocksFun,
        Fin.sum_univ_two, List.get_eq_getElem, Nat.add_assoc]
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (cubic_power_cost_bound hp) _) _

end Toffoli
