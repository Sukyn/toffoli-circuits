import Toffoli.Mixed.MixedModel
import Toffoli.Borrow.BinaryLadderCostModel
import Toffoli.Borrow.LadderWeightSum

namespace Toffoli

/-- With d-2 borrowed wires, the mixed family contains the binary ladder.
Its first group has two controls; every later singleton also uses the
preceding accumulator, so every update is a Toffoli base case. -/
theorem mixed_binary_ladder {p d b : ℕ} (hp : 5 ≤ p) (hd : 0 < d)
    (hb : d - 2 ≤ b) :
    MixedCost p hp d b (binaryLadderCost (2 * optimalSquareCost p hp) d) := by
  by_cases hone : d = 1
  · subst d
    simpa [binaryLadderCost] using MixedCost.sum (p := p) (hp := hp) b
  by_cases htwo : d = 2
  · subst d
    simpa [binaryLadderCost] using MixedCost.toffoli (p := p) (hp := hp) b
  have hlarge : 3 ≤ d := by omega
  let c : Composition d := {
    blocks := 2 :: List.replicate (d - 2) 1
    blocks_pos := by
      simp
    blocks_sum := by simp; omega }
  have hlength : c.length = d - 1 := by
    simp only [Composition.length, c, List.length_cons, List.length_replicate]
    omega
  have hblocks (j : Fin c.length) :
      c.blocksFun j = if j.val = 0 then 2 else 1 := by
    simp [Composition.blocksFun, c, List.get_eq_getElem, List.getElem_cons]
  let L : MixedLadder d b := {
    groups := c
    at_least_two := by omega
    workspace := by omega
    smaller := by
      intro j hj
      rw [hblocks, if_neg (show j.val ≠ 0 by omega)]
      omega }
  have hcontrols (j : Fin L.groups.length) : L.controls j = 2 := by
    change c.blocksFun j + (if j.val = 0 then 0 else 1) = 2
    rw [hblocks]
    by_cases hj : j.val = 0 <;> simp [hj]
  let C2 := 2 * optimalSquareCost p hp
  have hcost : L.cost (fun _ => C2) = 4 * (d - 2) * C2 := by
    rw [MixedLadder.cost, ← Finset.sum_mul, ladder_weight_sum L.at_least_two]
    change 4 * (c.length - 1) * C2 = _
    simp [hlength, Nat.sub_sub]
  have tree : MixedCost p hp d b (L.cost (fun _ => C2)) := by
    apply MixedCost.ladder hlarge L (fun _ => C2)
    intro j
    rw [hcontrols]
    exact MixedCost.toffoli _
  simpa only [hcost, binaryLadderCost, if_neg (show ¬ d ≤ 1 by omega),
    if_neg htwo] using tree

end Toffoli
