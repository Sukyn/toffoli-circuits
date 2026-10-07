import Toffoli.Quadratic.QuadraticModel

namespace Toffoli

/-- An admissible multiplier has order at least two, so a square addition
costs at least half of p-1 transpositions. -/
theorem optimal_square_cost_lower_bound {p : ℕ} (hp : 5 ≤ p) :
    p - 1 ≤ 2 * optimalSquareCost p hp := by
  let r := optimalSquareOrder p hp
  obtain ⟨hpositive, _, hnot⟩ : 0 < r ∧ r ∣ p - 1 ∧ ¬r ∣ 2 :=
    (least_admissible_order_spec (p - 1) 2 (by decide) (by omega)).1
  have horder : 2 ≤ r :=
    (Nat.two_le_iff r).2
      ⟨Nat.ne_of_gt hpositive, fun h => hnot (by simp [h])⟩
  have hquotient := Nat.div_le_div_left (a := p - 1) horder (by decide : 0 < 2)
  change p - 1 ≤ 2 * ((p - 1) - (p - 1) / r)
  omega

end Toffoli
