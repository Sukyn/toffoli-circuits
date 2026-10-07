import Toffoli.Mixed.MixedModel

namespace Toffoli

/-- A mixed construction exists with any nonnegative workspace budget.
After SUM and Toffoli, one polarization group adds a control while leaving
the recursive child's workspace budget unchanged. -/
theorem mixed_cost_exists {p d : ℕ} (hp : 5 ≤ p) (hd : 0 < d) (b : ℕ) :
    ∃ cost, MixedCost p hp d b cost := by
  change 1 ≤ d at hd
  induction d, hd using Nat.le_induction with
  | base => exact ⟨0, MixedCost.sum b⟩
  | succ d hd ih =>
    by_cases hone : d = 1
    · subst d
      exact ⟨_, MixedCost.toffoli b⟩
    obtain ⟨cost, hcost⟩ := ih
    let c := Composition.single d hd
    have hdegree : c.length + 1 ≤ p - 2 := by
      simp only [c, Composition.single_length]
      omega
    refine ⟨_, MixedCost.polarization (show 3 ≤ d + 1 by omega)
      c hdegree (fun _ => cost) ?_⟩
    intro j
    change MixedCost p hp (c.blocksFun j) (d + 1 + b - c.blocksFun j - 1) cost
    simpa only [c, Composition.single_blocksFun,
      show d + 1 + b - d - 1 = b by omega] using hcost

end Toffoli
