import Toffoli.Mixed.MixedCostExists

namespace Toffoli

/-- The mixed minimum is attained by a finite construction tree, and it
is no greater than the cost of any other tree with the same workspace. -/
theorem mixed_count_spec {p d : ℕ} (hp : 5 ≤ p) (hd : 0 < d) (b : ℕ) :
    MixedCost p hp d b (mixedCount p hp d b) ∧
      ∀ cost, MixedCost p hp d b cost → mixedCount p hp d b ≤ cost := by
  exact ⟨Nat.sInf_mem (mixed_cost_exists hp hd b), fun _ hcost => Nat.sInf_le hcost⟩

end Toffoli
