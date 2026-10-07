import Toffoli.Mixed.MixedCountSpec

namespace Toffoli

/-- Two controls use the fixed Toffoli base case. Recursive polarization
and ladder steps begin at three controls, so no other base cost is possible. -/
theorem mixed_count_two {p : ℕ} (hp : 5 ≤ p) (b : ℕ) :
    mixedCount p hp 2 b = 2 * optimalSquareCost p hp := by
  have honly (cost : ℕ) (h : MixedCost p hp 2 b cost) :
      cost = 2 * optimalSquareCost p hp := by
    cases h with
    | toffoli => rfl
    | polarization hd => omega
    | ladder hd => omega
  exact honly _ (mixed_count_spec hp (by decide : 0 < 2) b).1

end Toffoli
