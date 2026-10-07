import Toffoli.Mixed.MixedModel

namespace Toffoli

/-- A single control uses a free SUM, regardless of the available workspace. -/
theorem mixed_count_one {p : ℕ} (hp : 5 ≤ p) (b : ℕ) :
    mixedCount p hp 1 b = 0 := by
  exact Nat.eq_zero_of_le_zero
    (Nat.sInf_le (MixedCost.sum (p := p) (hp := hp) b))

end Toffoli
