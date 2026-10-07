import Toffoli.Divide.DivideModel

namespace Toffoli

/-- SUM is a zero-transposition construction, so the one-control minimum is zero. -/
theorem divide_count_one (p : ℕ) : divideCount p 1 = 0 := by
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le (DivideCost.sum (p := p)))

end Toffoli
