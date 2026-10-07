import Toffoli.Schedules.GrayModel

namespace Toffoli

/-- Every new group doubles the number of signed sums. -/
theorem gray_words_length (n : ℕ) : (grayWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [grayWords, ih, Nat.pow_succ, Nat.mul_two]

end Toffoli
