import Toffoli.Schedules.GrayModel

namespace Toffoli

/-- Changing the same sign twice restores the word. -/
theorem gray_flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (fun w => grayFlip w i) := by
  intro word
  simp [grayFlip]

end Toffoli
