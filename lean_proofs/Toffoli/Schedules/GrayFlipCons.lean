import Toffoli.Schedules.GrayModel

namespace Toffoli

/-- Prefixing a sign shifts every old flip index by one. -/
theorem gray_flip_cons {n : ℕ} (b : Bool) (word : GrayWord n) (i : Fin n) :
    grayFlip (Fin.cons b word) i.succ = Fin.cons b (grayFlip word i) := by
  simp [grayFlip]

end Toffoli
