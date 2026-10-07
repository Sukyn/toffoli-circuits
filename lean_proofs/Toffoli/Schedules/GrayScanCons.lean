import Toffoli.Schedules.GrayFlipCons

namespace Toffoli

/-- A prefix is untouched while the shifted old traversal runs. -/
theorem gray_scan_cons {n : ℕ} (b : Bool) (word : GrayWord n) (flips : List (Fin n)) :
    (flips.map Fin.succ).scanl grayFlip (Fin.cons b word) =
      (flips.scanl grayFlip word).map (Fin.cons b) := by
  induction flips generalizing word with
  | nil => simp
  | cons i flips ih => simp [gray_flip_cons, ih]

end Toffoli
