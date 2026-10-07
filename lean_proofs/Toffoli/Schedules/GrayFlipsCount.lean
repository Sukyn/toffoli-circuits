import Toffoli.Schedules.GrayModel

namespace Toffoli

/-- Group i changes sign 2^i times, with the slowest group indexed by zero. -/
theorem gray_flips_count (n : ℕ) (i : Fin n) : (grayFlips n).count i = 2 ^ i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hz : ((grayFlips n).map Fin.succ).count 0 = 0 :=
      List.count_eq_zero.mpr (by simp)
    cases i using Fin.cases with
    | zero => simp [grayFlips, hz]
    | succ i =>
      have hs := List.count_map_of_injective (grayFlips n) Fin.succ (Fin.succ_injective n) i
      simp [grayFlips, hs, ih, Ne.symm (Fin.succ_ne_zero i), Nat.pow_succ, Nat.mul_two]

end Toffoli
