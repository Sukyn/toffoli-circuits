import Toffoli.Schedules.GrayScan
import Toffoli.Schedules.GrayEndpoints

namespace Toffoli

/-- The executable traversal ends with only the first group negated, giving
exactly the restoration coefficients prescribed in the paper. -/
theorem gray_final_word (n : ℕ) :
    (grayFlips (n + 1)).foldl grayFlip (fun _ => false) =
      Fin.cons true (fun _ : Fin n => false) := by
  have h := congrArg List.getLast? (gray_scan (n + 1))
  rw [List.getLast?_scanl, (gray_endpoints n).2] at h
  exact Option.some.inj h

end Toffoli
