import Toffoli.Mixed.MixedLadderCostSplit

namespace Toffoli
open scoped BigOperators

/-- A ladder with m stages calls its two endpoints twice and each middle
stage four times, for a total of 4(m-1) calls. -/
theorem ladder_weight_sum {m : ℕ} (hm : 2 ≤ m) :
    (∑ j : Fin m, (if j.val = 0 ∨ j.val + 1 = m then 2 else 4)) =
      4 * (m - 1) := by
  obtain _ | _ | n := m
  · omega
  · omega
  -- Count calls by assigning unit cost to every stage.
  calc
    _ = 2 + 4 * n + 2 := by
      simpa using mixed_ladder_cost_split n (fun _ => 1)
    _ = 4 * (n + 1 + 1 - 1) := by omega

end Toffoli
