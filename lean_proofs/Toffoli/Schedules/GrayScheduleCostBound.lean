import Toffoli.Schedules.WeightedPrefixBound
import Toffoli.Divide.DivideWeightSum

namespace Toffoli

/-- If the first j groups receive at least 2*j+2^j-1 calls and group costs
are nonincreasing, the total cost is at least the Gray-order cost. -/
theorem gray_schedule_cost_bound (n : ℕ) (cost calls : ℕ → ℕ)
    (hcost : ∀ i, i + 1 < n → cost (i + 1) ≤ cost i)
    (hcalls : ∀ j, j ≤ n → 2 * j + 2 ^ j - 1 ≤
      ∑ i ∈ Finset.range j, calls i) :
    (∑ i ∈ Finset.range n, (2 + 2 ^ i) * cost i) ≤
      ∑ i ∈ Finset.range n, calls i * cost i := by
  have hprefix (j : ℕ) (hj : j ≤ n) :
      (∑ i ∈ Finset.range j, (2 + 2 ^ i)) ≤ ∑ i ∈ Finset.range j, calls i := by
    rw [Finset.sum_range, divide_weight_sum]
    simpa only [Nat.add_comm (2 ^ j) (2 * j)] using hcalls j hj
  simpa only [Nat.mul_comm] using
    weighted_prefix_bound n cost calls (fun i => 2 + 2 ^ i) hcost hprefix

end Toffoli
