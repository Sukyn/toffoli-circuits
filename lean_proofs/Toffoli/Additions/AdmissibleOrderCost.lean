import Toffoli.Additions.AdmissibleOrder

namespace Toffoli

/-- For positive orders, n-n/r increases with r. When r divides n this is
exactly the cycle count (n/r)*(r-1), written without rational arithmetic. -/
theorem admissible_order_cost_mono (n r s : ℕ) (hr : 0 < r) (hrs : r ≤ s) :
    n - n / r ≤ n - n / s := by
  exact Nat.sub_le_sub_left (Nat.div_le_div_left (a := n) hrs hr) n

end Toffoli
