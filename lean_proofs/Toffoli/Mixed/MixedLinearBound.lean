import Toffoli.Mixed.MixedBorrowBound
import Toffoli.Borrow.BorrowCostBound

namespace Toffoli

/-- The numerical mixed minimum satisfies Borrow's linear bound for every
workspace budget. For b = 0, `mixed_linear_circuit` constructs a circuit
with this bound. -/
theorem mixed_linear_bound {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 0 < d) (b : ℕ) : mixedCount p hp d b ≤ 40 * p * d := by
  exact (mixed_borrow_bound hp hd b).trans (borrow_cost_bound hp hd)

end Toffoli
