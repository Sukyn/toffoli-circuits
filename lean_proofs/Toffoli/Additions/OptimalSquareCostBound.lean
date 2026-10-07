import Toffoli.Quadratic.QuadraticModel

namespace Toffoli

/-- A square circuit costs strictly less than p-1: its admissible order
divides p-1, so the cycle count subtracted from p-1 is positive. -/
theorem optimal_square_cost_bound (p : ℕ) (hp : 5 ≤ p) :
    optimalSquareCost p hp < p - 1 := by
  obtain ⟨hpositive, hdivides, _⟩ := (least_admissible_order_spec (p - 1) 2
    (by decide) (by omega)).1
  have hquotient : 0 < (p - 1) / optimalSquareOrder p hp :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdivides) hpositive
  unfold optimalSquareCost
  exact tsub_lt_self (by omega) hquotient

end Toffoli
