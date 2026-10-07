import Toffoli.Divide.DivideCostExists

namespace Toffoli

/-- The minimum is attained by a construction, and is no greater than
the cost of any other construction in the recursive family. -/
theorem divide_count_spec {p d : ℕ} (hp : 5 ≤ p) (hd : 0 < d) :
    DivideCost p d (divideCount p d) ∧
      ∀ q, DivideCost p d q → divideCount p d ≤ q := by
  exact ⟨Nat.sInf_mem (divide_cost_exists hp hd), fun _ hq => Nat.sInf_le hq⟩

end Toffoli
