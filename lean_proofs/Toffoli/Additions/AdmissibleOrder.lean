import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Basic

namespace Toffoli

/-- The least positive divisor of n which does not divide the degree d.
The hypotheses ensure n itself is a candidate. In the paper n=p-1. -/
def leastAdmissibleOrder (n d : ℕ) (hd : 0 < d) (hbound : d < n) : ℕ :=
  Nat.find (show ∃ r : ℕ, 0 < r ∧ r ∣ n ∧ ¬r ∣ d from
    ⟨n, lt_trans hd hbound, Nat.dvd_refl n, Nat.not_dvd_of_pos_of_lt hd hbound⟩)

/-- The chosen order is admissible, and no other admissible order is smaller. -/
theorem least_admissible_order_spec (n d : ℕ) (hd : 0 < d) (hbound : d < n) :
    let r := leastAdmissibleOrder n d hd hbound
    (0 < r ∧ r ∣ n ∧ ¬r ∣ d) ∧
      ∀ s : ℕ, 0 < s → s ∣ n → ¬s ∣ d → r ≤ s := by
  unfold leastAdmissibleOrder
  exact ⟨Nat.find_spec (p := fun r => 0 < r ∧ r ∣ n ∧ ¬r ∣ d) _,
    fun s hs hn hsd => Nat.find_min' _ ⟨hs, hn, hsd⟩⟩

end Toffoli
