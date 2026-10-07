import Mathlib.FieldTheory.Finite.Basic

namespace Toffoli

/-- In the reduced degree range, only the highest power has nonzero sum.
For example, over `ZMod 5`, the sums for exponents `0,1,2,3,4` are
`0,0,0,0,-1`. The constant sum is zero because the field has characteristic
dividing its cardinality. -/
theorem finite_field_power_sum {K : Type*} [Field K] [Fintype K]
    (d : ℕ) (hd : d ≤ Fintype.card K - 1) :
    ∑ x : K, x ^ d = if d = Fintype.card K - 1 then -1 else 0 := by
  classical
  by_cases htop : d = Fintype.card K - 1
  · rw [if_pos htop, htop]
    have hpositive : Fintype.card K - 1 ≠ 0 :=
      Nat.sub_ne_zero_of_lt Fintype.one_lt_card
    calc
      ∑ x : K, x ^ (Fintype.card K - 1) =
          ∑ x : K, (1 - if x = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = 0
        · simp [hx, hpositive]
        · simp [hx, FiniteField.pow_card_sub_one_eq_one x hx]
      _ = -1 := by
        simp [Finset.sum_sub_distrib]
  · rw [if_neg htop]
    exact FiniteField.sum_pow_lt_card_sub_one K d (lt_of_le_of_ne hd htop)

end Toffoli
