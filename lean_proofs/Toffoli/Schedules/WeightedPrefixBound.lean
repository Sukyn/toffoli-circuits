import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Toffoli

/-- Summation by parts turns the prefix bounds into a weighted bound for
nonincreasing costs. Counts and costs may be zero. -/
theorem weighted_prefix_bound (n : ℕ) (cost actual required : ℕ → ℕ)
    (hcost : ∀ i, i + 1 < n → cost (i + 1) ≤ cost i)
    (hprefix : ∀ j, j ≤ n →
      (∑ i ∈ Finset.range j, required i) ≤ ∑ i ∈ Finset.range j, actual i) :
    (∑ i ∈ Finset.range n, cost i * required i) ≤
      ∑ i ∈ Finset.range n, cost i * actual i := by
  have hp (j : ℕ) (hj : j ≤ n) :
      (∑ i ∈ Finset.range j, (required i : ℤ)) ≤
        ∑ i ∈ Finset.range j, (actual i : ℤ) := by
    simpa only [Nat.cast_sum] using (Int.ofNat_le.mpr (hprefix j hj))
  have parts (counts : ℕ → ℕ) :=
    Finset.sum_range_by_parts (fun i => (cost i : ℤ)) (fun i => (counts i : ℤ)) n
  simp only [smul_eq_mul] at parts
  apply Int.ofNat_le.mp
  simp only [Nat.cast_sum, Nat.cast_mul]
  rw [parts required, parts actual]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hp n le_rfl) (Int.natCast_nonneg _)
  · apply Finset.sum_le_sum
    intro j hj
    have hjn : j + 1 < n := Nat.add_lt_of_lt_sub (Finset.mem_range.mp hj)
    have hd : (cost (j + 1) : ℤ) - (cost j : ℤ) ≤ 0 :=
      sub_nonpos.mpr (Int.ofNat_le.mpr (hcost j hjn))
    exact mul_le_mul_of_nonpos_left (hp (j + 1) hjn.le) hd

end Toffoli
