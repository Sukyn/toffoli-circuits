import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic.Ring

namespace Toffoli

/-- Split N objects into m positive groups whose sizes differ by at most one.
There are N mod m larger groups; every group is bounded by ceil(N/m). -/
theorem balanced_composition {N m : ℕ} (hm : 0 < m) (hN : m ≤ N) :
    ∃ c : Composition N, c.length = m ∧
      ∀ j, c.blocksFun j ≤ (N + m - 1) / m := by
  let q := N / m
  let r := N % m
  have hq : 0 < q := Nat.div_pos hN hm
  have hr : r < m := Nat.mod_lt N hm
  have hdivision : q * m + r = N := Nat.div_add_mod' N m
  -- Give one extra object to the first r groups.
  let blocks := List.replicate r (q + 1) ++ List.replicate (m - r) q
  -- Both replicated lists contain only positive entries, q+1 or q.
  have hpositive : ∀ a ∈ blocks, 0 < a := by
    simp only [blocks, List.forall_mem_append, List.forall_mem_replicate]
    exact ⟨Or.inr (Nat.succ_pos q), Or.inr hq⟩
  have hsum : blocks.sum = N := by
    simp only [blocks, List.sum_append, List.sum_replicate_nat]
    calc
      r * (q + 1) + (m - r) * q = q * (r + (m - r)) + r := by ring
      _ = q * m + r := by rw [Nat.add_sub_of_le hr.le]
      _ = N := hdivision
  let c : Composition N := ⟨blocks, fun {a} ha => hpositive a ha, hsum⟩
  refine ⟨c, ?_, ?_⟩
  · change blocks.length = m
    simpa only [blocks, List.length_append, List.length_replicate] using
      Nat.add_sub_of_le hr.le
  · intro j
    have hj : c.blocksFun j ∈ blocks := c.blocksFun_mem_blocks j
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨hrne, hblock⟩ := List.mem_replicate.mp hj
      rw [hblock, Nat.le_div_iff_mul_le hm, Nat.add_mul, Nat.one_mul]
      omega
    · rw [List.eq_of_mem_replicate hj]
      exact Nat.div_le_div_right (show N ≤ N + m - 1 by omega)

end Toffoli
