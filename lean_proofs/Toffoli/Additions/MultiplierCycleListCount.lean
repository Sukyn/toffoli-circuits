import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.BigOperators.Ring.List
import Toffoli.Additions.MultiplierCycleCard

namespace Toffoli

/-- A disjoint covering list has one zero cycle and (card K - 1)/r other
cycles, where r is the multiplier order. Counting zero occurrences avoids
choosing an ordering for those cycles. -/
theorem multiplier_cycle_list_count {K : Type*} [GroupWithZero K] [Fintype K] [DecidableEq K]
    (a : Kˣ) (cycles : List (List K))
    (hn : cycles.flatten.Nodup) (hcover : ∀ x, x ∈ cycles.flatten)
    (hne : ∀ labels ∈ cycles, labels ≠ [])
    (hc : ∀ labels ∈ cycles,
      (Equiv.mulLeft₀ (a : K) a.ne_zero).IsCycleOn {x | x ∈ labels}) :
    cycles.length = 1 + (Fintype.card K - 1) / orderOf a := by
  let r := orderOf a
  have hr : 0 < r := orderOf_pos a
  have hbalance : ∀ labels ∈ cycles,
      labels.length + labels.count 0 * (r - 1) = r := by
    intro labels hl
    have hnodup := (List.nodup_flatten.mp hn).1 labels hl
    have hnonempty := (List.toFinset_nonempty_iff labels).mpr (hne labels hl)
    have hcard := multiplier_cycle_card a labels.toFinset hnonempty
      (by simpa using hc labels hl)
    rw [List.toFinset_card_of_nodup hnodup] at hcard
    rw [hcard, hnodup.count]
    by_cases hz : (0 : K) ∈ labels <;> simp [hz] <;> omega
  have hu : cycles.flatten.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun x => List.mem_toFinset.mpr (hcover x))
  have hlength : cycles.flatten.length = Fintype.card K := by
    rw [← List.toFinset_card_of_nodup hn, hu, Finset.card_univ]
  have hzero := List.count_eq_one_of_mem hn (hcover 0)
  have htotal := congrArg List.sum (List.map_congr_left hbalance)
  simp only [List.sum_map_add, List.sum_map_mul_right, ← List.length_flatten,
    ← List.count_flatten, List.map_const', List.sum_replicate_nat] at htotal
  rw [hlength, hzero, one_mul] at htotal
  have hlenpos : 0 < cycles.length := by
    obtain ⟨labels, hlabels, _⟩ := List.mem_flatten.mp (hcover 0)
    exact List.length_pos_of_mem hlabels
  have hmul : (cycles.length - 1) * r = Fintype.card K - 1 := by
    -- Remove the singleton zero cycle from the total count.
    calc
      _ = cycles.length * r - r := by rw [Nat.sub_mul, one_mul]
      _ = Fintype.card K - 1 := by rw [← htotal]; omega
  rw [← hmul, Nat.mul_div_cancel _ hr]
  omega

end Toffoli
