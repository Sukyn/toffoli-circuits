import Toffoli.Mixed.IndexedLadderTraceModel
import Toffoli.Mixed.MixedLadderCostSplit

namespace Toffoli

private theorem indexed_pass_trace_cost {K : Type*} [One K] [Neg K]
    (m : ℕ) (μ : K) (q : Fin (m + 1) → ℕ) :
    ((indexedPassTrace m μ).map (fun call => q call.1)).sum =
      2 * (∑ j : Fin m, q j.castSucc) + q (Fin.last m) := by
  induction m with
  | zero => simp [indexedPassTrace]
  | succ m ih =>
    simp only [indexedPassTrace, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, List.map_map, Function.comp_def]
    rw [ih (fun j => q j.succ), Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last, Nat.succ_eq_add_one]
    omega

/-- The signed trace calls both endpoint stages twice and each middle stage
four times. The coefficient changes do not change these multiplicities. -/
theorem indexed_ladder_trace_cost {K : Type*} [One K] [Neg K]
    (m : ℕ) (μ : K) (q : Fin (m + 2) → ℕ) :
    ((indexedLadderTrace m μ).map (fun call => q call.1)).sum =
      ∑ j, (if j.val = 0 ∨ j.val + 1 = m + 2 then 2 else 4) * q j := by
  rw [mixed_ladder_cost_split]
  simp only [indexedLadderTrace, List.map_append, List.sum_append,
    List.map_map, Function.comp_def]
  rw [indexed_pass_trace_cost (m + 1) μ q,
    indexed_pass_trace_cost m (-μ) (fun j => q j.succ), Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last, Nat.succ_eq_add_one]
  omega

end Toffoli
