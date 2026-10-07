import Toffoli.Mixed.IndexedLadderTraceModel
import Mathlib.Algebra.GroupWithZero.Basic

namespace Toffoli

private theorem indexed_pass_trace_nonzero {K : Type*} [AddGroup K] [One K]
    [NeZero (1 : K)] (m : ℕ) {μ : K} (hμ : μ ≠ 0)
    {call : Fin (m + 1) × K} (hcall : call ∈ indexedPassTrace m μ) : call.2 ≠ 0 := by
  induction m with
  | zero =>
    have h : call = (0, μ) := by simpa only [indexedPassTrace, List.mem_singleton] using hcall
    simpa only [h] using hμ
  | succ m ih =>
    simp only [indexedPassTrace, List.mem_append, List.mem_singleton, List.mem_map, or_assoc] at hcall
    rcases hcall with rfl | ⟨child, hchild, rfl⟩ | rfl
    · exact one_ne_zero
    · exact ih hchild
    · exact neg_ne_zero.mpr one_ne_zero

/-- A nonzero parent coefficient makes every recursive call nonzero,
including both the preparation and undo occurrences. -/
theorem indexed_ladder_trace_nonzero {K : Type*} [AddGroup K] [One K]
    [NeZero (1 : K)] {m : ℕ} {μ : K} (hμ : μ ≠ 0)
    {call : Fin (m + 2) × K} (hcall : call ∈ indexedLadderTrace m μ) : call.2 ≠ 0 := by
  simp only [indexedLadderTrace, List.mem_append, List.mem_map] at hcall
  rcases hcall with hcall | ⟨child, hchild, rfl⟩
  · exact indexed_pass_trace_nonzero (m + 1) hμ hcall
  · exact indexed_pass_trace_nonzero m (neg_ne_zero.mpr hμ) hchild

end Toffoli
