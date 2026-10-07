import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace Toffoli
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Choose the starting label of a nontrivial cycle. Fixed points are added
separately, because Mathlib's `IsCycle` excludes singleton cycles. -/
noncomputable def cycleLabels (σ : Equiv.Perm α) : List α :=
  by
    classical
    exact if h : σ.IsCycle then σ.toList (Classical.choose h) else []

/-- The chosen list contains each moved point once, in permutation order. -/
theorem cycleLabels_spec (σ : Equiv.Perm α) (h : σ.IsCycle) :
    (cycleLabels σ).Nodup ∧ cycleLabels σ ≠ [] ∧
    (cycleLabels σ).formPerm = σ ∧
    (∀ x, x ∈ cycleLabels σ ↔ x ∈ σ.support) := by
  classical
  have hx : σ (Classical.choose h) ≠ Classical.choose h :=
    (Classical.choose_spec h).1
  simp only [cycleLabels, dif_pos h]
  refine ⟨Equiv.Perm.nodup_toList _ _, ?_, ?_, ?_⟩
  · simpa [Equiv.Perm.toList_eq_nil_iff, Equiv.Perm.mem_support] using hx
  · rw [Equiv.Perm.formPerm_toList, h.cycleOf_eq hx]
  · intro x
    -- In a single cycle, sharing the chosen point's orbit means being moved.
    rw [Equiv.Perm.mem_toList_iff, (Equiv.Perm.isCycle_iff_sameCycle hx).mp h]
    simp [Equiv.Perm.mem_support, hx]

end Toffoli
