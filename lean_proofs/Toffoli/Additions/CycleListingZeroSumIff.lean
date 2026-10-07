import Toffoli.Additions.CycleListingComplete
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Toffoli
variable {α M : Type*} [DecidableEq α] [AddCommMonoid M]

/-- Summing on the chosen lists is equivalent to summing on every actual
cycle of the permutation. The empty set contributes zero automatically. -/
theorem cycle_listing_zero_sum_iff (σ : Equiv.Perm α) (cycles : List (List α))
    (hn : cycles.flatten.Nodup) (hcover : ∀ x, x ∈ cycles.flatten)
    (hc : ∀ labels ∈ cycles, σ.IsCycleOn {x | x ∈ labels}) (f : α → M) :
    (∀ labels ∈ cycles, (labels.map f).sum = 0) ↔
      (∀ C : Finset α, σ.IsCycleOn (C : Set α) → ∑ x ∈ C, f x = 0) := by
  constructor
  · intro hs C hC
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨labels, hl, rfl⟩ :=
        cycle_listing_complete σ cycles hcover hc C hC hne
      rw [List.sum_toFinset f ((List.nodup_flatten.mp hn).1 labels hl)]
      exact hs labels hl
  · intro hs labels hl
    rw [← List.sum_toFinset f ((List.nodup_flatten.mp hn).1 labels hl)]
    apply hs
    simpa using hc labels hl

end Toffoli
