import Mathlib.GroupTheory.Perm.Cycle.Type

namespace Toffoli

/-- Relabelling states transports the support bijectively, so a permutation
moving exactly three states remains a three-cycle. -/
theorem is_three_cycle_perm_congr {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) {σ : Equiv.Perm X}
    (hσ : σ.IsThreeCycle) : (e.permCongr σ).IsThreeCycle := by
  have hs : (e.permCongr σ).support = σ.support.map e.toEmbedding := by
    ext y
    simp only [Finset.mem_map_equiv, Equiv.Perm.mem_support, Equiv.permCongr_apply,
      ne_eq, Equiv.apply_eq_iff_eq_symm_apply]
  apply card_support_eq_three_iff.mp
  rw [hs, Finset.card_map, hσ.card_support]

end Toffoli
