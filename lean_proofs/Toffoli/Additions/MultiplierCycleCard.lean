import Toffoli.Additions.MultiplierCyclePower
import Mathlib.GroupTheory.Perm.Cycle.Basic

namespace Toffoli

/-- Zero is a singleton cycle. Every nonzero cycle has the multiplier's order:
returning a nonzero point is equivalent to the multiplier power being one. -/
theorem multiplier_cycle_card {K : Type*} [GroupWithZero K] [DecidableEq K]
    (a : Kˣ) (C : Finset K) (hne : C.Nonempty)
    (hC : (Equiv.mulLeft₀ (a : K) a.ne_zero).IsCycleOn (C : Set K)) :
    C.card = if 0 ∈ C then 1 else orderOf a := by
  by_cases hzero : 0 ∈ C
  · rw [if_pos hzero]
    have heq : C = {0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hzero, ?_⟩
      intro y hy
      obtain ⟨n, _, h⟩ := hC.exists_pow_eq hzero hy
      simpa [multiplier_pow_apply] using h.symm
    simp [heq]
  · rw [if_neg hzero]
    obtain ⟨x, hx⟩ := hne
    have hx0 : x ≠ 0 := fun h => hzero (h ▸ hx)
    have hreturn (n : ℕ) :
        ((Equiv.mulLeft₀ (a : K) a.ne_zero) ^ n) x = x ↔ orderOf a ∣ n := by
      calc
        _ ↔ (a : K) ^ n = 1 := by rw [multiplier_pow_apply, mul_eq_right₀ hx0]
        _ ↔ a ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, Units.val_eq_one]
        _ ↔ orderOf a ∣ n := orderOf_dvd_iff_pow_eq_one.symm
    exact Nat.dvd_antisymm
      ((hC.pow_apply_eq hx).mp ((hreturn _).mpr dvd_rfl))
      ((hreturn _).mp (hC.pow_card_apply hx))

end Toffoli
