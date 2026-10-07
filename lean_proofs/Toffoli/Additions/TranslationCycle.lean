import Toffoli.Additions.PowerCycleModel
import Mathlib.Algebra.Field.ZMod

namespace Toffoli

/-- Over a prime field, a nonzero translation visits every field element.
From x to y, take the natural representative of (y-x)/b steps. -/
theorem translation_cycle {p : ℕ} [Fact p.Prime] (b : ZMod p) (hb : b ≠ 0) :
    (affineControl 1 b one_ne_zero).IsCycleOn Set.univ := by
  have hp : ∀ (n : ℕ) (x : ZMod p),
      ((affineControl 1 b one_ne_zero) ^ n) x = x + n * b := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      have hx : affineControl 1 b one_ne_zero x = x + b := by
        simp [affineControl]
      rw [hx, Nat.cast_add, Nat.cast_one]
      ring
  refine ⟨(affineControl 1 b one_ne_zero).bijective.bijOn_univ, ?_⟩
  intro x _ y _
  refine ⟨(((y - x) / b).val : ℤ), ?_⟩
  rw [zpow_natCast, hp, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hb]
  ring

end Toffoli
