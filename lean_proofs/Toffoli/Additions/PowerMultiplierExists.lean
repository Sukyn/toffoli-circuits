import Toffoli.Foundations.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Fintype.Units

/-! A multiplier for each degree in `thm:polynomial-synthesis`.
For `0 < d < Nat.card K - 1`, cyclicity of the finite field's unit group
gives a nonzero `a` with `a ^ d ≠ 1`.
-/
namespace Toffoli

/-- In a finite field, a nonzero power below the size of the unit group
cannot send every unit to one. For `K = ZMod p`, the bound is `d < p - 1`. -/
theorem power_multiplier_exists {K : Type*} [Field K] [Finite K]
    (d : ℕ) (hd : d ≠ 0) (hbound : d < Nat.card K - 1) :
    ∃ a : K, a ≠ 0 ∧ a ^ d ≠ 1 := by
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic (G := Kˣ) hd
    (by rwa [Nat.card_units])
  refine ⟨a, a.ne_zero, ?_⟩
  -- Passing from the unit to its field value preserves the power test.
  exact fun h => ha (Units.ext h)

end Toffoli
