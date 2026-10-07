import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Group.End

namespace Toffoli

/-- Iterating multiplication multiplies by the corresponding power. -/
theorem multiplier_pow_apply {K : Type*} [GroupWithZero K] (a : Kˣ) (n : ℕ) (x : K) :
    ((Equiv.mulLeft₀ (a : K) a.ne_zero) ^ n) x = (a : K) ^ n * x := by
  rw [Equiv.Perm.coe_pow]
  exact mul_left_iterate_apply _ _

end Toffoli
