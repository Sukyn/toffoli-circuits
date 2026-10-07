import Toffoli.Additions.PowerCycleModel

namespace Toffoli

/-- A nonzero scaled power can vanish at a fixed point only when that point
is zero. A singleton cycle already supplies the obstruction. -/
theorem power_cycle_fixed_point {K : Type*} [Field K]
    (a b μ : K) (ha : a ≠ 0) (d : ℕ) (hμ : μ ≠ 0)
    (hadm : PowerCycleAdmissible a b μ ha d) (x : K) (hfix : a * x + b = x) :
    x = 0 := by
  classical
  have hC : (affineControl a b ha).IsCycleOn (({x} : Finset K) : Set K) := by
    rw [Finset.coe_singleton, Equiv.Perm.isCycleOn_singleton]
    simpa [affineControl] using hfix
  have hz := hadm {x} hC
  simp only [Finset.sum_singleton] at hz
  have hpower : x ^ d = 0 := (mul_eq_zero.mp hz).resolve_left hμ
  exact eq_zero_of_pow_eq_zero hpower

end Toffoli
