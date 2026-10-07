import Toffoli.Additions.PowerCycles
import Mathlib.GroupTheory.OrderOfElement

/-! The multiplier order test used by the Python construction. Combine
`power_cycles` with the equivalence between `a ^ d = 1` and `orderOf a ∣ d`.
-/
namespace Toffoli

open scoped BigOperators

/-- The cycle sum vanishes whenever the multiplier's order does not divide
the power. This supplies the sufficient direction of the admissibility test
in `prop:optimal-power-cycles`; it makes no optimality claim. -/
theorem power_cycles_by_order {K : Type*} [Field K] (a : Kˣ) (μ : K) (d : ℕ)
    (horder : ¬orderOf a ∣ d) (C : Finset K)
    (hC : (Equiv.mulLeft₀ (a : K) a.ne_zero).IsCycleOn (C : Set K)) :
    ∑ c ∈ C, μ * c ^ d = 0 := by
  apply power_cycles (a : K) μ d a.ne_zero _ C hC
  -- The field power is one exactly when the unit's order divides the degree.
  intro hpower
  exact horder (orderOf_dvd_iff_pow_eq_one.mpr (Units.ext hpower))

end Toffoli
