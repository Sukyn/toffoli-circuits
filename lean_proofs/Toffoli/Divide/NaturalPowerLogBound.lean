import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Toffoli

/-- The weighted size of a complete recursion level is bounded by the
corresponding real power of the input size. The integer logarithm chooses
the last level whose q-power still fits below d. -/
theorem natural_power_log_bound {q w d : ℕ} (hq : 2 ≤ q) (hw : 1 ≤ w)
    (hd : 1 ≤ d) :
    ((w ^ Nat.log q d : ℕ) : ℝ) ≤
      (d : ℝ) ^ Real.logb (q : ℝ) (w : ℝ) := by
  have hqReal : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hwReal : 1 ≤ (w : ℝ) := by exact_mod_cast hw
  have hqpos : 0 < (q : ℝ) := zero_lt_one.trans hqReal
  have hlevel : (q : ℝ) ^ Nat.log q d ≤ (d : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self q (show d ≠ 0 by omega)
  have hexponent : 0 ≤ Real.logb (q : ℝ) (w : ℝ) :=
    Real.logb_nonneg hqReal hwReal
  -- Raising q^h to log_q(w) gives w^h; the exponent preserves the bound q^h ≤ d.
  calc
    ((w ^ Nat.log q d : ℕ) : ℝ) =
        ((q : ℝ) ^ Nat.log q d) ^ Real.logb (q : ℝ) (w : ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_pow_comm hqpos.le,
        Real.rpow_logb hqpos hqReal.ne' (zero_lt_one.trans_le hwReal)]
    _ ≤ (d : ℝ) ^ Real.logb (q : ℝ) (w : ℝ) :=
      Real.rpow_le_rpow (pow_nonneg hqpos.le _) hlevel hexponent

end Toffoli
