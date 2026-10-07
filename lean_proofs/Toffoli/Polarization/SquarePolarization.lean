import Toffoli.Foundations.Basic

namespace Toffoli
/-- The two-square polarization identity, valid when 4 is invertible. -/
theorem square_polarization {K : Type*} [Field K] (x y : K) (h4 : (4 : K) ≠ 0) :
    ((x + y) ^ 2 - (x - y) ^ 2) / 4 = x * y := by
  apply (div_eq_iff h4).2
  ring
end Toffoli
