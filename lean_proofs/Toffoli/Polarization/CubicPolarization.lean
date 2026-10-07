import Toffoli.Foundations.Basic

namespace Toffoli
/-- The four signed cubes in reflected Gray order (`eq:gray-cubic-polarization`). -/
theorem cubic_polarization {K : Type*} [Field K] (x y z : K)
    (h24 : (24 : K) ≠ 0) :
    ((x + y + z) ^ 3 - (x + y - z) ^ 3 +
      (x - y - z) ^ 3 - (x - y + z) ^ 3) / 24 = x * y * z := by
  apply (div_eq_iff h24).2
  ring
end Toffoli
