import Toffoli.Polarization.PolarizationFullSum
import Toffoli.Polarization.PolarizationHalfSum

namespace Toffoli

/-- The numerator of Fischer's identity, with the first sign fixed positive.
For n = 1 this is (x+y)^2 - (x-y)^2 = 4*x*y. -/
theorem fischer_polarization {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (n : ℕ) (x : K) (factors : Fin n → K) :
    (∑ word : Fin n → Bool, polarizationWeight word *
      (x + polarizationSum factors word) ^ (n + 1)) =
      (2 : K) ^ n * ((n + 1).factorial : K) * x * ∏ i, factors i := by
  have h := polarization_full_sum (n + 1) (Fin.cons x factors)
  rw [polarization_half_sum] at h
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, pow_succ (2 : K)] at h
  -- Pairing opposite words introduced a factor 2, which is invertible here.
  apply mul_left_cancel₀ h2
  convert h using 1; ring

end Toffoli
