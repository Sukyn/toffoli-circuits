import Toffoli.Polarization.PolarizationModel
import Mathlib.Data.Bool.Basic

namespace Toffoli

/-- Distinct Boolean signs give distinct coefficients outside characteristic two. -/
theorem polarization_sign_injective {K : Type*} [CommRing K] (h2 : (2 : K) ≠ 0) :
    Function.Injective (polarizationSign : Bool → K) := by
  rw [Bool.injective_iff]
  simpa [polarizationSign, eq_neg_iff_add_eq_zero, one_add_one_eq_two] using h2

end Toffoli
