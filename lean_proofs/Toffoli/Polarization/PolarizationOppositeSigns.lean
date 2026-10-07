import Toffoli.Polarization.PolarizationModel
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Toffoli

/-- Reversing every sign leaves a degree-n Fischer term unchanged. -/
theorem polarization_opposite_signs {K : Type*} [CommRing K]
    (n : ℕ) (x : Fin n → K) (word : Fin n → Bool) :
    polarizationWeight (fun i => !(word i)) *
        (polarizationSum x (fun i => !(word i))) ^ n =
      polarizationWeight word * (polarizationSum x word) ^ n := by
  have hs (b : Bool) : (polarizationSign (!b) : K) = -polarizationSign b := by
    cases b <;> simp [polarizationSign]
  have hw : (polarizationWeight (fun i => !(word i)) : K) =
      (-1 : K) ^ n * polarizationWeight word := by
    simp [polarizationWeight, hs, Finset.prod_neg]
  have hx : polarizationSum x (fun i => !(word i)) = -polarizationSum x word := by
    simp [polarizationSum, hs, Finset.sum_neg_distrib]
  rw [hw, hx, neg_pow (polarizationSum x word) n, mul_mul_mul_comm, ← mul_pow]
  simp

end Toffoli
