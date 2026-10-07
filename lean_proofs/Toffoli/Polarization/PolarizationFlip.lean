import Toffoli.Polarization.PolarizationExecutionModel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Toffoli

/-- The recorded group call changes exactly the signed term selected by Gray order. -/
theorem polarization_sum_flip {K : Type*} [CommRing K] {n : ℕ}
    (factors : Fin n → K) (word : GrayWord n) (i : Fin n) :
    polarizationSum factors (grayFlip word i) =
      polarizationSum factors word - 2 * polarizationSign (word i) * factors i := by
  have hsign : polarizationSign (!word i) = -(polarizationSign (word i) : K) := by
    cases word i <;> simp [polarizationSign]
  have hupdate : (fun j => polarizationSign (grayFlip word i j) * factors j) =
      Function.update (fun j => polarizationSign (word j) * factors j) i
        (-polarizationSign (word i) * factors i) := by
    funext j
    simpa only [grayFlip, hsign] using
      Function.apply_update (fun j b => (polarizationSign b : K) * factors j)
        word i (!(word i)) j
  unfold polarizationSum
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ i)
    (fun j => polarizationSign (word j) * factors j)]
  ring

end Toffoli
