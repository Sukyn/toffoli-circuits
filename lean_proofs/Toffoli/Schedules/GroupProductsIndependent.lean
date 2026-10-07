import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace Toffoli
open scoped BigOperators

/-- Disjoint nonempty control groups have independently observable coefficients.
Set every wire in group `i` to one and every other wire to zero: its product
is one, while every other group contains a zero factor. For example, the
groups `{0, 1}` and `{2}` can be isolated by inputs `(1, 1, 0)` and `(0, 0, 1)`.
Thus equality of the resulting functions determines every coefficient. -/
theorem group_products_independent {K I W : Type*} [CommSemiring K] [Fintype I]
    (groups : I → Finset W)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hnonempty : ∀ i, (groups i).Nonempty) :
    Function.Injective (fun coefficients : I → K => fun x : W → K =>
      ∑ i, coefficients i * ∏ j ∈ groups i, x j) := by
  classical
  intro a b hab
  funext i
  let x : W → K := fun j => if j ∈ groups i then 1 else 0
  have heval (coefficients : I → K) :
      (∑ j, coefficients j * ∏ w ∈ groups j, x w) = coefficients i := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.prod_eq_one (fun j hj => by simp [x, hj]), mul_one]
    · intro j _ hji
      obtain ⟨w, hw⟩ := hnonempty j
      have hwi : w ∉ groups i := Finset.disjoint_left.mp (hdisjoint hji) hw
      rw [Finset.prod_eq_zero hw (by simp [x, hwi]), mul_zero]
    · simp
  -- Evaluate both functions at x to isolate coefficient i on each side.
  simpa only [heval] using congrFun hab x

end Toffoli
