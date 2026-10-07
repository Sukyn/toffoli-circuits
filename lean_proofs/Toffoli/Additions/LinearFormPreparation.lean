import Toffoli.Foundations.MultiControlModel
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Toffoli
open scoped BigOperators

/-- A nonzero coefficient lets its wire hold the whole linear form.
All other wires stay unchanged. Their values determine every other summand,
so the nonzero coefficient also makes the original wire recoverable.
Mathlib turns this injective linear map into an affine equivalence. -/
theorem linear_form_preparation {K : Type*} [Field K] {n : ℕ}
    (b : Fin n → K) (i : Fin n) (hi : b i ≠ 0) :
    ∃ e : Controls K n ≃ᵃ[K] Controls K n,
      (∀ x, e x i = ∑ j, b j * x j) ∧
      (∀ x j, j ≠ i → e x j = x j) := by
  let L : Controls K n →ₗ[K] K := ∑ j, b j • LinearMap.proj j
  let T : Controls K n →ₗ[K] Controls K n :=
    LinearMap.pi (Function.update (fun j => LinearMap.proj j) i L)
  have hinjective : Function.Injective T := (injective_iff_map_eq_zero T).2 fun x hx => by
    have hother (j : Fin n) (hj : j ≠ i) : x j = 0 := by
      simpa [T, hj] using congrFun hx j
    have hsum : (∑ j, b j * x j) = 0 := by
      simpa [T, L] using congrFun hx i
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hother j hj, mul_zero])
      (by simp)] at hsum
    have hxi := (mul_eq_zero.mp hsum).resolve_left hi
    funext j
    by_cases hj : j = i
    · simpa [hj] using hxi
    · exact hother j hj
  refine ⟨(LinearEquiv.ofInjectiveEndo T hinjective).toAffineEquiv, ?_, ?_⟩
  · intro x
    simp [T, L]
  · intro x j hj
    simp [T, hj]

end Toffoli
