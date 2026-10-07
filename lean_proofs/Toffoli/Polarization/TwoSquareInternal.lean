import Toffoli.Foundations.MultiCircuitEvalAppend
import Toffoli.Foundations.CoordinateShearEval
import Toffoli.Polarization.TwoSquareModel

namespace Toffoli

/-- The same trace may target a third control wire. Only that coordinate
changes; in particular the surrounding circuit's final target is excluded. -/
theorem two_square_internal {K : Type*} [Field K] {n : ℕ}
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (μ : K) (h4 : (4 : K) ≠ 0) (positive negative : MultiCircuit K n)
    (hp : ∀ x t, positive.eval (x, t) =
      (Function.update x k (x k + (μ / 4) * x i ^ 2), t))
    (hn : ∀ x t, negative.eval (x, t) =
      (Function.update x k (x k - (μ / 4) * x i ^ 2), t)) :
    ∀ x t, (twoSquareCircuit i j hij positive negative).eval (x, t) =
      (Function.update x k (x k + μ * x i * x j), t) := by
  intro x t
  simp only [twoSquareCircuit, multi_circuit_eval_append, coordinate_shear_eval, hp, hn]
  apply Prod.ext
  · funext r
    by_cases hri : r = i
    · subst r
      simp [hij.symm, hik, hik.symm, hjk]
      ring
    · by_cases hrk : r = k
      · subst r
        simp [hij.symm, hik, hik.symm, hjk]
        field_simp [h4]
        ring
      · simp [hri, hrk]
  · rfl

end Toffoli
