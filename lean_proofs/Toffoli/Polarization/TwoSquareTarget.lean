import Toffoli.Foundations.MultiCircuitEvalAppend
import Toffoli.Foundations.CoordinateShearEval
import Toffoli.Polarization.TwoSquareModel

namespace Toffoli

/-- The two-square trace is a scaled Toffoli on the final target.
All control coordinates, including unused dirty registers, are restored. -/
theorem two_square_target {K : Type*} [Field K] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (μ : K) (h4 : (4 : K) ≠ 0)
    (positive negative : MultiCircuit K n)
    (hp : positive.Realizes (fun x => (μ / 4) * x i ^ 2))
    (hn : negative.Realizes (fun x => -(μ / 4) * x i ^ 2)) :
    (twoSquareCircuit i j hij positive negative).Realizes (fun x => μ * x i * x j) := by
  unfold MultiCircuit.Realizes at hp hn
  intro x t
  simp only [twoSquareCircuit, multi_circuit_eval_append, coordinate_shear_eval, hp, hn]
  apply Prod.ext
  -- The preparation amounts x_j, -2*x_j, x_j sum to zero.
  · simp [hij.symm]
    ring
  · simp [hij.symm]
    field_simp [h4]
    ring

end Toffoli
