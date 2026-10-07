import Toffoli.Borrow.BorrowProductTrace
import Toffoli.Foundations.CoordinateShearEval
import Toffoli.Borrow.BorrowCubicModel

namespace Toffoli

/-- The two square differences restore both temporary controls. The three
internal calls and four target calls are the only sources of cost. -/
theorem borrow_cubic_trace {K : Type*} [Field K] {n : ℕ}
    (i j y : Fin n) (hij : i ≠ j) (hiy : i ≠ y) (hjy : j ≠ y)
    (μ : K) (h4 : (4 : K) ≠ 0)
    (prepare middle positive negative : MultiCircuit K n)
    (hprepare : ∀ x t, prepare.eval (x, t) =
      (Function.update x y (x y + x i * x j), t))
    (hmiddle : ∀ x t, middle.eval (x, t) =
      (Function.update x y (x y + (-2) * x i * x j), t))
    (hpositive : positive.Realizes (fun x => (μ / 4) * x y * x i))
    (hnegative : negative.Realizes (fun x => -(μ / 4) * x y * x i)) :
    (borrowCubicCircuit i y hiy prepare middle positive negative).Realizes
      (fun x => μ * x i * x j * x y) ∧
    (borrowCubicCircuit i y hiy prepare middle positive negative).cost =
      2 * prepare.cost + middle.cost + 2 * positive.cost + 2 * negative.cost := by
  -- The cubic case is Borrow with F = {i, j}, G = {y}, and z = i.
  -- Preparing the singleton group G is just adding y to the borrowed wire i.
  let shear (a : K) : MultiCircuit K n :=
    [.affine (coordinateShear y i a hiy.symm)]
  have shear_cost (a : K) : (shear a).cost = 0 := rfl
  have hborrow := borrow_product_trace {i, j} {y}
    (by simp [Finset.disjoint_left, hiy, hjy])
    y i (by simp) (by simp) μ h4
    prepare middle (shear 1) (shear (-1)) positive negative
    (by simpa [hij] using hprepare)
    (by simpa [hij, mul_assoc] using hmiddle)
    (by
      intro x t
      simpa [shear] using coordinate_shear_eval y i (1 : K) hiy.symm x t)
    (by
      intro x t
      simpa [shear, sub_eq_add_neg] using
        coordinate_shear_eval y i (-1 : K) hiy.symm x t)
    hpositive hnegative
  -- Both definitions list exactly the same eleven calls.
  have htrace :
      borrowProductCircuit prepare middle (shear 1) (shear (-1)) positive negative =
        borrowCubicCircuit i y hiy prepare middle positive negative := by
    simp [borrowProductCircuit, borrowProductSquareCircuit, borrowCubicCircuit,
      shear, List.append_assoc]
  simpa only [htrace, Finset.prod_pair hij, Finset.prod_singleton, shear_cost,
    mul_zero, add_zero, mul_assoc] using hborrow

end Toffoli
