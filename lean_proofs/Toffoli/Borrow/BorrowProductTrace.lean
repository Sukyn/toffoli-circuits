import Toffoli.Borrow.BorrowProductSquare
import Mathlib.Data.Finset.Disjoint

namespace Toffoli

/-- Borrow on two disjoint groups, with actual circuits for all preparations.
At call boundaries only `y` and `z` may have changed. Both are restored, and the eleven-call
trace has three `F` preparations, four `G` preparations, and four Toffolis. -/
theorem borrow_product_trace {K : Type*} [Field K] {n : ℕ}
    (F G : Finset (Fin n)) (hFG : Disjoint F G)
    (y z : Fin n) (hy : y ∈ G) (hz : z ∈ F) (μ : K) (h4 : (4 : K) ≠ 0)
    (prepareF middleF prepareG undoG positive negative : MultiCircuit K n)
    (hprepareF : ∀ x t, prepareF.eval (x, t) =
      (Function.update x y (x y + ∏ j ∈ F, x j), t))
    (hmiddleF : ∀ x t, middleF.eval (x, t) =
      (Function.update x y (x y + (-2) * ∏ j ∈ F, x j), t))
    (hprepareG : ∀ x t, prepareG.eval (x, t) =
      (Function.update x z (x z + ∏ j ∈ G, x j), t))
    (hundoG : ∀ x t, undoG.eval (x, t) =
      (Function.update x z (x z - ∏ j ∈ G, x j), t))
    (hpositive : positive.Realizes (fun x => (μ / 4) * x y * x z))
    (hnegative : negative.Realizes (fun x => -(μ / 4) * x y * x z)) :
    (borrowProductCircuit prepareF middleF prepareG undoG positive negative).Realizes
      (fun x => μ * (∏ j ∈ F, x j) * ∏ j ∈ G, x j) ∧
    (borrowProductCircuit prepareF middleF prepareG undoG positive negative).cost =
      2 * prepareF.cost + middleF.cost + 2 * prepareG.cost + 2 * undoG.cost +
        2 * positive.cost + 2 * negative.cost := by
  have hyF : y ∉ F := Finset.disjoint_right.mp hFG hy
  have hzG : z ∉ G := Finset.disjoint_left.mp hFG hz
  have hyz : y ≠ z := fun h => hzG (h ▸ hy)
  have hplus := (borrow_product_square G y z hyz hzG (μ / 4)
    prepareG undoG positive negative hprepareG hundoG hpositive hnegative).1
  have hminus := (borrow_product_square G y z hyz hzG (-(μ / 4))
    prepareG undoG negative positive hprepareG hundoG hnegative
      (by simpa only [neg_neg] using hpositive)).1
  unfold MultiCircuit.Realizes at hplus hminus
  have productG_factor (x : Controls K n) (a : K) :
      (∏ j ∈ G, Function.update x y a j) = a * ∏ j ∈ G.erase y, x j := by
    simpa only [Finset.sdiff_singleton_eq_erase] using Finset.prod_update_of_mem hy x a
  constructor
  · intro x t
    simp only [borrowProductCircuit, multi_circuit_eval_append,
      hprepareF, hmiddleF, hplus, hminus]
    apply Prod.ext
    -- The three preparations change y by F, -2F, and F, hence restore it.
    · simp [Finset.prod_update_of_notMem hyF]
      ring
    -- With H = product (G.erase y), the target receives
    -- μ/4 * ((y + F)^2 - (y - F)^2) * H = μ * F * y * H.
    · simp [Finset.prod_update_of_notMem hyF, productG_factor]
      rw [← Finset.mul_prod_erase G x hy]
      field_simp [h4]
      ring
  · simp only [borrowProductCircuit, borrowProductSquareCircuit, multi_circuit_cost_append]
    omega

end Toffoli
