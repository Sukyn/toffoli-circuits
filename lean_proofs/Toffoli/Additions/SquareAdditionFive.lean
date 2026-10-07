import Toffoli.Foundations.Basic
import Mathlib.Algebra.Field.ZMod

/-! The square-addition circuit shown in `fig:core-cycle-square`.
Multiplication by two has cycle `(1 2 4 3)` over `ZMod 5`. The cycle-transfer
construction uses three transpositions; adjacent SUMs have been combined.
The final multiplication by three restores the control wire.
-/
namespace Toffoli

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Eight primitive gates for adding `μ * x²` over the five-element field. -/
def squareAdditionFive (μ : ZMod 5) : Circuit (ZMod 5) :=
  [.sum (4 * μ), .swap 1 2, .sum μ, .swap 1 4,
   .sum (2 * μ), .swap 1 3, .sum (3 * μ), .affine 3 0 (by decide)]

/-- Run all five possible controls, leaving both the coefficient and target
symbolic. Every case restores the control and adds the required square;
exactly three gates are transpositions. -/
theorem square_addition_five (μ : ZMod 5) :
    (squareAdditionFive μ).Realizes (fun x => μ * x ^ 2) ∧
    (squareAdditionFive μ).cost = 3 := by
  constructor
  · intro x t
    have hx : ∀ x : ZMod 5, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
    -- The collected coefficients are 0, 16, 29, 24, 31: the five squares modulo 5.
    rcases hx x with rfl | rfl | rfl | rfl | rfl <;>
      simp +decide [squareAdditionFive, Circuit.eval, Gate.eval, Equiv.swap_apply_def] <;>
      ring_nf
    · change t + μ * 1 = t + μ
      simp
    · rfl
    · rfl
    · rfl
  · rfl

end Toffoli
