import Toffoli.Mixed.MixedPolarizationBound
import Toffoli.Divide.DivideRecurrence
import Toffoli.Divide.DivideCountOne

namespace Toffoli

/-- Available workspace cannot make the mixed minimum exceed Divide-and-conquer:
reuse an attaining Divide grouping, with cheaper mixed preparations. -/
theorem mixed_divide_bound {p d : ℕ} (hp : 5 ≤ p) (hd : 0 < d) (b : ℕ) :
    mixedCount p hp d b ≤ divideCount p d := by
  revert hd b
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd b
    by_cases hone : d = 1
    · simp [hone, mixed_count_one, divide_count_one]
    obtain ⟨c, hdegree, hdivide⟩ := (divide_recurrence hp (show 2 ≤ d by omega)).1
    let costs (j : Fin c.length) :=
      mixedCount p hp (c.blocksFun j) (d + b - c.blocksFun j - 1)
    have hchildren (j : Fin c.length) : costs j ≤ divideCount p (c.blocksFun j) := by
      have hsize := c.blocksFun_le j
      exact ih (c.blocksFun j) (by omega) (c.one_le_blocksFun j)
        (d + b - c.blocksFun j - 1)
    -- The mixed family admits this grouping, including the two-control base case.
    calc
      mixedCount p hp d b ≤ divideStepCost p c hdegree costs :=
        mixed_polarization_bound hp (by omega) b c hdegree
      _ ≤ divideStepCost p c hdegree (fun j => divideCount p (c.blocksFun j)) :=
        divide_step_cost_mono p c hdegree _ _ hchildren
      _ = divideCount p d := hdivide.symm

end Toffoli
