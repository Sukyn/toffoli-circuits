import Toffoli.Divide.DivideRecurrence
import Toffoli.Divide.DivideCountOne

namespace Toffoli
open scoped BigOperators

/-- Grouping three controls together and leaving the others as singletons
uses degree d-2 polarization. Only the first preparation has a nonzero cost,
and its Gray-code weight is three. -/
theorem divide_triple_grouping {p d : ℕ} (hp : 5 ≤ p) (hd : 4 ≤ d)
    (hdp : d ≤ p - 2) :
    divideCount p d ≤
      2 ^ (d - 3) * ((p - 1) - (p - 1) /
        leastAdmissibleOrder (p - 1) (d - 2) (by omega) (by omega)) +
      3 * divideCount p 3 := by
  -- The group sizes sum to d-1: three controls, followed by d-4 singletons.
  let c : Composition (d - 1) := {
    blocks := 3 :: List.replicate (d - 4) 1
    blocks_pos := by
      simp
    blocks_sum := by
      simp
      omega }
  have hlength : c.length = d - 3 := by
    simp only [Composition.length, c, List.length_cons, List.length_replicate]
    omega
  have hdegree : c.length + 1 ≤ p - 2 := by omega

  -- Separate the triple from the remaining SUM preparations, whose costs are zero.
  have hsum : (∑ j : Fin c.length, (2 + 2 ^ j.val) *
      divideCount p (c.blocksFun j)) = 3 * divideCount p 3 := by
    have split := Fin.sum_univ_succ
      (fun j : Fin ((List.replicate (d - 4) (1 : ℕ)).length + 1) =>
        (2 + 2 ^ j.val) * divideCount p (c.blocksFun j))
    simpa [Composition.blocksFun, c, List.get_eq_getElem, divide_count_one] using split

  -- The minimum in the recurrence is bounded by this explicit grouping.
  have hbound := (divide_recurrence hp (show 2 ≤ d by omega)).2 c hdegree
  simpa only [divideStepCost, hsum, hlength, show d - 3 + 1 = d - 2 by omega]
    using hbound

end Toffoli
