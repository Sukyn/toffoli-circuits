import Toffoli.Additions.CycleAmountsFamilyOutside
import Toffoli.Additions.CycleAmountsCorrect
import Toffoli.Additions.CyclePermutationMembership

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- On one listed cycle, every other disjoint cycle circuit is inactive. -/
theorem cycleFamilyWithAmounts_on_cycle (cycles : List (List K))
    (amounts : K → K) (hn : cycles.flatten.Nodup)
    (labels : List K) (hc : labels ∈ cycles) (x t : K) (hx : x ∈ labels) :
    (cycleFamilyWithAmounts cycles amounts).eval (x, t) =
      (cycleWithAmounts labels amounts).eval (x, t) := by
  induction cycles with
  | nil => simp at hc
  | cons first rest ih =>
    obtain ⟨hfirst, hrest, hdisjoint⟩ := List.nodup_append'.mp
      (show (first ++ rest.flatten).Nodup by simpa using hn)
    simp only [cycleFamilyWithAmounts, List.flatMap_cons, Circuit.eval, List.foldl_append]
    change (cycleFamilyWithAmounts rest amounts).eval
      ((cycleWithAmounts first amounts).eval (x, t)) =
        (cycleWithAmounts labels amounts).eval (x, t)
    rcases List.mem_cons.mp hc with heq | hc
    · subst first
      cases labels with
      | nil => simp at hx
      | cons a tail =>
        simp only [cycleWithAmounts,
          cycleTransfersWithAmounts_correct a tail amounts (List.nodup_cons.mp hfirst).1]
        have hp : cyclePermutation a tail x ∈ a :: tail :=
          (cycle_permutation_mem_iff_mem a tail x).mpr hx
        exact cycleFamilyWithAmounts_outside rest amounts _ _
          (List.disjoint_left.mp hdisjoint hp)
    · have hxr : x ∈ rest.flatten := List.mem_flatten.mpr ⟨labels, hc, hx⟩
      have hxf : x ∉ first := fun h => List.disjoint_left.mp hdisjoint h hxr
      rw [cycleWithAmounts_outside first amounts x t hxf]
      exact ih hrest hc

end Toffoli
