import Toffoli.Additions.CycleAmountsOutside

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- Arbitrary amounts telescope to zero on the cycle, including singletons. -/
theorem cycleAmountsIncrement_sum (a : K) (labels : List K)
    (amounts : K → K) (hn : (a :: labels).Nodup) :
    ((a :: labels).map (cycleAmountsIncrement a labels amounts)).sum = 0 := by
  induction labels with
  | nil => simp [cycleAmountsIncrement]
  | cons b rest ih =>
    have ha : a ∉ b :: rest := (List.nodup_cons.mp hn).1
    have hb : b ∉ rest := (List.nodup_cons.mp hn.of_cons).1
    have hab : a ≠ b := fun h => ha (by simp [h])
    have hn' : (a :: rest).Nodup := hn.sublist (by simp)
    have hb' : b ∉ a :: rest := by simp [hab.symm, hb]
    have hmap : rest.map (cycleAmountsIncrement a (b :: rest) amounts) =
        rest.map (cycleAmountsIncrement a rest amounts) := by
      apply List.map_congr_left
      intro x hx
      have hxa : x ≠ a := fun h => ha (by simp [← h, hx])
      have hxb : x ≠ b := fun h => hb (h ▸ hx)
      simp [cycleAmountsIncrement, transferIncrement, Equiv.swap_apply_def, hxa, hxb]
    have hz := ih hn'
    simp only [List.map_cons, List.sum_cons] at hz ⊢
    rw [hmap]
    simp only [cycleAmountsIncrement, transferIncrement, ite_true,
      Equiv.swap_apply_left, Equiv.swap_apply_right, if_neg hab.symm,
      cycleAmountsIncrement_outside a rest amounts b hb', add_zero]
    convert hz using 1; ring

end Toffoli
