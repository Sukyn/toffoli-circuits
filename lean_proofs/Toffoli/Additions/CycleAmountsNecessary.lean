import Toffoli.Additions.CycleAmountsFamilyOnCycle
import Toffoli.Additions.CycleAmountsZeroSum

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- If any choices of transfer amounts realize f, f must sum to zero on
 each listed cycle. The final affine inverse changes only the control. -/
theorem cycle_synthesis_zero_sum_necessary (a b : K) (ha : a ≠ 0)
    (cycles : List (List K)) (amounts f : K → K)
    (hn : cycles.flatten.Nodup)
    (hrealizes : (cycleSynthesisWithAmounts a b ha cycles amounts).Realizes f)
    (labels : List K) (hc : labels ∈ cycles) : (labels.map f).sum = 0 := by
  cases labels with
  | nil => simp
  | cons v rest =>
    have hn' : (v :: rest).Nodup := hn.sublist (List.sublist_flatten_of_mem hc)
    have heq : (v :: rest).map f =
        (v :: rest).map (cycleAmountsIncrement v rest amounts) := by
      apply List.map_congr_left
      intro x hx
      have h := congrArg Prod.snd (hrealizes x 0)
      simp only [cycleSynthesisWithAmounts, Circuit.eval, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at h
      change ((cycleFamilyWithAmounts cycles amounts).eval (x, 0)).2 = 0 + f x at h
      rw [cycleFamilyWithAmounts_on_cycle cycles amounts hn (v :: rest) hc x 0 hx,
        cycleWithAmounts,
        cycleTransfersWithAmounts_correct v rest amounts (List.nodup_cons.mp hn').1] at h
      simpa using h.symm
    rw [heq]
    exact cycleAmountsIncrement_sum v rest amounts hn'

end Toffoli
