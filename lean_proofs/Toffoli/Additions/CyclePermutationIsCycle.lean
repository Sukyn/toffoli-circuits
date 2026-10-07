import Toffoli.Additions.CyclePermutationFormPerm
import Mathlib.GroupTheory.Perm.Cycle.Basic

namespace Toffoli

/-- Distinct entries give one cycle, including the one-point case. -/
theorem cycle_permutation_isCycleOn {K : Type*} [DecidableEq K]
    (a : K) (labels : List K) (hn : (a :: labels).Nodup) :
    (cyclePermutation a labels).IsCycleOn {x | x ∈ a :: labels} := by
  rw [cycle_permutation_eq_formPerm a labels hn]
  exact hn.isCycleOn_formPerm

end Toffoli
