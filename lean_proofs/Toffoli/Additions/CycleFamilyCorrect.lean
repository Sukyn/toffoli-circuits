import Toffoli.Additions.CycleFamily
import Toffoli.Additions.CycleTransfersCorrect
import Toffoli.Additions.CyclePermutationFormPerm

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- Disjoint zero-sum cycles can be executed in any listed order. The same
primitive circuit gives both the control permutation and target increment. -/
theorem cycleFamily_correct (cycles : List (List K)) (f : K → K)
    (hn : cycles.flatten.Nodup)
    (hs : ∀ labels ∈ cycles, (labels.map f).sum = 0) (x t : K) :
    (cycleFamilyCircuit cycles f).eval (x, t) =
      (cycleFamilyPermutation cycles x,
        t + if x ∈ cycles.flatten then f x else 0) := by
  classical
  induction cycles generalizing x t with
  | nil => simp [cycleFamilyCircuit, cycleFamilyPermutation, Circuit.eval]
  | cons labels rest ih =>
    obtain ⟨hfirstSum, hrestSum⟩ := List.forall_mem_cons.mp hs
    cases labels with
    | nil =>
      simpa [cycleFamilyCircuit, cycleCircuit, cycleFamilyPermutation] using
        ih (by simpa using hn) hrestSum x t
    | cons a labels =>
      obtain ⟨hlabels, hrest, hdisjoint⟩ := List.nodup_append'.mp
        (show ((a :: labels) ++ rest.flatten).Nodup by simpa using hn)
      simp only [cycleFamilyCircuit, List.flatMap_cons, cycleCircuit,
        Circuit.eval, List.foldl_append]
      change (cycleFamilyCircuit rest f).eval
        ((cycleTransfers a labels f).eval (x, t)) = _
      rw [cycleTransfers_correct a labels f hlabels hfirstSum,
        cycle_permutation_eq_formPerm a labels hlabels, ih hrest hrestSum]
      simp only [cycleFamilyPermutation, List.map_cons, List.reverse_cons,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one, Equiv.Perm.mul_apply]
      congr 1
      by_cases hx : x ∈ a :: labels
      · have hpx : (a :: labels).formPerm x ∈ a :: labels :=
          List.formPerm_mem_iff_mem.mpr hx
        have hnot : (a :: labels).formPerm x ∉ rest.flatten :=
          List.disjoint_left.mp hdisjoint hpx
        have hall : x ∈ ((a :: labels) :: rest).flatten := by
          simp only [List.flatten_cons, List.mem_append]
          exact Or.inl hx
        simp only [if_pos hx, if_neg hnot, if_pos hall, add_zero]
      · rw [List.formPerm_apply_of_notMem hx]
        simp only [List.flatten_cons, List.mem_append, hx, false_or, if_false, add_zero]

end Toffoli
