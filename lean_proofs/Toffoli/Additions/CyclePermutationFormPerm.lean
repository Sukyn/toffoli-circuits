import Toffoli.Additions.CyclePermutationModel

namespace Toffoli

/-- The anchored-swap program is the cycle whose entries are `a :: labels`.
For example, `[a,b,c]` means `a ↦ b ↦ c ↦ a`. -/
theorem cycle_permutation_eq_formPerm {K : Type*} [DecidableEq K]
    (a : K) (labels : List K) (hn : (a :: labels).Nodup) :
    cyclePermutation a labels = (a :: labels).formPerm := by
  induction labels with
  | nil => simp [cyclePermutation]
  | cons b bs ih =>
    have htail : (a :: bs).Nodup := hn.sublist (by simp)
    have hrot : (b :: (bs ++ [a])).Nodup := by
      simpa using (List.nodup_rotate.mpr hn : ((a :: b :: bs).rotate 1).Nodup)
    have hfirst := List.formPerm_rotate_one (a :: b :: bs) hn
    have hsecond := List.formPerm_rotate_one (b :: (bs ++ [a])) hrot
    have hshort := List.formPerm_rotate_one (a :: bs) htail
    simp only [List.rotate_cons_succ, List.rotate_zero, List.cons_append] at hfirst hsecond hshort
    rw [cyclePermutation, ih htail, ← hfirst, ← hsecond]
    simpa [List.append_assoc, List.formPerm_append_pair] using
      congrArg (fun p => p * Equiv.swap a b) hshort.symm

end Toffoli
