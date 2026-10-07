import Toffoli.Additions.CycleTransfers
import Toffoli.Additions.CyclePermutationModel

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- The prefix-sum transfers realize every required increment on their cycle.
The control follows the ordered cycle; inputs outside it are unchanged. -/
theorem cycleTransfers_correct (a : K) (labels : List K) (f : K → K)
    (hn : (a :: labels).Nodup) (hs : ((a :: labels).map f).sum = 0) (x t : K) :
    (cycleTransfers a labels f).eval (x, t) =
      (cyclePermutation a labels x, t + if x ∈ a :: labels then f x else 0) := by
  classical
  induction labels generalizing f x t with
  | nil =>
    have ha : f a = 0 := by simpa using hs
    by_cases hx : x = a
    · subst x
      simp [cycleTransfers, cyclePermutation, Circuit.eval, ha]
    · simp [cycleTransfers, cyclePermutation, Circuit.eval, hx]
  | cons b rest ih =>
    have ha : a ∉ b :: rest := (List.nodup_cons.mp hn).1
    have hb : b ∉ rest := (List.nodup_cons.mp hn.of_cons).1
    have hab : a ≠ b := fun h => ha (by simp [h])
    have hn' : (a :: rest).Nodup := hn.sublist (by simp)
    let g := Function.update f a (f a + f b)
    have hmap : rest.map g = rest.map f := by
      apply List.map_congr_left
      intro y hy
      have hya : y ≠ a := fun h => ha (by simp [← h, hy])
      simp [g, hya]
    have hs' : ((a :: rest).map g).sum = 0 := by
      simp only [List.map_cons, List.sum_cons]
      rw [show g a = f a + f b by simp [g], hmap]
      simpa [add_assoc] using hs
    have hb' : b ∉ a :: rest := by simp [hab.symm, hb]
    simp only [cycleTransfers, Circuit.eval, List.foldl_append]
    change (cycleTransfers a rest g).eval
      ((cycleTransferBlock a b (-f a)).eval (x, t)) = _
    rw [(cycleTransferBlock_spec a b (-f a) hab x t).1, ih g hn' hs']
    simp only [cyclePermutation, Equiv.Perm.mul_apply]
    congr 1
    by_cases hxa : x = a
    · subst x
      simp [transferIncrement, hb']
    · by_cases hxb : x = b
      · subst x
        simp [transferIncrement, hab.symm, g]
      · simp [Equiv.swap_apply_def, hxa, hxb, transferIncrement, g]

end Toffoli
