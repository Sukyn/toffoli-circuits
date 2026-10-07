import Toffoli.Polarization.PolarizationOppositeSigns
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

namespace Toffoli

/-- Pair globally opposite sign words, retaining the word whose first sign is positive. -/
theorem polarization_half_sum {K : Type*} [CommRing K]
    (n : ℕ) (x : Fin (n + 1) → K) :
    (∑ word : Fin (n + 1) → Bool,
      polarizationWeight word * (polarizationSum x word) ^ (n + 1)) =
      2 * ∑ word : Fin n → Bool, polarizationWeight word *
        (x 0 + polarizationSum (fun i => x i.succ) word) ^ (n + 1) := by
  classical
  let term (word : Fin (n + 1) → Bool) :=
    polarizationWeight word * (polarizationSum x word) ^ (n + 1)
  let flip (word : Fin n → Bool) := fun i => !(word i)
  have hflip : Function.Involutive flip := by intro word; funext i; simp [flip]
  have hpair (word : Fin n → Bool) :
      term (Fin.cons true (flip word)) = term (Fin.cons false word) := by
    simpa only [← Function.comp_def, Fin.comp_cons, Bool.not_false] using
      polarization_opposite_signs (n + 1) x (Fin.cons false word)
  have hsum : (∑ word : Fin n → Bool, term (Fin.cons true word)) =
      ∑ word : Fin n → Bool, term (Fin.cons false word) := by
    calc
      _ = ∑ word : Fin n → Bool, term (Fin.cons true (flip word)) :=
        (hflip.bijective.sum_comp (fun word => term (Fin.cons true word))).symm
      _ = _ := Finset.sum_congr rfl (fun word _ => hpair word)
  have hsplit : (∑ pair : Bool × (Fin n → Bool), term (Fin.cons pair.1 pair.2)) =
      ∑ word, term word :=
    (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp term
  rw [← hsplit, Fintype.sum_prod_type, Fintype.sum_bool, hsum]
  have hpositive (word : Fin n → Bool) : term (Fin.cons false word) =
      polarizationWeight word *
        (x 0 + polarizationSum (fun i => x i.succ) word) ^ (n + 1) := by
    simp [term, polarizationWeight, polarizationSum, Fin.prod_univ_succ,
      Fin.sum_univ_succ, polarizationSign]
  simp_rw [hpositive]
  ring

end Toffoli
