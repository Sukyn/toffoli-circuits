import Toffoli.Foundations.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

namespace Toffoli
variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- Choose the earlier of x and -x in any enumeration of the finite field. -/
noncomputable def oddRepresentatives : Finset K :=
  Finset.univ.filter (fun x => (Fintype.equivFin K x).val < (Fintype.equivFin K (-x)).val)

/-- Each nonzero negation pair has exactly one representative. -/
theorem odd_representatives_spec (htwo : (2 : K) ≠ 0) (x : K) :
    ((x ∈ oddRepresentatives K ∨ -x ∈ oddRepresentatives K) ↔ x ≠ 0) ∧
    ¬(x ∈ oddRepresentatives K ∧ -x ∈ oddRepresentatives K) := by
  have hnotboth : ¬(x ∈ oddRepresentatives K ∧ -x ∈ oddRepresentatives K) := by
    simp only [oddRepresentatives, Finset.mem_filter, Finset.mem_univ, true_and, neg_neg]
    exact fun h => Nat.lt_asymm h.1 h.2
  constructor
  · constructor
    · intro h hx
      subst x
      simpa [oddRepresentatives] using h
    · intro hx
      have hn : x ≠ -x := by
        simpa only [ne_eq, eq_neg_iff_add_eq_zero, ← two_mul,
          mul_eq_zero_iff_left htwo] using hx
      have hr : (Fintype.equivFin K x).val ≠ (Fintype.equivFin K (-x)).val := by
        intro h
        exact hn ((Fintype.equivFin K).injective (Fin.ext h))
      rcases lt_or_gt_of_ne hr with h | h
      · exact Or.inl (by simpa [oddRepresentatives] using h)
      · exact Or.inr (by simpa [oddRepresentatives] using h)
  · exact hnotboth

end Toffoli
