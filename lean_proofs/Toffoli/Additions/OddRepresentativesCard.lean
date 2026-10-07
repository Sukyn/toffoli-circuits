import Toffoli.Additions.OddRepresentatives

namespace Toffoli
variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- Each pair contributes two nonzero elements and one representative. -/
theorem odd_representatives_card (htwo : (2 : K) ≠ 0) :
    (oddRepresentatives K).card = (Fintype.card K - 1) / 2 := by
  classical
  let R := oddRepresentatives K
  have hdisjoint : Disjoint R (R.image fun x => -x) := by
    apply Finset.disjoint_left.mpr
    intro x hx hn
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hn
    subst x
    exact (odd_representatives_spec K htwo y).2 ⟨hy, hx⟩
  have hunion : R ∪ R.image (fun x => -x) = Finset.univ.erase (0 : K) := by
    ext x
    simpa only [Finset.mem_union, Finset.mem_image, neg_eq_iff_eq_neg,
      exists_eq_right, Finset.mem_erase, Finset.mem_univ, and_true]
      using (odd_representatives_spec K htwo x).1
  have himage : (R.image fun x => -x).card = R.card :=
    Finset.card_image_of_injective _ neg_injective
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisjoint, himage] at hcard
  simp only [Finset.card_erase_of_mem (Finset.mem_univ (0 : K)), Finset.card_univ] at hcard
  change R.card = _
  omega

end Toffoli
