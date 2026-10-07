import Toffoli.Polarization.PolarizationModel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

namespace Toffoli

/-- In a signed expansion, nonbijective terms cancel; each bijection contributes 2^n. -/
theorem polarization_monomial_sum {K : Type*} [CommRing K]
    (n : ℕ) (g : Fin n → Fin n) :
    (∑ word : Fin n → Bool,
      polarizationWeight word * ∏ i, (polarizationSign (word (g i)) : K)) =
      if Function.Bijective g then (2 : K) ^ n else 0 := by
  classical
  by_cases hg : Function.Bijective g
  · rw [if_pos hg]
    -- A permutation uses every sign once, so each sign is squared.
    have hterm (word : Fin n → Bool) :
        polarizationWeight word * ∏ i, (polarizationSign (word (g i)) : K) = 1 := by
      rw [hg.prod_comp (fun i => (polarizationSign (word i) : K))]
      unfold polarizationWeight
      rw [← Finset.prod_mul_distrib]
      have hs (b : Bool) : (polarizationSign b : K) * polarizationSign b = 1 := by
        cases b <;> simp [polarizationSign]
      simp [hs]
    simp [hterm, Fintype.card_fin]
  · rw [if_neg hg]
    -- A missing variable lets us pair opposite contributions by flipping its sign.
    have hnotsurj : ¬ Function.Surjective g := fun hs => hg hs.bijective_of_finite
    obtain ⟨j, hj⟩ := not_forall.mp hnotsurj
    have hmiss (i : Fin n) : g i ≠ j := fun h => hj ⟨i, h⟩
    let flip (word : Fin n → Bool) := Function.update word j (!(word j))
    have hflip : Function.Involutive flip := by intro word; simp [flip]
    have hdistinct (word : Fin n → Bool) : flip word ≠ word := by
      intro h
      exact Bool.not_ne_self (word j) (by simpa [flip] using congrFun h j)
    have hweight (word : Fin n → Bool) :
        (polarizationWeight (flip word) : K) = -polarizationWeight word := by
      change (∏ i, ((polarizationSign : Bool → K) ∘
        Function.update word j (!(word j))) i) = -∏ i, polarizationSign (word i)
      rw [Function.comp_update, Finset.prod_update_of_mem (Finset.mem_univ j),
        Finset.sdiff_singleton_eq_erase,
        ← Finset.mul_prod_erase Finset.univ (fun i => (polarizationSign (word i) : K))
          (Finset.mem_univ j)]
      cases word j <;> simp [polarizationSign]
    have hterm (word : Fin n → Bool) :
        (polarizationWeight (flip word) * ∏ i, (polarizationSign (flip word (g i)) : K)) =
        -(polarizationWeight word * ∏ i, (polarizationSign (word (g i)) : K)) := by
      rw [hweight]
      simp [flip, hmiss]
    exact Finset.sum_ninvolution flip
      (fun word => by rw [hterm]; exact add_neg_cancel _)
      (fun word _ => hdistinct word)
      (fun _ => Finset.mem_univ _) hflip

end Toffoli
