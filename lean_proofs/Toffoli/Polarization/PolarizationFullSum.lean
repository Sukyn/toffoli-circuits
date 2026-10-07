import Toffoli.Polarization.PolarizationMonomialSum
import Mathlib.Data.Fintype.Perm

namespace Toffoli

/-- Fischer's numerator with all signs free. Expansion leaves the n! permutations. -/
theorem polarization_full_sum {K : Type*} [CommRing K]
    (n : ℕ) (x : Fin n → K) :
    (∑ word : Fin n → Bool,
      polarizationWeight word * (polarizationSum x word) ^ n) =
      (2 : K) ^ n * (n.factorial : K) * ∏ i, x i := by
  classical
  have hterm (g : Fin n → Fin n) :
      (∑ word : Fin n → Bool, polarizationWeight word *
        ∏ i, ((polarizationSign (word (g i)) : K) * x (g i))) =
      if Function.Bijective g then (2 : K) ^ n * ∏ i, x i else 0 := by
    simp_rw [Finset.prod_mul_distrib, ← mul_assoc]
    rw [← Finset.sum_mul, polarization_monomial_sum]
    by_cases hg : Function.Bijective g
    · rw [if_pos hg, if_pos hg, hg.prod_comp x]
    · rw [if_neg hg, if_neg hg, zero_mul]
  let e : {g : Fin n → Fin n // Function.Bijective g} ≃ Equiv.Perm (Fin n) :=
    { toFun := fun g => Equiv.ofBijective g.val g.property
      invFun := fun g => ⟨g, g.bijective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Equiv.ext (fun _ => rfl) }
  have hcard : (Finset.univ.filter (fun g : Fin n → Fin n => Function.Bijective g)).card =
      n.factorial := by
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_perm,
      Fintype.card_fin]
  unfold polarizationSum
  simp_rw [Fintype.sum_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hterm]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    hcard, nsmul_eq_mul]
  ring

end Toffoli
