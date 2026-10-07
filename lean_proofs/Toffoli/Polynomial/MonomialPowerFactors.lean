import Toffoli.Polynomial.PolynomialPowerModel
import Toffoli.Polarization.FischerPolarization
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorial.NatCast

namespace Toffoli

/-- Polarize a product of coordinate occurrences; coordinates may repeat.
For positive degree, the first factor has fixed positive sign, as in the
paper's Fischer construction. An empty product is represented by a constant. -/
theorem monomial_power_factors {p k d : ℕ} [Fact p.Prime]
    (hd : d ≤ p - 2) (μ : ZMod p) (factors : Fin d → Fin k) :
    ∃ terms : List (PolynomialPowerTerm (ZMod p) k),
      (∀ term ∈ terms, term.degree = d) ∧
      ∀ x, μ * ∏ j, x (factors j) = (terms.map (fun term => term.eval x)).sum := by
  classical
  cases d with
  | zero =>
    refine ⟨[⟨μ, fun _ => 0, 0⟩], ?_, ?_⟩
    · simp
    · intro x
      simp [PolynomialPowerTerm.eval]
  | succ n =>
    have h2 : (2 : ZMod p) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
    have hfactorial : ((n + 1).factorial : ZMod p) ≠ 0 :=
      ((IsUnit.natCast_factorial_iff_of_charP p).2 (by omega)).ne_zero
    let denominator : ZMod p := (2 : ZMod p) ^ n * ((n + 1).factorial : ZMod p)
    have hden : denominator ≠ 0 := mul_ne_zero (pow_ne_zero n h2) hfactorial
    let term (word : Fin n → Bool) : PolynomialPowerTerm (ZMod p) k :=
      { coefficient := μ * denominator⁻¹ * polarizationWeight word
        linear := fun i => (if factors 0 = i then 1 else 0) +
          ∑ j, if factors j.succ = i then polarizationSign (word j) else 0
        degree := n + 1 }
    refine ⟨Finset.univ.toList.map term, ?_, ?_⟩
    · intro t ht
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp ht
      rfl
    · intro x
      have hlinear (word : Fin n → Bool) :
          (∑ i, (term word).linear i * x i) =
            x (factors 0) + polarizationSum (fun j => x (factors j.succ)) word := by
        dsimp [term]
        simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ite_mul, zero_mul]
        rw [Finset.sum_comm]
        simp [polarizationSum]
      have hnormalized : denominator⁻¹ *
          (∑ word : Fin n → Bool, polarizationWeight word *
            (x (factors 0) + polarizationSum (fun j => x (factors j.succ)) word) ^ (n + 1)) =
          ∏ j, x (factors j) := by
        rw [fischer_polarization h2, Fin.prod_univ_succ]
        change denominator⁻¹ * (denominator * x (factors 0) * _) = _
        rw [mul_assoc denominator, inv_mul_cancel_left₀ hden]
      simp only [List.map_map, Finset.sum_map_toList, PolynomialPowerTerm.eval,
        Function.comp_apply]
      simp_rw [hlinear]
      dsimp only [term]
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [hnormalized]

end Toffoli
