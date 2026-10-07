import Toffoli.Polynomial.LowExponentMonomialSynthesis
import Toffoli.Polynomial.TopExponentFactor
import Toffoli.Polynomial.FiniteProductSplitTwo

namespace Toffoli

/-- Every reduced monomial except the all-`p - 1` monomial has an accumulator
circuit. Induct on the number of top exponents: a shear removes one of them,
and unary factor replacement restores the chosen lower exponent afterwards. -/
theorem reduced_monomial_synthesis {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, d i ≤ p - 1)
    (hlow : ∃ i, d i < p - 1) (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => μ * ∏ i, x i ^ d i) := by
  classical
  let tops (e : Fin n → ℕ) := Finset.univ.filter (fun i => e i = p - 1)
  have build : ∀ k, ∀ e : Fin n → ℕ, (tops e).card = k →
      (∀ i, e i ≤ p - 1) → (∃ i, e i < p - 1) → ∀ a : ZMod p,
      ∃ c : MultiCircuit (ZMod p) n, c.Realizes (fun x => a * ∏ i, x i ^ e i) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e hk he hlow a
      by_cases htop : (tops e).Nonempty
      · obtain ⟨j, hj⟩ := htop
        have hjtop : e j = p - 1 := (Finset.mem_filter.mp hj).2
        obtain ⟨i, hi⟩ := hlow
        have hij : i ≠ j := by
          rintro rfl
          omega
        let rest (x : Controls (ZMod p) n) :=
          ∏ l ∈ (Finset.univ.erase i).erase j, x l ^ e l
        have hind (x : Controls (ZMod p) n) (b : ZMod p) :
            rest (Function.update x i b) = rest x := by
          apply Finset.prod_congr rfl
          intro l hl
          rw [Function.update_of_ne (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1]

        -- Replacing both selected exponents by lower ones removes exactly j.
        have ht (u v : ℕ) (hu : u < p - 1) (hv : v < p - 1) :
            tops (Function.update (Function.update e i u) j v) = (tops e).erase j := by
          ext l
          by_cases hli : l = i
          · subst l
            simp [tops, hij, hu.ne, hi.ne]
          · by_cases hlj : l = j
            · subst l
              simp [tops, hv.ne]
            · simp [tops, hli, hlj]
        have factor (u v : ℕ) (x : Controls (ZMod p) n) :
            (∏ l, x l ^ (Function.update (Function.update e i u) j v) l) =
              x i ^ u * x j ^ v * rest x := by
          rw [finite_product_split_two Finset.univ _ i j
            (Finset.mem_univ i) (Finset.mem_univ j) hij]
          simp only [Function.update_of_ne hij, Function.update_self]
          congr 1
          apply Finset.prod_congr rfl
          intro l hl
          have hlj := (Finset.mem_erase.mp hl).1
          have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
          simp [hli, hlj]
        have smaller (u v : ℕ) (hu : u < p - 1) (hv : v < p - 1)
            (b : ZMod p) : ∃ c : MultiCircuit (ZMod p) n,
            c.Realizes (fun x => b * (x i ^ u * x j ^ v * rest x)) := by
          let e' := Function.update (Function.update e i u) j v
          have hcount : (tops e').card < k := by
            rw [ht u v hu hv, ← hk]
            exact Finset.card_erase_lt_of_mem hj
          have hfirst : Function.update e i u ≤ fun _ => p - 1 :=
            update_le_iff.mpr ⟨hu.le, fun l _ => he l⟩
          have hdegree : e' ≤ fun _ => p - 1 :=
            update_le_iff.mpr ⟨hv.le, fun l _ => hfirst l⟩
          obtain ⟨c, hc⟩ := ih (tops e').card hcount e' rfl hdegree
            ⟨j, by simpa [e'] using hv⟩ b
          exact ⟨c, fun x t => by simpa only [e', factor] using hc x t⟩

        -- The shear produces a linear factor at i and the desired top power at j.
        have linear_factor (b : ZMod p) : ∃ c : MultiCircuit (ZMod p) n,
            c.Realizes (fun x => b * (x i * (x j ^ (p - 1) * rest x))) := by
          have square := smaller 2 (p - 2) (by omega) (by omega)
          have linear : ∀ b : ZMod p, ∃ c : MultiCircuit (ZMod p) n,
              c.Realizes (fun x => b * (x j * rest x)) := by
            intro b
            simpa only [pow_zero, pow_one, one_mul] using
              smaller 0 1 (by omega) (by omega) b
          obtain ⟨c, hc⟩ := top_exponent_factor hp i j hij rest hind square linear b
          exact ⟨c, fun x t => by simpa only [mul_assoc] using hc x t⟩
        have hind' (x : Controls (ZMod p) n) (b : ZMod p) :
            (Function.update x i b) j ^ (p - 1) * rest (Function.update x i b) =
              x j ^ (p - 1) * rest x := by
          rw [Function.update_of_ne hij.symm, hind]
        have hsum : ∑ b : ZMod p, b ^ e i = 0 :=
          FiniteField.sum_pow_lt_card_sub_one (ZMod p) (e i) (by simpa using hi)
        obtain ⟨c, hc⟩ := unary_factor_replacement i
          (fun x => x j ^ (p - 1) * rest x) hind' linear_factor
          (fun b => b ^ e i) hsum a
        refine ⟨c, fun x t => ?_⟩
        have hproduct : (∏ l, x l ^ e l) = x i ^ e i * (x j ^ (p - 1) * rest x) := by
          simpa only [hjtop, mul_assoc] using finite_product_split_two
            Finset.univ (fun l => x l ^ e l) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
        simpa only [hproduct] using hc x t
      · apply low_exponent_monomial_synthesis hp hn e ?_ a
        intro i
        have hne : e i ≠ p - 1 := by
          intro h
          exact htop ⟨i, by simp [tops, h]⟩
        have := he i
        omega
  exact build (tops d).card d rfl hd hlow μ

end Toffoli
