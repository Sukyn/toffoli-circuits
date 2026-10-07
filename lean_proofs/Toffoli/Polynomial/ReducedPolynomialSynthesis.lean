import Toffoli.Polynomial.ReducedMonomialSynthesis
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Toffoli

/-- Every supported monomial except the top one has a smaller exponent in
some coordinate. Compile those monomials and concatenate their circuits. -/
theorem reduced_polynomial_synthesis {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) (f : MvPolynomial (Fin n) (ZMod p))
    (hdegree : ∀ i, f.degreeOf i ≤ p - 1)
    (htop : f.coeff (Finsupp.equivFunOnFinite.symm
      (fun _ : Fin n => p - 1)) = 0) :
    ∃ c : MultiCircuit (ZMod p) n, c.Realizes (fun x => MvPolynomial.eval x f) := by
  classical
  have monomial (d : f.support) : ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => f.coeff d.val * ∏ i, x i ^ d.val i) := by
    have hd (i) : d.val i ≤ p - 1 :=
      (MvPolynomial.monomial_le_degreeOf i d.property).trans (hdegree i)
    have hne : d.val ≠ Finsupp.equivFunOnFinite.symm (fun _ : Fin n => p - 1) := by
      intro heq
      exact (MvPolynomial.mem_support_iff.mp d.property) (by simpa only [heq] using htop)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    have hi' : d.val i ≠ p - 1 := by simpa using hi
    have hlow : ∃ i, d.val i < p - 1 := ⟨i, by have := hd i; omega⟩
    exact reduced_monomial_synthesis hp hn d.val hd hlow (f.coeff d.val)
  choose circuits hcircuits using monomial
  refine ⟨f.support.attach.toList.flatMap circuits, ?_⟩
  have hrun := multi_circuit_realizes_list f.support.attach.toList circuits
    (fun d x => f.coeff d.val * ∏ i, x i ^ d.val i) (fun d _ => hcircuits d)
  intro x t
  -- The compiled increments are exactly the supported monomials of f.
  simpa only [Finset.sum_map_toList,
    Finset.sum_attach f.support (fun d => f.coeff d * ∏ i, x i ^ d i),
    ← MvPolynomial.eval_eq' x f] using hrun x t

end Toffoli
