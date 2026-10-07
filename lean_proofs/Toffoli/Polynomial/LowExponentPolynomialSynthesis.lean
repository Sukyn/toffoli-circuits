import Toffoli.Polynomial.LowExponentMonomialSynthesis
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Toffoli

/-- Compile each supported monomial and concatenate its circuit. The bound
is on each variable's degree, so the total degree may exceed `p - 2`.
For example, over `ZMod 5`, this includes `x₀³*x₁³ + x₀² + 1`. -/
theorem low_exponent_polynomial_synthesis {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) (f : MvPolynomial (Fin n) (ZMod p))
    (hdegree : ∀ i, f.degreeOf i ≤ p - 2) :
    ∃ c : MultiCircuit (ZMod p) n, c.Realizes (fun x => MvPolynomial.eval x f) := by
  classical
  have monomial (d : f.support) : ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => f.coeff d.val * ∏ i, x i ^ d.val i) :=
    low_exponent_monomial_synthesis hp hn d.val
      (fun i => (MvPolynomial.monomial_le_degreeOf i d.property).trans (hdegree i))
      (f.coeff d.val)
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
