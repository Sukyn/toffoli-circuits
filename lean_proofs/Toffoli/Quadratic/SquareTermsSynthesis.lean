import Toffoli.Quadratic.QuadraticModel
import Toffoli.Additions.OptimalLinearFormPowerAddition
import Toffoli.Foundations.MultiAffineAddition
import Toffoli.Foundations.MultiCircuitRealizesList
import Toffoli.Foundations.MultiCircuitCostList

namespace Toffoli

/-- Compile each square of a nonzero linear form with a least-order admissible multiplier,
then add the affine part. Each term restores the same control register,
and the resulting count is exactly one optimal square cost per term.
Coefficients may vanish; they do not affect this construction's gate count. -/
theorem square_terms_synthesis {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) (terms : List (SquareTerm (ZMod p) n))
    (hterms : ∀ term ∈ terms, term.linear ≠ 0) (b : ZMod p) (a : Fin n → ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => (terms.map (fun term => term.eval x)).sum + affineValue b a x) ∧
      c.cost = terms.length * optimalSquareCost p hp := by
  classical
  have hterm (term : {t // t ∈ terms}) : ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes term.val.eval ∧ c.cost = optimalSquareCost p hp := by
    simpa only [SquareTerm.eval, optimalSquareCost, optimalSquareOrder] using
      optimal_linear_form_power_addition term.val.coefficient term.val.linear
        (Function.ne_iff.mp (hterms term.val term.property)) 2 (by decide) (by omega)
  choose circuits hrealizes hcost using hterm
  have hlist := multi_circuit_realizes_list terms.attach circuits (fun term => term.val.eval)
    (fun term _ => hrealizes term)
  have hcount : MultiCircuit.cost (terms.attach.flatMap circuits) =
      terms.length * optimalSquareCost p hp := by
    simp [multi_circuit_cost_list, hcost]
  obtain ⟨affine, haffine, haffine_cost⟩ := multi_affine_addition ⟨0, hn⟩ b a
  refine ⟨terms.attach.flatMap circuits ++ affine, ?_, ?_⟩
  · intro x t
    simpa only [List.attach_map_val (l := terms) (f := fun term => term.eval x), affineValue]
      using multi_circuit_realizes_append _ _ _ _ hlist haffine x t
  · rw [multi_circuit_cost_append, hcount, haffine_cost, add_zero]

end Toffoli
