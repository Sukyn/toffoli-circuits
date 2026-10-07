import Toffoli.Polynomial.PolynomialPowerDecomposition
import Toffoli.Polynomial.PolynomialPowerAddition
import Toffoli.Foundations.MultiCircuitRealizesList

namespace Toffoli

/-- For a positive number of controls, decompose the polynomial into powers
of linear forms by Fischer polarization. Compile each term on the same controls
and concatenate the circuits; each term restores the controls. Repeated factors,
as in x₁²*x₂, require no extra wires. -/
theorem polynomial_synthesis {p n : ℕ} [Fact p.Prime]
    (hn : 0 < n) (f : MvPolynomial (Fin n) (ZMod p))
    (hdegree : f.totalDegree ≤ p - 2) :
    ∃ c : MultiCircuit (ZMod p) n, c.Realizes (fun x => MvPolynomial.eval x f) := by
  classical
  obtain ⟨terms, hdegrees, heval⟩ := polynomial_power_decomposition f hdegree
  have hterm (term : {t // t ∈ terms}) : ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes term.val.eval :=
    polynomial_power_addition hn term.val (hdegrees term.val term.property)
  choose circuits hcircuits using hterm
  refine ⟨terms.attach.flatMap circuits, ?_⟩
  have h := multi_circuit_realizes_list terms.attach circuits (fun term => term.val.eval)
    (fun term _ => hcircuits term)
  intro x t
  simpa only [List.attach_map_val (l := terms) (f := fun term => term.eval x), ← heval x]
    using h x t

end Toffoli
