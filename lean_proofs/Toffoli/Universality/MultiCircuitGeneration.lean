import Toffoli.Universality.MultiGateGeneration

namespace Toffoli
open scoped Classical

/-- A realizing primitive circuit places its target addition in the generated
permutation group. Multiplication follows the circuit's execution order. -/
theorem multi_circuit_generation {K : Type*} [Field K] {n : ℕ}
    (hone : affineSwapGroup K (Equiv.swap (0 : K) 1) = ⊤)
    (c : MultiCircuit K n) (f : Controls K n → K) (hc : c.Realizes f) :
    targetAddition f ∈ affineSwapGroup K (targetSwap (C := Controls K n) (K := K)) := by
  let G := affineSwapGroup K (targetSwap (C := Controls K n) (K := K))
  have compile (c : MultiCircuit K n) : ∃ σ ∈ G, ∀ s, σ s = c.eval s := by
    induction c with
    | nil => exact ⟨1, G.one_mem, fun _ => rfl⟩
    | cons g c ih =>
      obtain ⟨σ, hσ, hrun⟩ := multi_gate_generation hone g
      obtain ⟨τ, hτ, htail⟩ := ih
      refine ⟨τ * σ, G.mul_mem hτ hσ, fun s => ?_⟩
      rw [Equiv.Perm.mul_apply, htail, hrun]
      rfl
  obtain ⟨σ, hσ, hrun⟩ := compile c
  have heq : σ = targetAddition f := by
    ext ⟨x, t⟩ : 1
    exact (hrun (x, t)).trans (hc x t)
  rwa [← heq]

end Toffoli
