import Toffoli.Foundations.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Logic.Equiv.Prod

/-! The paper's accumulator gates on several controls and one target.
Affine maps act only on the controls; swaps exchange two labels on one wire.
Only a scaled SUM can change the target. Whole control-string permutations
are not primitive gates: their synthesis is a separate universality problem.
-/
namespace Toffoli

abbrev Controls (K : Type*) (n : ℕ) := Fin n → K

inductive MultiGate (K : Type*) [Field K] (n : ℕ) where
  | affine (e : Controls K n ≃ᵃ[K] Controls K n)
  | swap (i : Fin n) (a b : K)
  | sum (i : Fin n) (coefficient : K)

variable {K : Type*} [Field K] {n : ℕ}

noncomputable def MultiGate.control : MultiGate K n → Equiv.Perm (Controls K n)
  | .affine e => e.toEquiv
  | .swap i a b => by
      classical
      exact Equiv.piCongrRight (fun j => if j = i then Equiv.swap a b else Equiv.refl K)
  | .sum _ _ => Equiv.refl _

def MultiGate.increment : MultiGate K n → Controls K n → K
  | .sum i coefficient, x => coefficient * x i
  | _, _ => 0

noncomputable def MultiGate.eval (g : MultiGate K n) (state : Controls K n × K) :
    Controls K n × K := (g.control state.1, state.2 + g.increment state.1)

def MultiGate.cost : MultiGate K n → ℕ
  | .swap _ _ _ => 1
  | _ => 0

abbrev MultiCircuit (K : Type*) [Field K] (n : ℕ) := List (MultiGate K n)

noncomputable def MultiCircuit.eval (c : MultiCircuit K n) (state : Controls K n × K) :
    Controls K n × K := c.foldl (fun state gate => gate.eval state) state

def MultiCircuit.cost (c : MultiCircuit K n) : ℕ := (c.map MultiGate.cost).sum

noncomputable def MultiCircuit.Realizes (c : MultiCircuit K n) (f : Controls K n → K) : Prop :=
  ∀ x t, c.eval (x, t) = (x, t + f x)

end Toffoli
