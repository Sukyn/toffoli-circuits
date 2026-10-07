import Mathlib.Algebra.Field.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Shared semantics for one control wire and one target wire.
Gate lists run from left to right. Only `swap` contributes to the count.
The nonzero coefficient on `affine` makes its control update invertible.
-/
namespace Toffoli

inductive Gate (K : Type*) [Zero K] where
  | affine (a b : K) (nonzero : a ≠ 0)
  | swap (a b : K)
  | sum (coefficient : K)

variable {K : Type*} [Field K]

noncomputable def Gate.eval (g : Gate K) (s : K × K) : K × K := by
  classical
  exact match g with
    | .affine a b _ => (a * s.1 + b, s.2)
    | .swap a b => (Equiv.swap a b s.1, s.2)
    | .sum coefficient => (s.1, s.2 + coefficient * s.1)

@[simp] def Gate.cost : Gate K → ℕ
  | .swap _ _ => 1
  | _ => 0

abbrev Circuit (K : Type*) [Zero K] := List (Gate K)

noncomputable def Circuit.eval (c : Circuit K) (s : K × K) : K × K :=
  c.foldl (fun state gate => gate.eval state) s

def Circuit.cost (c : Circuit K) : ℕ := (c.map Gate.cost).sum

noncomputable def Circuit.Realizes (c : Circuit K) (f : K → K) : Prop :=
  ∀ x t, c.eval (x, t) = (x, t + f x)

end Toffoli
