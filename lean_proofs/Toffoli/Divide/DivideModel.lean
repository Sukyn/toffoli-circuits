import Toffoli.Additions.AdmissibleOrder
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Lattice

namespace Toffoli

/-- The power calls and weighted preparation calls in one grouped step.
The composition lists the ordered positive group sizes, whose sum is d-1. -/
def divideStepCost (p : ℕ) {d : ℕ} (c : Composition (d - 1))
    (hdegree : c.length + 1 ≤ p - 2) (q : Fin c.length → ℕ) : ℕ :=
  2 ^ c.length * ((p - 1) - (p - 1) /
    leastAdmissibleOrder (p - 1) (c.length + 1) (by omega) (by omega)) +
      ∑ j : Fin c.length, (2 + 2 ^ j.val) * q j

/-- Costs of recursive grouped-polarization constructions. A leaf is SUM;
each other node records its grouping and the costs of its child circuits.
This relation describes finite construction trees, before taking a minimum. -/
inductive DivideCost (p : ℕ) : ℕ → ℕ → Prop
  | sum : DivideCost p 1 0
  | step {d : ℕ} (hd : 2 ≤ d) (c : Composition (d - 1))
      (hdegree : c.length + 1 ≤ p - 2) (q : Fin c.length → ℕ)
      (children : ∀ j, DivideCost p (c.blocksFun j) (q j)) :
      DivideCost p d (divideStepCost p c hdegree q)

/-- The infimum of the recursive construction costs. `divide_count_spec`
proves attainment for p ≥ 5 and d ≥ 1. -/
noncomputable def divideCount (p d : ℕ) : ℕ := sInf {q | DivideCost p d q}

end Toffoli
