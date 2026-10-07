import Toffoli.Divide.DivideModel
import Toffoli.Quadratic.QuadraticModel

namespace Toffoli

/-- A grouped ladder uses one dirty accumulator between consecutive groups.
Later updates also use the preceding accumulator as a control. -/
structure MixedLadder (d b : ℕ) where
  groups : Composition d
  at_least_two : 2 ≤ groups.length
  workspace : groups.length - 1 ≤ b
  smaller : ∀ j : Fin groups.length, 0 < j.val → groups.blocksFun j ≤ d - 2

namespace MixedLadder

def controls {d b : ℕ} (L : MixedLadder d b) (j : Fin L.groups.length) : ℕ :=
  L.groups.blocksFun j + if j.val = 0 then 0 else 1

/-- Internal updates exclude the parent target. The last update uses it. -/
def borrowed {d b : ℕ} (L : MixedLadder d b) (j : Fin L.groups.length) : ℕ :=
  if j.val + 1 = L.groups.length then d + b - L.controls j
  else d + b - L.controls j - 1

/-- End stages are called twice; intermediate stages are called four times. -/
def cost {d b : ℕ} (L : MixedLadder d b) (q : Fin L.groups.length → ℕ) : ℕ :=
  ∑ j, (if j.val = 0 ∨ j.val + 1 = L.groups.length then 2 else 4) * q j

end MixedLadder

/-- Recursive cost trees for the paper's mixed family. These record its exact
workspace budgets; compiling them into primitive circuits is a separate step. -/
inductive MixedCost (p : ℕ) (hp : 5 ≤ p) : ℕ → ℕ → ℕ → Prop
  | sum (b : ℕ) : MixedCost p hp 1 b 0
  | toffoli (b : ℕ) : MixedCost p hp 2 b (2 * optimalSquareCost p hp)
  | polarization {d b : ℕ} (hd : 3 ≤ d) (c : Composition (d - 1))
      (hdegree : c.length + 1 ≤ p - 2) (q : Fin c.length → ℕ)
      (children : ∀ j, MixedCost p hp (c.blocksFun j)
        (d + b - c.blocksFun j - 1) (q j)) :
      MixedCost p hp d b (divideStepCost p c hdegree q)
  | ladder {d b : ℕ} (hd : 3 ≤ d) (L : MixedLadder d b)
      (q : Fin L.groups.length → ℕ)
      (children : ∀ j, MixedCost p hp (L.controls j) (L.borrowed j) (q j)) :
      MixedCost p hp d b (L.cost q)

noncomputable def mixedCount (p : ℕ) (hp : 5 ≤ p) (d b : ℕ) : ℕ :=
  sInf {q | MixedCost p hp d b q}

/-- One polarization step with minimum-cost preparations. -/
def MixedPolarizationChoice (p : ℕ) (hp : 5 ≤ p) (d b cost : ℕ) : Prop :=
  ∃ (c : Composition (d - 1)) (hdegree : c.length + 1 ≤ p - 2),
    cost = divideStepCost p c hdegree
      (fun j => mixedCount p hp (c.blocksFun j) (d + b - c.blocksFun j - 1))

/-- One ladder step with minimum-cost updates. -/
def MixedLadderChoice (p : ℕ) (hp : 5 ≤ p) (d b cost : ℕ) : Prop :=
  ∃ L : MixedLadder d b,
    cost = L.cost (fun j => mixedCount p hp (L.controls j) (L.borrowed j))

end Toffoli
