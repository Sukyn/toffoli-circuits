import Toffoli.Mixed.MixedLadderLayoutModel
import Toffoli.Additions.PowerCircuitFamilyModel
import Toffoli.Mixed.IndexedLadderTraceModel
import Toffoli.Polarization.IndexedPolarizationModel
import Toffoli.Foundations.CoordinateShearEval
import Mathlib.Algebra.Field.ZMod

namespace Toffoli

/-- The primitive SUM, with either the external or an internal target. -/
noncomputable def indexedSumCircuit {K : Type*} [Field K] {n : ℕ}
    (i : Fin n) (target : IndexedTarget n) (hti : target ≠ some i) (μ : K) :
    MultiCircuit K n := by
  cases target with
  | none => exact [.sum i μ]
  | some j =>
    have hij : i ≠ j := by simpa [ne_comm] using hti
    exact [.affine (coordinateShear i j μ hij)]

/-- A polarization layout records wires, not a cost or an optimality claim.
The reserved first control is the destination of every preparation. -/
structure MixedPolarizationLayout {n d b : ℕ} (c : Composition (d - 1))
    (controls pool : Finset (Fin n)) where
  controls_subset : controls ⊆ pool
  controls_card : controls.card = d
  pool_card : pool.card = d + b
  first : Fin n
  first_mem : first ∈ controls
  groups : Fin c.length → Finset (Fin n)
  group_card : ∀ j, (groups j).card = c.blocksFun j
  group_subset : ∀ j, groups j ⊆ pool.erase first
  groups_disjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))
  groups_cover : Finset.univ.biUnion groups = controls.erase first

/-- Actual primitive circuits in the paper's recursive family.

Each trace position has its own chunk and recursive derivation. In particular,
two occurrences of the same update may choose different circuits. The pool
excludes the current target, and child pools also exclude their destinations.
No constructor mentions a cost tree, minimum, or required transposition count. -/
inductive MixedCircuitFamily {p n : ℕ} [Fact p.Prime] :
    (d b : ℕ) → Finset (Fin n) → Finset (Fin n) → IndexedTarget n →
      ZMod p → MultiCircuit (ZMod p) n → Prop
  | sum (b : ℕ) (i : Fin n) (pool : Finset (Fin n))
      (hi : i ∈ pool) (hpool : pool.card = 1 + b)
      (target : IndexedTarget n) (htarget : ∀ j ∈ pool, target ≠ some j)
      (μ : ZMod p) :
      MixedCircuitFamily 1 b {i} pool target μ
        (indexedSumCircuit i target (htarget i hi) μ)
  | polarization {d b : ℕ} (hd : 2 ≤ d) (c : Composition (d - 1))
      (hdegree : c.length + 1 ≤ p - 2)
      {controls pool : Finset (Fin n)}
      (layout : MixedPolarizationLayout (b := b) c controls pool)
      (target : IndexedTarget n) (htarget : ∀ j ∈ pool, target ≠ some j)
      (μ : ZMod p) (calls : List (PolarizationCall (ZMod p) c.length))
      (htrace : calls = polarizationCircuit
        (μ * (((2 : ZMod p) ^ c.length * ((c.length + 1).factorial : ZMod p))⁻¹)))
      (chunks : Fin calls.length → MultiCircuit (ZMod p) n)
      (groups : ∀ r j a, calls.get r = .group j a →
        MixedCircuitFamily (c.blocksFun j) (d + b - c.blocksFun j - 1)
          (layout.groups j) (pool.erase layout.first) (some layout.first) a (chunks r))
      (powers : ∀ r a, calls.get r = .power a →
        IndexedPowerCircuitFamily layout.first target a (c.length + 1) (chunks r)) :
      MixedCircuitFamily d b controls pool target μ (List.ofFn chunks).flatten
  | ladder {d b : ℕ} (hd : 3 ≤ d) (L : MixedLadder d b)
      {controls pool : Finset (Fin n)} (layout : MixedLadderLayout L controls pool)
      (target : IndexedTarget n) (htarget : ∀ j ∈ pool, target ≠ some j)
      (μ : ZMod p) (m : ℕ) (hlength : L.groups.length = m + 2)
      (chunks : Fin (indexedLadderTrace m μ).length → MultiCircuit (ZMod p) n)
      (children : ∀ r,
        let call := (indexedLadderTrace m μ).get r
        let j := finCongr hlength.symm call.1
        MixedCircuitFamily (L.controls j) (L.borrowed j)
          (layout.callControls j) (layout.callPool j)
          (layout.callTarget target j) call.2 (chunks r)) :
      MixedCircuitFamily d b controls pool target μ (List.ofFn chunks).flatten

end Toffoli
