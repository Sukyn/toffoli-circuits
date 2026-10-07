import Toffoli.Mixed.MixedModel
import Mathlib.Tactic.GCongr

namespace Toffoli

/-- A construction valid with b borrowed wires remains valid with more.
Reuse every group and every child cost; only their workspace budgets grow. -/
theorem mixed_cost_workspace {p d b cost : ℕ} (hp : 5 ≤ p)
    (tree : MixedCost p hp d b cost) :
    ∀ b', b ≤ b' → MixedCost p hp d b' cost := by
  induction tree with
  | sum =>
    intro b' _
    exact MixedCost.sum b'
  | toffoli =>
    intro b' _
    exact MixedCost.toffoli b'
  | @polarization d b hd c hdegree q _children ih =>
    intro b' hb
    apply MixedCost.polarization hd c hdegree q
    intro j
    apply ih j
    gcongr
  | @ladder d b hd L q _children ih =>
    intro b' hb
    let L' : MixedLadder d b' := { L with workspace := L.workspace.trans hb }
    apply MixedCost.ladder hd L' q
    intro j
    apply ih j
    dsimp only [MixedLadder.borrowed, L', MixedLadder.controls]
    split_ifs <;> gcongr

end Toffoli
