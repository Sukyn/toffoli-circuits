import Toffoli.Mixed.MixedLadderLayout
import Toffoli.Mixed.MixedLadderCalls
import Toffoli.Mixed.CompiledMixedLadder

namespace Toffoli

/-- Compile a grouped ladder from its recursive child constructions. The
layout gives each child exactly the workspace prescribed by the recurrence.
The numbered chain restores all dirty wires and preserves the parent's
excluded targets at every gate, with the paper's exact weighted cost. -/
theorem mixed_ladder {K : Type*} [Field K] {d b : ℕ}
    (L : MixedLadder d b) (q : Fin L.groups.length → ℕ)
    (children : ∀ j, ProductConstruction K (L.controls j) (L.borrowed j) (q j)) :
    ProductConstruction K d b (L.cost q) := by
  classical
  intro n controls pool hsubset hcontrols hpool target htarget μ
  obtain ⟨layout⟩ := mixed_ladder_layout L controls pool hsubset hcontrols hpool
  obtain ⟨call, hcall, hcost, hlocal⟩ := mixed_ladder_calls layout q children target htarget
  obtain ⟨m, hlength⟩ : ∃ m, L.groups.length = m + 2 :=
    ⟨L.groups.length - 2, by have := L.at_least_two; omega⟩
  exact ⟨_, compiled_mixed_ladder layout q target htarget call
    hcall hcost hlocal m hlength μ⟩

end Toffoli
