import Toffoli.Mixed.MixedLadderWorkspace
import Toffoli.Foundations.ProductConstructionModel
import Toffoli.Mixed.MixedLadderCallLocality
import Mathlib.Tactic.Choose

namespace Toffoli

/-- Compile every allocated ladder call with its exact workspace budget.
The same witnesses realize the required updates and costs; promoting internal
targets to parent controls proves locality for the complete ladder's pool. -/
theorem mixed_ladder_calls {K : Type*} [Field K] {n d b : ℕ}
    {L : MixedLadder d b} {controls pool : Finset (Fin n)}
    (layout : MixedLadderLayout L controls pool) (q : Fin L.groups.length → ℕ)
    (children : ∀ j, ProductConstruction K (L.controls j) (L.borrowed j) (q j))
    (target : IndexedTarget n) (htarget : ∀ i ∈ pool, target ≠ some i) :
    ∃ call : Fin L.groups.length → K → MultiCircuit K n,
      (∀ j a x t, (call j a).eval (x, t) = indexedTargetAdd (layout.callTarget target j)
        (a * ∏ i ∈ layout.callControls j, x i) (x, t)) ∧
      (∀ j a, (call j a).cost = q j) ∧
      ∀ j a, (call j a).AccumulatorLocal pool target := by
  classical
  have hplacement := mixed_ladder_call_locality (K := K) layout target htarget
  have hcall (j : Fin L.groups.length) (a : K) := by
    obtain ⟨hcard, hsubset, hpool, _⟩ := mixed_ladder_workspace layout j
    exact children j (layout.callControls j) (layout.callPool j) hsubset hcard hpool
      (layout.callTarget target j) (hplacement j).1 a
  choose call hrun hcost hlocal using hcall
  exact ⟨call, hrun, hcost, fun j a => (hplacement j).2 (call j a) (hlocal j a)⟩

end Toffoli
