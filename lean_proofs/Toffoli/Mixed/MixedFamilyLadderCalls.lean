import Toffoli.Mixed.MixedLadderWorkspace
import Toffoli.Mixed.FamilyProductConstructionModel
import Toffoli.Mixed.MixedLadderCallLocality
import Mathlib.Tactic.Choose

namespace Toffoli

/-- Compile each allocated ladder update on its own pool, retaining its
family derivation. Internal destinations become controls of the parent,
so their locality proofs also lift to the complete ladder's pool. -/
theorem mixed_family_ladder_calls {p n d b : ℕ} [Fact p.Prime]
    {L : MixedLadder d b} {controls pool : Finset (Fin n)}
    (layout : MixedLadderLayout L controls pool) (q : Fin L.groups.length → ℕ)
    (children : ∀ j, FamilyProductConstruction p (L.controls j) (L.borrowed j) (q j))
    (target : IndexedTarget n) (htarget : ∀ i ∈ pool, target ≠ some i) :
    ∃ call : Fin L.groups.length → ZMod p → MultiCircuit (ZMod p) n,
      (∀ j a, MixedCircuitFamily (L.controls j) (L.borrowed j)
        (layout.callControls j) (layout.callPool j) (layout.callTarget target j)
        a (call j a)) ∧
      (∀ j a x t, (call j a).eval (x, t) = indexedTargetAdd (layout.callTarget target j)
        (a * ∏ i ∈ layout.callControls j, x i) (x, t)) ∧
      (∀ j a, (call j a).cost = q j) ∧
      ∀ j a, (call j a).AccumulatorLocal pool target := by
  classical
  have hplacement := mixed_ladder_call_locality (K := ZMod p) layout target htarget
  have hcall (j : Fin L.groups.length) (a : ZMod p) := by
    obtain ⟨hcard, hsubset, hpool, _⟩ := mixed_ladder_workspace layout j
    exact children j (layout.callControls j) (layout.callPool j) hsubset hcard hpool
      (layout.callTarget target j) (hplacement j).1 a
  choose call member hrun hcost hlocal using hcall
  exact ⟨call, member, hrun, hcost, fun j a => (hplacement j).2 (call j a) (hlocal j a)⟩

end Toffoli
