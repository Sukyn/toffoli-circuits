import Toffoli.Mixed.MixedLadderLayout
import Toffoli.Mixed.MixedFamilyLadderCalls
import Toffoli.Mixed.CompiledMixedLadder

namespace Toffoli

/-- Compile the signed ladder trace with a separate family derivation at
every position. The same primitive list restores dirty wires, has the exact
weighted cost, and protects every excluded target. -/
theorem mixed_family_ladder {p d b : ℕ} [Fact p.Prime] (hd : 3 ≤ d)
    (L : MixedLadder d b) (q : Fin L.groups.length → ℕ)
    (children : ∀ j, FamilyProductConstruction p (L.controls j) (L.borrowed j) (q j)) :
    FamilyProductConstruction p d b (L.cost q) := by
  classical
  intro n controls pool hsubset hcontrols hpool target htarget μ
  obtain ⟨layout⟩ := mixed_ladder_layout L controls pool hsubset hcontrols hpool
  obtain ⟨call, hmember, hcall, hcost, hlocal⟩ := mixed_family_ladder_calls layout q children target htarget
  -- Number the two endpoints and the intervening groups as Fin (m + 2).
  obtain ⟨m, hlength⟩ : ∃ m, L.groups.length = m + 2 :=
    ⟨L.groups.length - 2, by have := L.at_least_two; omega⟩
  let index : Fin (m + 2) ≃ Fin L.groups.length := finCongr hlength.symm
  obtain ⟨hrun, hcount, hprotected⟩ := compiled_mixed_ladder layout q target htarget
    call hcall hcost hlocal m hlength μ
  let trace := indexedLadderTrace m μ
  let compile (step : Fin (m + 2) × ZMod p) := call (index step.1) step.2
  let chunks (r : Fin trace.length) := compile (trace.get r)
  have hflat : (List.ofFn chunks).flatten = trace.flatMap compile := by
    simp only [chunks, List.ofFn_comp', List.ofFn_get, List.flatMap_def]
  have member : MixedCircuitFamily d b controls pool target μ (List.ofFn chunks).flatten :=
    MixedCircuitFamily.ladder hd L layout target htarget μ m hlength chunks
      (fun r => hmember (index (trace.get r).1) (trace.get r).2)
  rw [hflat] at member
  exact ⟨trace.flatMap compile, member, hrun, hcount, hprotected⟩

end Toffoli
