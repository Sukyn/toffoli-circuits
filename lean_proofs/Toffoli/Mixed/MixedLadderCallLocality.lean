import Toffoli.Mixed.MixedLadderLayoutModel
import Toffoli.Foundations.CircuitLocalityPromote

namespace Toffoli

/-- Each ladder destination lies outside its child pool. A circuit local to
that child is also local to the parent: the last stage has the parent target,
while an internal destination is an allowed control of the parent. -/
theorem mixed_ladder_call_locality {K : Type*} [Field K] {n d b : ℕ}
    {L : MixedLadder d b} {controls pool : Finset (Fin n)}
    (layout : MixedLadderLayout L controls pool) (target : IndexedTarget n)
    (htarget : ∀ i ∈ pool, target ≠ some i) (j : Fin L.groups.length) :
    (∀ i ∈ layout.callPool j, layout.callTarget target j ≠ some i) ∧
      ∀ circuit : MultiCircuit K n,
        circuit.AccumulatorLocal (layout.callPool j) (layout.callTarget target j) →
          circuit.AccumulatorLocal pool target := by
  by_cases hlast : j.val + 1 = L.groups.length
  · simp only [MixedLadderLayout.callPool, MixedLadderLayout.callTarget, dif_pos hlast]
    exact ⟨htarget, fun _ h => h⟩
  · simp only [MixedLadderLayout.callPool, MixedLadderLayout.callTarget, dif_neg hlast]
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa only [ne_eq, Option.some.injEq] using (Finset.mem_erase.mp hi).1.symm
    · intro circuit hlocal
      let destination := layout.dirty ⟨j.val, by have := j.isLt; omega⟩
      exact circuit_locality_promote circuit (pool.erase destination) pool
        (Finset.erase_subset destination pool) destination
        (Finset.mem_sdiff.mp (layout.dirty_mem _)).1 target htarget hlocal

end Toffoli
