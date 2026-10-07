import Toffoli.Mixed.MixedLadderLayoutModel
import Toffoli.Mixed.MixedLadderProduct
import Toffoli.Mixed.CompiledIndexedChainLadder

namespace Toffoli

/-- Realize an allocated ladder by compiling its signed occurrence trace.
The layout determines every call's controls and destination. Reindexing the
stages preserves that exact primitive list, its execution, cost, and locality. -/
theorem compiled_mixed_ladder {K : Type*} [Field K] {n d b : ℕ}
    {L : MixedLadder d b} {controls pool : Finset (Fin n)}
    (layout : MixedLadderLayout L controls pool) (q : Fin L.groups.length → ℕ)
    (target : IndexedTarget n) (htarget : ∀ i ∈ pool, target ≠ some i)
    (call : Fin L.groups.length → K → MultiCircuit K n)
    (hcall : ∀ j a x t, (call j a).eval (x, t) =
      indexedTargetAdd (layout.callTarget target j)
        (a * ∏ i ∈ layout.callControls j, x i) (x, t))
    (hcost : ∀ j a, (call j a).cost = q j)
    (hlocal : ∀ j a, (call j a).AccumulatorLocal pool target)
    (m : ℕ) (hlength : L.groups.length = m + 2) (μ : K) :
    let index : Fin (m + 2) ≃ Fin L.groups.length := finCongr hlength.symm
    let circuit : MultiCircuit K n := (indexedLadderTrace m μ).flatMap (fun step => call (index step.1) step.2)
    (∀ x t, circuit.eval (x, t) =
      indexedTargetAdd target (μ * ∏ i ∈ controls, x i) (x, t)) ∧
      circuit.cost = L.cost q ∧ circuit.AccumulatorLocal pool target := by
  classical
  let index : Fin (m + 2) ≃ Fin L.groups.length := finCongr hlength.symm
  let groups (j : Fin (m + 2)) := layout.groups (index j)
  let dirty (j : Fin (m + 1)) :=
    layout.dirty ⟨j.val, by have := j.isLt; omega⟩
  have hindex (j : Fin (m + 2)) : (index j).val = j.val := rfl
  have hdirtyOutside (i : Fin (L.groups.length - 1)) (j : Fin L.groups.length) :
      layout.dirty i ∉ layout.groups j :=
    fun hi => (Finset.mem_sdiff.mp (layout.dirty_mem i)).2 (layout.group_subset j hi)
  have hinjective : Function.Injective dirty := by
    intro i j h
    exact Fin.ext (congrArg (@Fin.val (L.groups.length - 1)) (layout.dirty.injective h))
  have houtside (i : Fin (m + 1)) (j : Fin (m + 2)) : dirty i ∉ groups j :=
    hdirtyOutside _ _
  have hgroups (j : Fin (m + 2)) : groups j ⊆ pool :=
    (layout.group_subset (index j)).trans layout.controls_subset
  have hdirty (j : Fin (m + 1)) : dirty j ∈ pool :=
    (Finset.mem_sdiff.mp (layout.dirty_mem _)).1
  have hfirst : ∀ a x t, (call (index 0) a).eval (x, t) =
      indexedTargetAdd (some (dirty 0)) (a * ∏ i ∈ groups 0, x i) (x, t) := by
    intro a x t
    have hlast : (index 0).val + 1 ≠ L.groups.length := by
      rw [hindex, hlength]
      simp
    have h := hcall (index 0) a x t
    simp only [MixedLadderLayout.callControls, dif_pos (show (index 0).val = 0 from rfl),
      MixedLadderLayout.callTarget, dif_neg hlast] at h
    exact h
  have hmiddle : ∀ (j : Fin m) a x t, (call (index j.castSucc.succ) a).eval (x, t) =
      indexedTargetAdd (some (dirty j.succ))
        (a * x (dirty j.castSucc) * ∏ i ∈ groups j.castSucc.succ, x i) (x, t) := by
    intro j a x t
    have hfirst : (index j.castSucc.succ).val ≠ 0 := by simp [hindex]
    have hlast : (index j.castSucc.succ).val + 1 ≠ L.groups.length := by
      rw [hindex, hlength]
      have := j.isLt
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have h := hcall (index j.castSucc.succ) a x t
    simp only [MixedLadderLayout.callControls, dif_neg hfirst,
      MixedLadderLayout.callTarget, dif_neg hlast,
      Finset.prod_insert (hdirtyOutside _ _)] at h
    simpa [groups, dirty, index, mul_assoc] using h
  have hlast : ∀ a x t, (call (index (Fin.last (m + 1))) a).eval (x, t) =
      indexedTargetAdd target
        (a * x (dirty (Fin.last m)) * ∏ i ∈ groups (Fin.last (m + 1)), x i) (x, t) := by
    intro a x t
    have hfirst : (index (Fin.last (m + 1))).val ≠ 0 := by simp [hindex]
    have hlast : (index (Fin.last (m + 1))).val + 1 = L.groups.length := by
      rw [hindex, hlength]
      rfl
    have h := hcall (index (Fin.last (m + 1))) a x t
    simp only [MixedLadderLayout.callControls, dif_neg hfirst,
      MixedLadderLayout.callTarget, dif_pos hlast,
      Finset.prod_insert (hdirtyOutside _ _)] at h
    simpa [groups, dirty, index, mul_assoc] using h
  obtain ⟨hrun, hcount, hprotected⟩ := compiled_indexed_chain_ladder pool target groups dirty
    hinjective houtside hgroups hdirty htarget (fun j => call (index j))
    (fun j => q (index j)) hfirst hmiddle hlast
    (fun j => hcost (index j)) (fun j => hlocal (index j)) μ
  refine ⟨?_, ?_, hprotected⟩
  · intro x t
    have hproduct : (∏ j, ∏ i ∈ groups j, x i) = ∏ i ∈ controls, x i :=
      (index.prod_comp (fun j => ∏ i ∈ layout.groups j, x i)).trans
        (mixed_ladder_product layout x)
    simpa only [hproduct] using hrun x t
  · rw [hcount]
    simpa only [MixedLadder.cost, hindex, hlength] using
      index.sum_comp (fun j => (if j.val = 0 ∨ j.val + 1 = L.groups.length then 2 else 4) * q j)

end Toffoli
