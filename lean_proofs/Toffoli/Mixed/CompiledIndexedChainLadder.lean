import Toffoli.Mixed.CompiledIndexedChainPass
import Toffoli.Mixed.IndexedGroupedLadder
import Toffoli.Mixed.MixedLadderCostSplit
import Mathlib.Algebra.BigOperators.Fin

namespace Toffoli

/-- The primitive list compiled from the signed ladder trace realizes the
product addition, restores every dirty wire, and has the exact ladder cost.
Keeping the list explicit allows a separate family derivation per occurrence. -/
theorem compiled_indexed_chain_ladder {K : Type*} [Field K] {n m : ℕ}
    (pool : Finset (Fin n)) (target : IndexedTarget n)
    (groups : Fin (m + 2) → Finset (Fin n)) (dirty : Fin (m + 1) → Fin n)
    (hinjective : Function.Injective dirty)
    (houtside : ∀ i j, dirty i ∉ groups j)
    (hgroups : ∀ j, groups j ⊆ pool) (hdirty : ∀ j, dirty j ∈ pool)
    (htarget : ∀ i ∈ pool, target ≠ some i)
    (call : Fin (m + 2) → K → MultiCircuit K n) (q : Fin (m + 2) → ℕ)
    (hfirst : ∀ a x t, (call 0 a).eval (x, t) =
      indexedTargetAdd (some (dirty 0)) (a * ∏ i ∈ groups 0, x i) (x, t))
    (hmiddle : ∀ (j : Fin m) a x t, (call j.castSucc.succ a).eval (x, t) =
      indexedTargetAdd (some (dirty j.succ))
        (a * x (dirty j.castSucc) * ∏ i ∈ groups j.castSucc.succ, x i) (x, t))
    (hlast : ∀ a x t, (call (Fin.last (m + 1)) a).eval (x, t) =
      indexedTargetAdd target
        (a * x (dirty (Fin.last m)) * ∏ i ∈ groups (Fin.last (m + 1)), x i) (x, t))
    (hcost : ∀ j a, (call j a).cost = q j)
    (hlocal : ∀ j a, (call j a).AccumulatorLocal pool target) (μ : K) :
    let circuit : MultiCircuit K n := (indexedLadderTrace m μ).flatMap (fun step => call step.1 step.2)
    (∀ x t, circuit.eval (x, t) =
        indexedTargetAdd target (μ * ∏ j, ∏ i ∈ groups j, x i) (x, t)) ∧
      circuit.cost = ∑ j, (if j.val = 0 ∨ j.val + 1 = m + 2 then 2 else 4) * q j ∧
      circuit.AccumulatorLocal pool target := by
  classical
  let stages := List.ofFn (fun j : Fin m => (groups j.castSucc.succ, dirty j.succ))
  have htdirty (j : Fin (m + 1)) := htarget (dirty j) (hdirty j)
  have htgroups (j : Fin (m + 2)) (i : Fin n) (hi : i ∈ groups j) :=
    htarget i (hgroups j hi)
  -- The two passes use the same explicit trace with opposite final coefficients.
  let pass (a : K) :=
    (indexedPassTrace m a).flatMap (fun step => call step.1.succ step.2)
  have hpasses (a : K) := compiled_indexed_chain_pass pool target
    (fun j => groups j.succ) dirty hinjective (fun i j => houtside i j.succ)
    htdirty (fun j => htgroups j.succ) (fun j => call j.succ) (fun j => q j.succ)
    hmiddle hlast (fun j => hcost j.succ) (fun j => hlocal j.succ) a
  have hpass := fun a => (hpasses a).1
  have hpassCost := fun a => (hpasses a).2.1
  have hpassLocal := fun a => (hpasses a).2.2
  have hvalues (x : Controls K n) : indexedGroupedStageValues stages x =
      List.ofFn (fun j : Fin m => ((∏ i ∈ groups j.castSucc.succ, x i), x (dirty j.succ))) := by
    simp [stages, indexedGroupedStageValues, List.map_ofFn, Function.comp_def]
  have hstagesDirty : ∀ stage ∈ stages, dirty 0 ∉ stage.1 ∧ dirty 0 ≠ stage.2 := by
    intro stage hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    exact ⟨houtside 0 _, fun h => Fin.succ_ne_zero j (hinjective h).symm⟩
  have htstages : ∀ stage ∈ stages,
      (∀ i ∈ stage.1, target ≠ some i) ∧ target ≠ some stage.2 := by
    intro stage hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    exact ⟨htgroups _, htdirty _⟩
  obtain ⟨hrun, hcount, hprotected⟩ := indexed_grouped_ladder
    pool (groups 0) (groups (Fin.last (m + 1))) (dirty 0) target stages
    (houtside 0 0) (houtside 0 _) hstagesDirty (htdirty 0)
    (htgroups 0) (htgroups _) htstages (call 0) pass (q 0)
    (2 * (∑ j : Fin m, q j.castSucc.succ) + q (Fin.last (m + 1)))
    hfirst (by simpa only [hvalues] using hpass) (hcost 0) hpassCost
    (hlocal 0) hpassLocal μ
  have htrace :
      (indexedLadderTrace m μ).flatMap (fun step => call step.1 step.2) =
        ((call 0 1 ++ pass μ) ++ call 0 (-1)) ++ pass (-μ) := by
    simp [indexedLadderTrace, indexedPassTrace, pass, List.flatMap_map, List.append_assoc]
  rw [htrace]
  refine ⟨?_, ?_, hprotected⟩
  · intro x t
    have hproduct : (∏ i ∈ groups 0, x i) *
        ((indexedGroupedStageValues stages x).map Prod.fst).prod *
        (∏ i ∈ groups (Fin.last (m + 1)), x i) = ∏ j, ∏ i ∈ groups j, x i := by
      rw [hvalues]
      simp only [List.map_ofFn, Function.comp_def, List.prod_ofFn]
      rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
      simp only [Fin.succ_last, mul_assoc]
    simpa only [mul_assoc, ← hproduct] using hrun x t
  · rw [hcount, mixed_ladder_cost_split]
    ring

end Toffoli
