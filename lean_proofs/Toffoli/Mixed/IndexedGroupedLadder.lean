import Toffoli.Mixed.IndexedGroupedPassStep
import Toffoli.Mixed.IndexedGroupedStageValuesUpdate
import Toffoli.Mixed.IndexedGroupedStageValuesTarget
import Toffoli.Foundations.IndexedTargetAddAdd
import Toffoli.Borrow.BorrowedPropagation

namespace Toffoli

/-- Two supplied grouped passes cancel every initial borrowed value.
The first group is prepared only for the positive pass. The explicit
primitive list retains both endpoint calls, including when μ is zero. -/
theorem indexed_grouped_ladder {K : Type*} [Field K] {n : ℕ}
    (pool first last : Finset (Fin n)) (dirty : Fin n) (target : IndexedTarget n)
    (stages : List (Finset (Fin n) × Fin n))
    (hfirstDirty : dirty ∉ first) (hlastDirty : dirty ∉ last)
    (hstagesDirty : ∀ stage ∈ stages, dirty ∉ stage.1 ∧ dirty ≠ stage.2)
    (htdirty : target ≠ some dirty)
    (htfirst : ∀ i ∈ first, target ≠ some i)
    (htlast : ∀ i ∈ last, target ≠ some i)
    (htstages : ∀ stage ∈ stages,
      (∀ i ∈ stage.1, target ≠ some i) ∧ target ≠ some stage.2)
    (group pass : K → MultiCircuit K n) (q r : ℕ)
    (hgroup : ∀ a x t, (group a).eval (x, t) =
      indexedTargetAdd (some dirty) (a * ∏ i ∈ first, x i) (x, t))
    (hpass : ∀ a x t, (pass a).eval (x, t) = indexedTargetAdd target
      (a * borrowedPropagation (x dirty) (indexedGroupedStageValues stages x) *
        ∏ i ∈ last, x i) (x, t))
    (hgroupCost : ∀ a, (group a).cost = q)
    (hpassCost : ∀ a, (pass a).cost = r)
    (hgroupLocal : ∀ a, (group a).AccumulatorLocal pool target)
    (hpassLocal : ∀ a, (pass a).AccumulatorLocal pool target) (μ : K) :
    (∀ x t, (((group 1 ++ pass μ) ++ group (-1)) ++ pass (-μ)).eval (x, t) =
      indexedTargetAdd target
        (μ * (∏ i ∈ first, x i) *
          ((indexedGroupedStageValues stages x).map Prod.fst).prod *
          ∏ i ∈ last, x i) (x, t)) ∧
    (((group 1 ++ pass μ) ++ group (-1)) ++ pass (-μ)).cost = 2 * q + 2 * r ∧
    (((group 1 ++ pass μ) ++ group (-1)) ++ pass (-μ)).AccumulatorLocal pool target := by
  have hvaluesUpdate (x : Controls K n) (v : K) :=
    indexed_grouped_stage_values_update stages x dirty v hstagesDirty
  have hlastUpdate (x : Controls K n) (v : K) :=
    Finset.prod_update_of_notMem hlastDirty x v
  have hvaluesTarget (amount : K) (x : Controls K n) (t : K) :=
    indexed_grouped_stage_values_target stages target htstages amount x t
  have hlastTarget (x : Controls K n) (t amount : K) :
      (∏ i ∈ last, (indexedTargetAdd target amount (x, t)).1 i) =
        ∏ i ∈ last, x i :=
    Finset.prod_congr rfl (fun i hi =>
      indexed_target_add_control target amount x t i (htlast i hi))
  let increment (x : Controls K n) :=
    μ * borrowedPropagation (x dirty + ∏ i ∈ first, x i)
      (indexedGroupedStageValues stages x) * ∏ i ∈ last, x i
  obtain ⟨hprepared, hpreparedCost, hpreparedLocal⟩ :=
    indexed_grouped_pass_step pool first dirty target hfirstDirty htdirty htfirst
      (group 1) (pass μ) (group (-1))
      (fun x => μ * borrowedPropagation (x dirty) (indexedGroupedStageValues stages x) *
        ∏ i ∈ last, x i) q r
      (by simpa only [one_mul] using hgroup 1) (hpass μ)
      (by simpa only [neg_one_mul] using hgroup (-1))
      (hgroupCost 1) (hpassCost μ) (hgroupCost (-1))
      (hgroupLocal 1) (hpassLocal μ) (hgroupLocal (-1))
  have hfirst (x : Controls K n) (t : K) :
      ((group 1 ++ pass μ) ++ group (-1)).eval (x, t) =
        indexedTargetAdd target (increment x) (x, t) := by
    simpa only [increment, Function.update_self, hvaluesUpdate, hlastUpdate]
      using hprepared x t
  -- The propagated difference contains the first product and every later factor,
  -- while all initial dirty values disappear.
  have hcancel (x : Controls K n) :
      increment x + (-μ) * borrowedPropagation (x dirty)
          (indexedGroupedStageValues stages x) * (∏ i ∈ last, x i) =
        μ * (∏ i ∈ first, x i) *
          ((indexedGroupedStageValues stages x).map Prod.fst).prod *
          ∏ i ∈ last, x i := by
    dsimp only [increment]
    rw [borrowedPropagation_difference]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro x t
    rw [multi_circuit_eval_append, hfirst, hpass]
    simp only [indexed_target_add_control target _ _ _ dirty htdirty,
      hvaluesTarget, hlastTarget]
    rw [indexed_target_add_add, hcancel]
  · rw [multi_circuit_cost_append, hpreparedCost, hpassCost]
    ring
  · exact ⟨hpreparedLocal.target_outside, List.forall_mem_append.mpr
      ⟨hpreparedLocal.gates, (hpassLocal (-μ)).gates⟩⟩

end Toffoli
