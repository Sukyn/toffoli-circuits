import Toffoli.Schedules.SchedulePrefixBound
import Toffoli.Schedules.SchedulePrefixCounts
import Toffoli.Schedules.GrayScheduleCostBound

namespace Toffoli

/-- Every scalar-update schedule which evaluates all sign vectors and returns
to zero costs at least the grouped Gray construction. The three lists mark
the first and last evaluations; they can contain arbitrary scalar updates. -/
theorem schedule_cost_bound {K : Type*} [CommRing K] [Nontrivial K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {n : ℕ}
    (prepare traverse restore : List (ScheduleCall K n)) (first last : Fin n → Bool)
    (hprepare : prepare.foldl scheduleStep 0 = fun i => polarizationSign (first i))
    (htraverse : traverse.foldl scheduleStep (fun i => polarizationSign (first i)) =
      fun i => polarizationSign (last i))
    (hrestore : restore.foldl scheduleStep
      (traverse.foldl scheduleStep (fun i => polarizationSign (first i))) = 0)
    (hvisit : ∀ word : Fin n → Bool,
      (fun i => polarizationSign (word i)) ∈
        traverse.scanl scheduleStep (fun i => polarizationSign (first i)))
    (cost : ℕ → ℕ) (hcost : ∀ i, i + 1 < n → cost (i + 1) ≤ cost i) :
    (∑ i ∈ Finset.range n, (2 + 2 ^ i) * cost i) ≤
      ∑ i ∈ Finset.range n,
        ((prepare ++ traverse ++ restore).map (fun call => call.1.val)).count i * cost i := by
  apply gray_schedule_cost_bound n cost _ hcost
  intro j hj
  rw [← schedule_prefix_counts]
  exact schedule_prefix_bound h2 hj prepare traverse restore first last
    hprepare htraverse hrestore hvisit

end Toffoli
