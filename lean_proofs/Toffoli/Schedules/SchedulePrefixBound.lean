import Toffoli.Schedules.ScheduleEndpointBound
import Toffoli.Schedules.ScheduleTraversalBound

namespace Toffoli

/-- Cut a schedule at its first and last evaluated signed sums. Preparation
and restoration each need j prefix calls; the intervening trace needs 2^j−1.
These cuts impose no restriction on repetitions or intermediate coefficients. -/
theorem schedule_prefix_bound {K : Type*} [CommRing K] [Nontrivial K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {n j : ℕ} (hj : j ≤ n)
    (prepare traverse restore : List (ScheduleCall K n)) (first last : Fin n → Bool)
    (hprepare : prepare.foldl scheduleStep 0 = fun i => polarizationSign (first i))
    (htraverse : traverse.foldl scheduleStep (fun i => polarizationSign (first i)) =
      fun i => polarizationSign (last i))
    (hrestore : restore.foldl scheduleStep
      (traverse.foldl scheduleStep (fun i => polarizationSign (first i))) = 0)
    (hvisit : ∀ word : Fin n → Bool,
      (fun i => polarizationSign (word i)) ∈
        traverse.scanl scheduleStep (fun i => polarizationSign (first i))) :
    2 * j + 2 ^ j - 1 ≤ schedulePrefixCalls j (prepare ++ traverse ++ restore) := by
  have hsign (b : Bool) : (polarizationSign b : K) ≠ 0 := by
    cases b <;> simp [polarizationSign]
  have hp := schedule_endpoint_bound hj prepare (0 : Fin n → K) (by
    intro i
    rw [hprepare]
    exact hsign (first (Fin.castLE hj i)))
  have hr := schedule_endpoint_bound hj restore
    (traverse.foldl scheduleStep (fun i => polarizationSign (first i))) (by
      intro i
      rw [hrestore, htraverse]
      exact (hsign (last (Fin.castLE hj i))).symm)
  have ht := schedule_traversal_bound h2 hj traverse _ hvisit
  simp only [schedulePrefixCalls, List.countP_append] at hp hr ht ⊢
  have hpositive : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

end Toffoli
