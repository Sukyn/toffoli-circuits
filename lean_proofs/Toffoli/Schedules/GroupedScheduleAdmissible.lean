import Toffoli.Schedules.GroupProductsIndependent
import Toffoli.Schedules.GroupedScheduleModel

namespace Toffoli
open scoped BigOperators

/-- The register's current value: its original value plus the group increments.
The original value can be any fixed function of the inputs. -/
def groupScheduleValue {K W : Type*} [CommSemiring K] {n : ℕ}
    (groups : Fin n → Finset W) (base : (W → K) → K) (state : Fin n → K) :
    (W → K) → K :=
  fun x => base x + ∑ i, state i * ∏ j ∈ groups i, x j

/-- Conditions on the actual register functions imply the coefficient-schedule
conditions. Disjoint nonempty groups make their coefficients observable, even
when intermediate coefficients are arbitrary. Preparation and restoration are
tested on the states actually produced by the preceding calls. -/
theorem grouped_schedule_admissible {K W : Type*} [CommRing K] {n : ℕ}
    (groups : Fin n → Finset W)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hnonempty : ∀ i, (groups i).Nonempty) (base : (W → K) → K)
    (prepare traverse restore : List (ScheduleCall K n)) (first last : GrayWord n)
    (hprepare : groupScheduleValue groups base (prepare.foldl scheduleStep 0) =
      groupScheduleValue groups base (fun i => polarizationSign (first i)))
    (htraverse : groupScheduleValue groups base
      (traverse.foldl scheduleStep (prepare.foldl scheduleStep 0)) =
      groupScheduleValue groups base (fun i => polarizationSign (last i)))
    (hrestore : groupScheduleValue groups base
      (restore.foldl scheduleStep (traverse.foldl scheduleStep
        (prepare.foldl scheduleStep 0))) = base)
    (hvisit : ∀ word : GrayWord n, ∃ state ∈
      traverse.scanl scheduleStep (prepare.foldl scheduleStep 0),
      groupScheduleValue groups base state =
        groupScheduleValue groups base (fun i => polarizationSign (word i))) :
    ScheduleAdmissible prepare traverse restore first last := by
  have hinjective : Function.Injective (groupScheduleValue groups base) := by
    intro a b hab
    apply group_products_independent groups hdisjoint hnonempty
    funext x
    exact add_left_cancel (congrFun hab x)
  have hzero : groupScheduleValue groups base (0 : Fin n → K) = base := by
    funext x
    simp [groupScheduleValue]
  have hp := hinjective hprepare
  refine ⟨hp, ?_, ?_, ?_⟩
  · simpa [hp] using hinjective htraverse
  · simpa [hp] using hinjective (hrestore.trans hzero.symm)
  · intro word
    obtain ⟨state, hmem, heq⟩ := hvisit word
    simpa [hp, hinjective heq] using hmem

end Toffoli
