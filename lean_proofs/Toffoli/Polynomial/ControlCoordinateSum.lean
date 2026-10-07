import Toffoli.Additions.CircuitZeroSumField
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators

namespace Toffoli

/-- Each coordinate sums to zero over all control inputs. Splitting off that
coordinate reduces the claim to the one-variable finite-field power sum. -/
theorem control_coordinate_sum {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) {n : ℕ} (i : Fin n) :
    (∑ x : Fin n → K, x i) = 0 := by
  classical
  change (∑ x, ((Equiv.funSplitAt i K) x).1) = 0
  rw [(Equiv.funSplitAt i K).sum_comp Prod.fst, Fintype.sum_prod_type_right]
  simp [finite_field_sum_id hcard]

end Toffoli
