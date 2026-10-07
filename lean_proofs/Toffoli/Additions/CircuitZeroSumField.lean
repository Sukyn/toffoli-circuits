import Mathlib.FieldTheory.Finite.Basic

namespace Toffoli
open scoped BigOperators

/-- Mathlib's power-sum theorem at exponent one. The cardinality condition
also covers non-prime finite fields, including characteristic two. -/
theorem finite_field_sum_id {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) : (∑ x : K, x) = 0 := by
  simpa using FiniteField.sum_pow_lt_card_sub_one K 1 (by omega)

end Toffoli
