import Toffoli.Foundations.IndexedTargetModel

namespace Toffoli

/-- Successive increments of the same destination add their amounts. -/
theorem indexed_target_add_add {K : Type*} [AddSemigroup K] {n : ℕ}
    (target : IndexedTarget n) (a b : K) (state : Controls K n × K) :
    indexedTargetAdd target b (indexedTargetAdd target a state) =
      indexedTargetAdd target (a + b) state := by
  cases target <;> simp [indexedTargetAdd, add_assoc]

end Toffoli
