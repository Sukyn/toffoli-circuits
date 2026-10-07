import Toffoli.Foundations.IndexedTargetModel

namespace Toffoli

/-- An update cannot change a control excluded from its destination. -/
theorem indexed_target_add_control {K : Type*} [Add K] {n : ℕ}
    (target : IndexedTarget n) (amount : K) (x : Controls K n) (t : K)
    (i : Fin n) (hti : target ≠ some i) :
    (indexedTargetAdd target amount (x, t)).1 i = x i := by
  cases target with
  | none => rfl
  | some j =>
    have hji : j ≠ i := by simpa using hti
    simp [indexedTargetAdd, hji.symm]

end Toffoli
