import Toffoli.Borrow.BorrowedLadderModel

namespace Toffoli

/-- An increment to the initial value propagates through the ordered product
of the factors, using only distributivity and associativity. -/
theorem borrowedPropagation_difference {K : Type*} [Semiring K]
    (middle : List (K × K)) (b delta : K) :
    borrowedPropagation (b + delta) middle =
      borrowedPropagation b middle + delta * (middle.map Prod.fst).prod := by
  induction middle generalizing b delta with
  | nil => simp [borrowedPropagation]
  | cons head rest ih =>
    rcases head with ⟨factor, dirty⟩
    simp only [borrowedPropagation, List.map_cons, List.prod_cons]
    -- At this stage, the increment becomes delta * factor.
    have hprepare : dirty + (b + delta) * factor =
        (dirty + b * factor) + delta * factor := by rw [add_mul, add_assoc]
    rw [hprepare, ih, mul_assoc]

end Toffoli
