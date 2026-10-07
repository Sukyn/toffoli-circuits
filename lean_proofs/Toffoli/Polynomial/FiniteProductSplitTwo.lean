import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Toffoli

/-- Separate two distinct factors from a finite product. The remaining
product omits both coordinates, so it is independent of their values. -/
theorem finite_product_split_two {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ι → M) (i j : ι)
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    (∏ k ∈ s, f k) = f i * f j * ∏ k ∈ (s.erase i).erase j, f k := by
  have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  calc
    (∏ k ∈ s, f k) = f i * ∏ k ∈ s.erase i, f k :=
      (Finset.mul_prod_erase s f hi).symm
    _ = f i * (f j * ∏ k ∈ (s.erase i).erase j, f k) := by
      rw [Finset.mul_prod_erase (s.erase i) f hj']
    _ = _ := (mul_assoc _ _ _).symm

end Toffoli
