import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Toffoli

/-- Multiplying disjoint groups and the reserved control gives precisely the
original product. This identity depends only on the partition of the wires. -/
theorem divide_layout_product {K : Type*} {W : Type*} {I : Type*}
    [CommMonoid K] [DecidableEq W]
    [Fintype I] (controls : Finset W) {first : W} (hfirst : first ∈ controls)
    (groups : I → Finset W)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hcover : Finset.univ.biUnion groups = controls.erase first) (x : W → K) :
    x first * (∏ i, ∏ j ∈ groups i, x j) = ∏ j ∈ controls, x j := by
  have hproduct : (∏ i, ∏ j ∈ groups i, x j) =
      ∏ j ∈ controls.erase first, x j := by
    rw [← hcover, Finset.prod_biUnion (fun i _ j _ hij => hdisjoint hij)]
  rw [hproduct]
  exact Finset.mul_prod_erase controls x hfirst

end Toffoli
