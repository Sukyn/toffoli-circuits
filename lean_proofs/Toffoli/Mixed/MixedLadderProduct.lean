import Toffoli.Mixed.MixedLadderLayoutModel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Toffoli

/-- The allocated groups partition the controls, so their products multiply
to the original control product. Dirty wires do not enter this identity. -/
theorem mixed_ladder_product {K : Type*} [CommMonoid K] {n d b : ℕ}
    {L : MixedLadder d b} {controls pool : Finset (Fin n)}
    (layout : MixedLadderLayout L controls pool) (x : Fin n → K) :
    (∏ j, ∏ i ∈ layout.groups j, x i) = ∏ i ∈ controls, x i := by
  calc
    _ = ∏ i ∈ Finset.univ.biUnion layout.groups, x i :=
      (Finset.prod_biUnion (fun i _ j _ hij => layout.groups_disjoint hij)).symm
    _ = ∏ i ∈ controls, x i :=
      congrArg (fun s : Finset (Fin n) => ∏ i ∈ s, x i) layout.groups_cover

end Toffoli
