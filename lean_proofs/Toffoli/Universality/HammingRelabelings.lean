import Mathlib.InformationTheory.Hamming

namespace Toffoli

/-- Independent label permutations and a permutation of the wires preserve
Hamming distance: relabeling preserves inequality, and reindexing preserves
the number of coordinates where the two states differ. -/
theorem hamming_relabelings {I A : Type*} [Fintype I] [DecidableEq A]
    (σ : Equiv.Perm I) (e : I → Equiv.Perm A) (x y : I → A) :
    hammingDist (fun i => e i (x (σ i))) (fun i => e i (y (σ i))) =
      hammingDist x y := by
  calc
    _ = hammingDist (fun i => x (σ i)) (fun i => y (σ i)) :=
      hammingDist_comp (fun i => e i) (fun i => (e i).injective)
    _ = hammingDist x y := by
      unfold hammingDist
      exact Finset.card_equiv σ (fun i => by simp)

end Toffoli
