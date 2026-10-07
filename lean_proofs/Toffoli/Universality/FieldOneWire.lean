import Toffoli.Universality.AffineSwapModel
import Toffoli.Additions.LocalSwapConjugacy
import Mathlib.GroupTheory.Perm.Sign

namespace Toffoli
open scoped Classical

/-- On a finite field, affine relabelling turns the fixed swap into every
transposition. Mathlib's generation theorem then gives all permutations.
No restriction on the field's characteristic or cardinality is needed. -/
theorem field_one_wire {K : Type*} [Field K] [Finite K] :
    affineSwapGroup K (Equiv.swap (0 : K) 1) = ⊤ := by
  let G := affineSwapGroup K (Equiv.swap (0 : K) 1)
  have affine_mem (e : K ≃ᵃ[K] K) : e.toEquiv ∈ G :=
    Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)
  have fixed_mem : Equiv.swap (0 : K) 1 ∈ G :=
    Subgroup.subset_closure (Or.inr rfl)
  change G = ⊤
  apply top_unique
  rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro _ ⟨a, b, hab, rfl⟩

  -- Affine conjugacy supplies each transposition from the fixed swap.
  let e := affineRelabel a b hab
  have hconjugate := G.mul_mem (G.mul_mem (affine_mem e) fixed_mem)
    (G.inv_mem (affine_mem e))
  simpa only [e, ← localSwap_conjugacy a b hab] using hconjugate

end Toffoli
