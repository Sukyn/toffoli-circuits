import Toffoli.Universality.AffineSwapLiftMem
import Toffoli.Universality.AffineSwapConjugateMem
import Toffoli.Universality.RegisterTargetSwap
import Toffoli.Universality.CoordinateGeneration

namespace Toffoli
open scoped Classical

/-- If the controls already form a universal register, the larger register
can permute either factor independently. Affine wire exchanges move the
distinguished target gate onto a control wire for the induction hypothesis. -/
theorem product_register_generation {R : Type*} [CommRing R] [DecidableEq R]
    {n : ℕ} (hn : 0 < n)
    (hone : affineSwapGroup R (Equiv.swap (0 : R) 1) = ⊤)
    (hcontrols : affineSwapGroup R
      (coordinatePermutation (⟨0, hn⟩ : Fin n) (Equiv.swap (0 : R) 1)) = ⊤) :
    (∀ σ : Equiv.Perm (Controls R n),
      Equiv.prodCongr σ (Equiv.refl R) ∈
        affineSwapGroup R (targetSwap (C := Controls R n) (K := R))) ∧
    (∀ σ : Equiv.Perm R,
      Equiv.prodCongr (Equiv.refl (Controls R n)) σ ∈
        affineSwapGroup R (targetSwap (C := Controls R n) (K := R))) := by
  cases Subsingleton.elim ‹DecidableEq R› (Classical.decEq R)
  let C := Controls R n
  let G := affineSwapGroup R (targetSwap (C := C) (K := R))
  let left : Equiv.Perm C →* Equiv.Perm (C × R) :=
    { toFun := fun σ => Equiv.prodCongr σ (Equiv.refl R)
      map_one' := by ext x : 1; rfl
      map_mul' := by intro σ τ; ext x : 1; rfl }
  let right : Equiv.Perm R →* Equiv.Perm (C × R) :=
    { toFun := fun σ => Equiv.prodCongr (Equiv.refl C) σ
      map_one' := by ext x : 1; rfl
      map_mul' := by intro σ τ; ext x : 1; rfl }
  have affine_mem (e : (C × R) ≃ᵃ[R] (C × R)) : e.toEquiv ∈ G :=
    Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)
  have target_mem : right (Equiv.swap (0 : R) 1) ∈ G :=
    Subgroup.subset_closure (Or.inr rfl)
  have control_mem : left (coordinatePermutation (⟨0, hn⟩ : Fin n)
      (Equiv.swap (0 : R) 1)) ∈ G := by
    let i : Fin n := ⟨0, hn⟩
    have h := coordinate_generation (0 : Fin (n + 1)) i.succ
      (Equiv.swap (0 : R) 1) (Equiv.swap (0 : R) 1) hone
    have htransport := affine_swap_conjugate_mem (registerJoin (K := R) n).symm
      (coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : R) 1)) _ h
    rw [register_target_swap] at htransport
    have hcontrol : (registerJoin (K := R) n).symm.toEquiv.permCongr
        (coordinatePermutation i.succ (Equiv.swap (0 : R) 1)) =
        left (coordinatePermutation i (Equiv.swap (0 : R) 1)) := by
      ext ⟨x, t⟩ : 1
      apply Prod.ext
      · funext j
        change coordinatePermutation i.succ (Equiv.swap (0 : R) 1)
          (Fin.cons t x) j.succ = coordinatePermutation i (Equiv.swap (0 : R) 1) x j
        simp [coordinate_permutation_apply]
      · change coordinatePermutation i.succ (Equiv.swap (0 : R) 1) (Fin.cons t x) 0 = t
        simp [coordinate_permutation_apply, (Fin.succ_ne_zero i).symm]
    rwa [hcontrol] at htransport
  constructor
  · intro σ
    exact affine_swap_lift_mem _ hcontrols left G
      (fun e => affine_mem (e.prodCongr (AffineEquiv.refl R R))) control_mem σ
  · intro σ
    exact affine_swap_lift_mem _ hone right G
      (fun e => affine_mem ((AffineEquiv.refl R C).prodCongr e)) target_mem σ

end Toffoli
