import Toffoli.Universality.AccumulatorPermutationModel
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Transvection.Basic

namespace Toffoli
open scoped Classical

/-- Arbitrary control permutations turn a SUM into a two-point transfer.
First arrange that its source is zero at `a` and one at `b`; comparing
that addition before and after swapping `a,b` gives increments `+1,-1`.
Only affine maps and the supplied control permutations are used; the ring
need not be commutative. -/
theorem balanced_addition_from_control_permutations {R : Type*} [Ring R]
    [Nontrivial R] [DecidableEq R] {n : ℕ} (hn : 0 < n)
    (G : Subgroup (Equiv.Perm ((Fin n → R) × R)))
    (hcontrol : ∀ σ : Equiv.Perm (Fin n → R),
      Equiv.prodCongr σ (Equiv.refl R) ∈ G)
    (haffine : ∀ e : ((Fin n → R) × R) ≃ᵃ[R] ((Fin n → R) × R), e.toEquiv ∈ G)
    (a b : Fin n → R) (hab : a ≠ b) :
    targetAddition (fun x =>
      (if x = a then (1 : R) else 0) - (if x = b then 1 else 0)) ∈ G := by
  classical
  let C := Fin n → R
  let i : Fin n := ⟨0, hn⟩
  let u : C := fun _ => 0
  let v : C := fun _ => 1
  have huv : u ≠ v := fun h => zero_ne_one (congrFun h i)

  -- A permutation sends the chosen pair to the constant zero and one states.
  obtain ⟨σ, hσa, hσb⟩ : ∃ σ : Equiv.Perm C, σ a = u ∧ σ b = v :=
    MulAction.is_two_pretransitive_iff.mp
      (Equiv.Perm.isMultiplyPretransitive C 2) hab huv
  let h : C → R := fun x => σ x i
  have ha : h a = 0 := by simp [h, hσa, u]
  have hb : h b = 1 := by simp [h, hσb, v]

  -- The original SUM is a transvection on the control-target product.
  have hsum : targetAddition (fun x : C => x i) ∈ G := by
    let source : (C × R) →ₗ[R] R :=
      (LinearMap.proj i).comp (LinearMap.fst R C R)
    let e : (C × R) ≃ᵃ[R] (C × R) :=
      (LinearEquiv.transvection (f := source) (v := (0, 1))
        (by rfl)).toAffineEquiv
    have he : e.toEquiv = targetAddition (fun x : C => x i) := by
      ext ⟨x, t⟩ : 1
      change (x, t) + source (x, t) • (0, 1) = (x, t + x i)
      simp [source]
    rw [← he]
    exact haffine e
  let lift (τ : Equiv.Perm C) := Equiv.prodCongr τ (Equiv.refl R)
  have hadd : targetAddition h ∈ G := by
    have he : (lift σ)⁻¹ * targetAddition (fun x : C => x i) * lift σ =
        targetAddition h := by
      ext ⟨x, t⟩ : 1
      simp [lift, targetAddition, Equiv.Perm.mul_apply, h]
    rw [← he]
    exact G.mul_mem (G.mul_mem (G.inv_mem (hcontrol σ)) hsum) (hcontrol σ)

  -- The commutator restores the control and vanishes off the chosen pair.
  let swap := lift (Equiv.swap a b)
  have hswap : swap ∈ G := hcontrol _
  have he : swap * targetAddition h * swap⁻¹ * (targetAddition h)⁻¹ =
      targetAddition (fun x =>
        (if x = a then (1 : R) else 0) - (if x = b then 1 else 0)) := by
    ext ⟨x, t⟩ : 1
    by_cases hxa : x = a
    · subst x
      simp [swap, lift, targetAddition, Equiv.Perm.mul_apply, hab, ha, hb]
    · by_cases hxb : x = b
      · subst x
        simp [swap, lift, targetAddition, Equiv.Perm.mul_apply, hab.symm, ha, hb]
      · have hsx : Equiv.swap a b x = x := Equiv.swap_apply_of_ne_of_ne hxa hxb
        simp [swap, lift, targetAddition, Equiv.Perm.mul_apply, hxa, hxb, hsx]
  rw [← he]
  exact G.mul_mem (G.mul_mem (G.mul_mem hswap hadd) (G.inv_mem hswap)) (G.inv_mem hadd)

end Toffoli
