import Toffoli.Universality.AccumulatorPermutationModel
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Group

namespace Toffoli
open scoped Classical

/-- Two balanced additions give three-cycles on pairs of control fibers.
Relabel the target so their supports meet in just one label; their commutator
then isolates one three-cycle on the common control fiber. This also works
in characteristic three. -/
theorem balanced_three_cycle {R C : Type*} [Ring R] [Fintype R]
    [DecidableEq R] [Nontrivial R] [Fintype C] [DecidableEq C]
    (htwo : (2 : R) ≠ 0) (hcard : 5 ≤ Fintype.card R)
    (a b c : C) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (G : Subgroup (Equiv.Perm (C × R)))
    (htarget : ∀ σ : Equiv.Perm R, Equiv.prodCongr (Equiv.refl C) σ ∈ G)
    (hab_mem : targetAddition (fun x : C =>
      (if x = a then 1 else 0) - (if x = b then 1 else 0) : C → R) ∈ G)
    (hac_mem : targetAddition (fun x : C =>
      (if x = a then 1 else 0) - (if x = c then 1 else 0) : C → R) ∈ G) :
    ∃ g ∈ G, g.IsThreeCycle := by
  classical
  have h12 : (1 : R) ≠ 2 := by
    intro h
    have : (1 : R) + 0 = 1 + 1 := by
      simpa only [add_zero, one_add_one_eq_two] using h
    exact zero_ne_one (add_left_cancel this)
  have hroom : 1 < (Finset.univ \ ({0, 1, 2} : Finset R)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have := (Finset.card_le_three (a := (0 : R)) (b := 1) (c := 2))
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hroom
  have hu' : u ≠ 0 ∧ u ≠ 1 ∧ u ≠ 2 := by simpa using hu
  have hv' : v ≠ 0 ∧ v ≠ 1 ∧ v ≠ 2 ∧ v ≠ u := by
    simpa [and_assoc] using And.intro hv huv.symm

  let S : Equiv.Perm R := Equiv.swap 0 1
  let T : Equiv.Perm R := Equiv.addRight 1
  let Q : Equiv.Perm R := Equiv.swap 1 u * Equiv.swap 2 v
  let α : Equiv.Perm R := Equiv.swap 0 1 * Equiv.swap 1 2
  let β : Equiv.Perm R := Equiv.swap 0 u * Equiv.swap u v
  have hQ0 : Q 0 = 0 := by
    simp only [Q, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne htwo.symm hv'.1.symm,
      Equiv.swap_apply_of_ne_of_ne zero_ne_one hu'.1.symm]
  have hQ1 : Q 1 = u := by
    simp only [Q, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne h12 hv'.2.1.symm, Equiv.swap_apply_left]
  have hQ2 : Q 2 = v := by
    simp only [Q, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hv'.2.1 hv'.2.2.2]
  have hbase : S * T * S⁻¹ * T⁻¹ = α := by
    have hshift : T * S * T⁻¹ = Equiv.swap 1 2 := by
      simpa [T, S, one_add_one_eq_two] using (Equiv.swap_apply_apply T 0 1).symm
    simpa [S, α, mul_assoc] using congrArg (S * ·) hshift
  have hconj : Q * α * Q⁻¹ = β := by
    calc
      Q * α * Q⁻¹ =
          (Q * Equiv.swap 0 1 * Q⁻¹) * (Q * Equiv.swap 1 2 * Q⁻¹) := by
        dsimp [α]
        group
      _ = β := by
        rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply, hQ0, hQ1, hQ2]
  have hα0 : α 0 = 1 := by
    simp only [α, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne zero_ne_one htwo.symm, Equiv.swap_apply_left]
  have hαu : α u = u := by
    simp only [α, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hu'.2.1 hu'.2.2,
      Equiv.swap_apply_of_ne_of_ne hu'.1 hu'.2.1]
  have hαv : α v = v := by
    simp only [α, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hv'.2.1 hv'.2.2.1,
      Equiv.swap_apply_of_ne_of_ne hv'.1 hv'.2.1]
  have hcomm : α * β * α⁻¹ * β⁻¹ = Equiv.swap 1 u * Equiv.swap 0 u := by
    calc
      α * β * α⁻¹ * β⁻¹ =
          (α * Equiv.swap 0 u * α⁻¹) * (α * Equiv.swap u v * α⁻¹) * β⁻¹ := by
        dsimp [β]
        group
      _ = Equiv.swap 1 u * Equiv.swap 0 u := by
        rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply, hα0, hαu, hαv]
        simp [β, mul_assoc]

  let lift : (C → Equiv.Perm R) →* Equiv.Perm (C × R) :=
    { toFun := Equiv.prodCongrRight
      map_one' := by ext x : 1; rfl
      map_mul' := by intro f g; ext x : 1; rfl }
  let s : C → Equiv.Perm R := fun _ => S
  let q : C → Equiv.Perm R := fun _ => Q
  let d : C → Equiv.Perm R := fun x =>
    Equiv.addRight ((if x = a then 1 else 0) - (if x = b then 1 else 0))
  let e : C → Equiv.Perm R := fun x =>
    Equiv.addRight ((if x = a then 1 else 0) - (if x = c then 1 else 0))
  let A := s * d * s⁻¹ * d⁻¹
  let B := q * (s * e * s⁻¹ * e⁻¹) * q⁻¹
  let L := A * B * A⁻¹ * B⁻¹
  have hs : lift s ∈ G := by
    simpa only [Equiv.prodCongr_refl_left] using htarget S
  have hq : lift q ∈ G := by
    simpa only [Equiv.prodCongr_refl_left] using htarget Q
  have comm_mem (f g : C → Equiv.Perm R) (hf : lift f ∈ G) (hg : lift g ∈ G) :
      lift (f * g * f⁻¹ * g⁻¹) ∈ G := by
    simp only [map_mul, map_inv]
    exact G.mul_mem (G.mul_mem (G.mul_mem hf hg) (G.inv_mem hf)) (G.inv_mem hg)
  have hA : lift A ∈ G := comm_mem s d hs hab_mem
  have hB : lift B ∈ G := by
    change lift (q * (s * e * s⁻¹ * e⁻¹) * q⁻¹) ∈ G
    rw [map_mul, map_mul, map_inv]
    exact G.mul_mem (G.mul_mem hq (comm_mem s e hs hac_mem)) (G.inv_mem hq)
  have hL : lift L ∈ G := comm_mem A B hA hB
  have hrow : L = fun x => if x = a then Equiv.swap 1 u * Equiv.swap 0 u else 1 := by
    funext x
    by_cases hxa : x = a
    · subst x
      have hd : d a = T := by simp [d, T, hab]
      have he : e a = T := by simp [e, T, hac]
      simpa only [L, A, B, Pi.mul_apply, Pi.inv_apply, s, q, hd, he,
        if_pos rfl, hbase, hconj] using hcomm
    · by_cases hxb : x = b
      · subst x
        simp [L, B, e, hxa, hbc]
      · simp [L, A, d, hxa, hxb]
  have hlocal : lift L =
      Equiv.swap (a, 1) (a, u) * Equiv.swap (a, 0) (a, u) := by
    rw [hrow]
    ext ⟨x, t⟩ : 1
    by_cases hxa : x = a
    · subst x
      simp only [lift, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Prod.mk.injEq, true_and]
      split_ifs <;> simp_all [Equiv.swap_apply_def]
    · simp [lift, hxa, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  refine ⟨lift L, hL, ?_⟩
  rw [hlocal, Equiv.swap_comm (a, 1) (a, u), Equiv.swap_comm (a, 0) (a, u)]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
    (by simpa using hu'.2.1) (by simpa using hu'.1) (by simp)

end Toffoli
