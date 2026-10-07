import Toffoli.Universality.AccumulatorPermutationModel
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

namespace Toffoli
open scoped Classical

/-- Two balanced additions and the target swap isolate a three-cycle.
The first commutator acts only over `a` and `b`. Commuting it with an
addition supported over `a` and `c` leaves only the three-cycle over `a`. -/
theorem localized_three_cycle {C : Type*} [Fintype C] [DecidableEq C]
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (a b c : C) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (G : Subgroup (Equiv.Perm (C × ZMod p)))
    (hs : targetSwap (C := C) (K := ZMod p) ∈ G)
    (hab_mem : targetAddition (fun x : C =>
      (if x = a then 1 else 0) - (if x = b then 1 else 0) : C → ZMod p) ∈ G)
    (hac_mem : targetAddition (fun x : C =>
      (if x = a then 1 else 0) - (if x = c then 1 else 0) : C → ZMod p) ∈ G) :
    ∃ g ∈ G, g.IsThreeCycle := by
  classical
  let lift : (C → Equiv.Perm (ZMod p)) →* Equiv.Perm (C × ZMod p) :=
    { toFun := Equiv.prodCongrRight
      map_one' := by ext x : 1; rfl
      map_mul' := by intro u v; ext x : 1; rfl }
  let s : C → Equiv.Perm (ZMod p) := fun _ => Equiv.swap 0 1
  let d : C → Equiv.Perm (ZMod p) := fun x =>
    Equiv.addRight ((if x = a then 1 else 0) - (if x = b then 1 else 0))
  let e : C → Equiv.Perm (ZMod p) := fun x =>
    Equiv.addRight ((if x = a then 1 else 0) - (if x = c then 1 else 0))
  let A := s * d * s⁻¹ * d⁻¹
  let B := A * e * A⁻¹ * e⁻¹
  have hs' : lift s ∈ G := by
    convert hs using 1
    ext ⟨x, t⟩ : 1
    simp [lift, s, targetSwap, Equiv.swap_apply_def]
    split_ifs <;> rfl
  have hA : lift A ∈ G := by
    change lift (s * d * s⁻¹ * d⁻¹) ∈ G
    simp only [map_mul, map_inv]
    exact G.mul_mem (G.mul_mem (G.mul_mem hs' hab_mem) (G.inv_mem hs'))
      (G.inv_mem hab_mem)
  have hB : lift B ∈ G := by
    change lift (A * e * A⁻¹ * e⁻¹) ∈ G
    simp only [map_mul, map_inv]
    exact G.mul_mem (G.mul_mem (G.mul_mem hA hac_mem) (G.inv_mem hA))
      (G.inv_mem hac_mem)

  -- On the surviving fiber, [S,T] = (0 1 2), and [[S,T],T] = (0 1 3).
  have small_ne (i j : ℕ) (hi : i < p) (hj : j < p) (hij : i ≠ j) :
      (i : ZMod p) ≠ (j : ZMod p) := by
    rw [ne_eq, ZMod.natCast_eq_natCast_iff']
    simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hij
  have h03 : (0 : ZMod p) ≠ 3 := by
    simpa only [Nat.cast_zero] using small_ne 0 3 (by omega) (by omega) (by decide)
  have h13 : (1 : ZMod p) ≠ 3 := by
    simpa only [Nat.cast_one] using small_ne 1 3 (by omega) (by omega) (by decide)
  have h23 : (2 : ZMod p) ≠ 3 := small_ne 2 3 (by omega) (by omega) (by decide)
  let T : Equiv.Perm (ZMod p) := Equiv.addRight 1
  let S : Equiv.Perm (ZMod p) := Equiv.swap 0 1
  let U : Equiv.Perm (ZMod p) := Equiv.swap 1 2
  let V : Equiv.Perm (ZMod p) := Equiv.swap 2 3
  have hshift01 : T * S * T⁻¹ = U := by
    simpa [T, S, U, one_add_one_eq_two] using (Equiv.swap_apply_apply T 0 1).symm
  have hshift12 : T * U * T⁻¹ = V := by
    simpa [T, U, V, one_add_one_eq_two, show (2 : ZMod p) + 1 = 3 by norm_num] using
      (Equiv.swap_apply_apply T 1 2).symm
  have hfirst : S * T * S⁻¹ * T⁻¹ = S * U := by
    simpa [S, mul_assoc] using congrArg (S * ·) hshift01
  have hconj : U * V * U = Equiv.swap 1 3 := by
    simpa only [U, V, Equiv.swap_inv, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne h13.symm h23.symm] using
      (Equiv.swap_apply_apply U 2 3).symm
  have hsecond : (S * T * S⁻¹ * T⁻¹) * T * (S * T * S⁻¹ * T⁻¹)⁻¹ * T⁻¹ =
      S * Equiv.swap 1 3 := by
    rw [hfirst]
    calc
      (S * U) * T * (S * U)⁻¹ * T⁻¹ =
          S * U * (T * U * T⁻¹) * (T * S * T⁻¹) := by
        simp only [S, U, mul_inv_rev, Equiv.swap_inv]
        group
      _ = S * (U * V * U) := by rw [hshift12, hshift01]; group
      _ = S * Equiv.swap 1 3 := by rw [hconj]
  have hrow : B = fun x => if x = a then S * Equiv.swap 1 3 else 1 := by
    funext x
    by_cases hxa : x = a
    · subst x
      simpa [B, A, s, d, e, hab, hac, S, T] using hsecond
    · by_cases hxb : x = b
      · subst x
        simp [B, A, e, hxa, hbc]
      · simp [B, A, s, d, hxa, hxb]
  have hlocal : lift B =
      Equiv.swap (a, 0) (a, 1) * Equiv.swap (a, 1) (a, 3) := by
    rw [hrow]
    ext ⟨x, t⟩ : 1
    by_cases hxa : x = a
    · subst x
      simp only [lift, Equiv.Perm.mul_apply, S, Equiv.swap_apply_def, Prod.mk.injEq, true_and]
      split_ifs <;> simp_all [Equiv.swap_apply_def]
    · simp [lift, hxa, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  refine ⟨lift B, hB, ?_⟩
  rw [hlocal, Equiv.swap_comm (a, 0) (a, 1)]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
    (by simp) (by simpa using h13) (by simpa using h03)

end Toffoli
