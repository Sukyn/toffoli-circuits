import Toffoli.Additions.CycleFamily
import Toffoli.Additions.CycleListingLabels
import Mathlib.Tactic.Choose

namespace Toffoli
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Mathlib's disjoint cycle factors give ordered lists covering exactly the
moved points. Reversing the factors matches the circuit's execution order. -/
theorem exists_nontrivial_cycle_listing (σ : Equiv.Perm α) :
    ∃ cycles : List (List α), cycles.flatten.Nodup ∧
      (∀ x, x ∈ cycles.flatten ↔ x ∈ σ.support) ∧
      cycleFamilyPermutation cycles = σ ∧
      (∀ labels ∈ cycles, labels ≠ []) ∧
      (∀ labels ∈ cycles, σ.IsCycleOn {x | x ∈ labels}) := by
  classical
  obtain ⟨factors, hp, hc, hd⟩ := σ.truncCycleFactors.out
  have hfset : σ.cycleFactorsFinset = factors.toFinset :=
    (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset
      (Equiv.Perm.nodup_of_pairwise_disjoint_cycles hc hd)).mpr ⟨hc, hd, hp⟩
  -- Each factor has an ordered list of exactly its moved points.
  choose hnodup hnonempty hform hsupport using
    (fun g hg => cycleLabels_spec g (hc g hg))
  have hfactor (g : Equiv.Perm α) : g ∈ factors ↔ g ∈ σ.cycleFactorsFinset := by
    simp [hfset]
  have hmap : factors.map (fun g => (cycleLabels g).formPerm) = factors := by
    simpa using (List.map_congr_left hform :
      factors.map (fun g => (cycleLabels g).formPerm) = factors.map id)
  refine ⟨factors.reverse.map cycleLabels, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_flatten]
    constructor
    · simpa only [List.forall_mem_map, List.mem_reverse] using hnodup
    · rw [List.pairwise_map]
      have hdr : factors.reverse.Pairwise Equiv.Perm.Disjoint :=
        hd.reverse.imp (fun h => h.symm)
      apply hdr.imp_of_mem
      intro g h hg hh hdis
      apply List.disjoint_left.mpr
      intro x hx hy
      exact hdis.mem_imp
        ((hsupport g (List.mem_reverse.mp hg) x).mp hx)
        ((hsupport h (List.mem_reverse.mp hh) x).mp hy)
  · intro x
    simp only [List.mem_flatten, List.mem_map, List.mem_reverse]
    constructor
    · rintro ⟨labels, ⟨g, hg, rfl⟩, hx⟩
      apply (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).mpr
      exact ⟨g, (hfactor g).mp hg, (hsupport g hg x).mp hx⟩
    · intro hx
      obtain ⟨g, hg, hxg⟩ :=
        Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hx
      have hgf : g ∈ factors := (hfactor g).mpr hg
      exact ⟨cycleLabels g, ⟨g, hgf, rfl⟩,
        (hsupport g hgf x).mpr hxg⟩
  · simpa [cycleFamilyPermutation, List.map_map, ← List.map_reverse, Function.comp_def, hmap] using hp
  · simpa only [List.forall_mem_map, List.mem_reverse] using hnonempty
  · intro labels hl
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
    have hgf : g ∈ factors := List.mem_reverse.mp hg
    have hset : {x | x ∈ cycleLabels g} = (g.support : Set α) := by
      ext x
      exact hsupport g hgf x
    rw [hset]
    exact Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset
      ((hfactor g).mp hgf)

end Toffoli
