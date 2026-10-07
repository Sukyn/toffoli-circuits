import Toffoli.Mixed.MixedModel
import Toffoli.Foundations.IndexedTargetModel

namespace Toffoli

/-- Place a mixed ladder on an available wire pool. The control groups
partition the parent controls; each intervening dirty wire is distinct and
comes from the rest of the pool. No wire outside the pool is assigned. -/
structure MixedLadderLayout {n d b : ℕ} (L : MixedLadder d b)
    (controls pool : Finset (Fin n)) where
  controls_subset : controls ⊆ pool
  controls_card : controls.card = d
  pool_card : pool.card = d + b
  groups : Fin L.groups.length → Finset (Fin n)
  group_card : ∀ j, (groups j).card = L.groups.blocksFun j
  group_subset : ∀ j, groups j ⊆ controls
  groups_disjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))
  groups_cover : Finset.univ.biUnion groups = controls
  dirty : Fin (L.groups.length - 1) ↪ Fin n
  dirty_mem : ∀ j, dirty j ∈ pool \ controls

namespace MixedLadderLayout

variable {n d b : ℕ} {L : MixedLadder d b} {controls pool : Finset (Fin n)}

/-- The first call uses its group alone. Each later call also reads the
preceding dirty accumulator. -/
def callControls (layout : MixedLadderLayout L controls pool)
    (j : Fin L.groups.length) : Finset (Fin n) :=
  if hfirst : j.val = 0 then layout.groups j
  else insert (layout.dirty ⟨j.val - 1, by have := j.isLt; omega⟩) (layout.groups j)

/-- Internal calls exclude their dirty destination. The last call updates
the parent target and can use the entire parent pool. -/
def callPool (layout : MixedLadderLayout L controls pool)
    (j : Fin L.groups.length) : Finset (Fin n) :=
  if hlast : j.val + 1 = L.groups.length then pool
  else pool.erase (layout.dirty ⟨j.val, by have := j.isLt; omega⟩)

/-- Every call except the last updates its own dirty accumulator.
The last call updates the parent target. -/
def callTarget (layout : MixedLadderLayout L controls pool)
    (target : IndexedTarget n) (j : Fin L.groups.length) : IndexedTarget n :=
  if hlast : j.val + 1 = L.groups.length then target
  else some (layout.dirty ⟨j.val, by have := j.isLt; omega⟩)

end MixedLadderLayout
end Toffoli
