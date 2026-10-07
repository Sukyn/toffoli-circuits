import Toffoli.Additions.CycleAmounts

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- Record the prefix-sum amount used by the existing constructive algorithm. -/
noncomputable def canonicalTransferAmounts (a : K) : List K → (K → K) → K → K
  | [], _ => fun _ => 0
  | b :: rest, f => Function.update
      (canonicalTransferAmounts a rest (Function.update f a (f a + f b))) b (-f a)

/-- Disjoint cycles select their own table; amounts at unused labels are zero. -/
noncomputable def canonicalFamilyAmounts : List (List K) → (K → K) → K → K
  | [], _ => fun _ => 0
  | [] :: rest, f => canonicalFamilyAmounts rest f
  | (a :: labels) :: rest, f => fun x =>
      if x ∈ a :: labels then canonicalTransferAmounts a labels f x
      else canonicalFamilyAmounts rest f x

end Toffoli
