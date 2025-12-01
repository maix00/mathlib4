import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.Truncation

open TreeNode ENNReal NNReal ENat Cardinal

namespace RLTree

variable {T T1 T2 : 𝕋₀} {v : 𝕍}

-- ## LocallyFinite

protected def IsLocallyFinite (T : 𝕋₀) := ∀ n, Set.Finite (T↾(n)).set

protected structure LocallyFinite extends 𝕋₀ where
  locally_finite : RLTree.IsLocallyFinite toRLTree

scoped[RLTree.LocallyFinite] notation "𝕋" => RLTree.LocallyFinite

open LocallyFinite

instance : Coe 𝕋 𝕋₀ where
  coe T := T.toRLTree

protected def Finite := {T : 𝕋 // Set.Finite T.set}

scoped[RLTree.Finite] notation "𝕋ᵉ" => RLTree.Finite

-- namespace Finite

-- -- lemma finite_eq : 𝕋ᵉ = {T : 𝕋 // ‖T‖ₕ < ∞} := by sorry

-- end Finite

open Finite

lemma isLocallyFinite_iff_forall_truncation_finite :
  T.IsLocallyFinite ↔ ∀ n, Set.Finite (T↾(n)).set := by simp [RLTree.IsLocallyFinite]

lemma truncation_isLocallyFinite (hT : T.IsLocallyFinite) (n : ℕ) : T↾(n).IsLocallyFinite := by
  simp only [isLocallyFinite_iff_forall_truncation_finite, truncation_truncation] at ⊢ hT
  intro m; exact hT (min n m)

namespace LocallyFinite

def generateFinite (s : Set 𝕍) (hs : s ≠ ∅) (hs' : s.Finite) : 𝕋 := @mk (generateTree s hs) (by
    simp only [isLocallyFinite_iff_forall_truncation_finite]
    exact finite_truncation_of_finite <| finite_of_generate_finite hs hs')

lemma toRLTree_inj : Function.Injective @toRLTree := by
  intro T1 T2 h; cases T1; cases T2; simp only at h; cases h; rfl

lemma toRLTree_iff {T1 T2 : 𝕋} : T1.toRLTree = T2.toRLTree ↔ T1 = T2 :=
  ⟨@toRLTree_inj T1 T2, congrArg @toRLTree⟩

instance : Coe 𝕋 (Set 𝕍) where
  coe T := T.set

instance : Membership 𝕍 𝕋 where
  mem T v := v ∈ T.set

lemma mem_iff {v : 𝕍} {T : 𝕋} : v ∈ T ↔ v ∈ T.set := by constructor <;> intro h <;> exact h

instance : HasSubset 𝕋 where
  Subset T1 T2 := T1.set ⊆ T2.set

-- ## LocallyFinite.truncation

@[simp] def truncation (T : 𝕋) (n : ℕ) : 𝕋 := @mk (T.toRLTree↾(n))
  (truncation_isLocallyFinite T.locally_finite n)

scoped[RLTree.LocallyFinite] notation T "↾(" n ")" => @truncation T n

noncomputable instance instFintypeTruncate (T : 𝕋) (n : ℕ) :
  Fintype (T.toRLTree↾(n)).set := by
  exact @Fintype.ofFinite _ <| Set.finite_coe_iff.2 <| T.locally_finite n

end LocallyFinite

end RLTree
