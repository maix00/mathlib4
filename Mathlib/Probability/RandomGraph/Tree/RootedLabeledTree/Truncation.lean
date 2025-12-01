import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.Defs

open TreeNode ENNReal NNReal ENat Cardinal

namespace RLTree

variable {T T1 T2 : 𝕋₀} {n m : ℕ}

def truncation (T : 𝕋₀) (n : ℕ) : 𝕋₀ := ⟨{v | ‖v‖ₕ ≤ n ∧ v ∈ T}, by
    ext v; constructor
    · intro hv; simp only [Set.mem_setOf_eq]
      induction hv with
      | mem => assumption
      | tail m v' hv' ih =>
        exact ⟨by grind, mem_iff.2 <| T.generate_refl ▸ generateSet.tail m v'
          <| Eq.symm T.generate_refl ▸ mem_iff.1 ih.2⟩
      | less m v' hv' n hnm ih =>
        exact ⟨by grind, mem_iff.2 <| T.generate_refl ▸ generateSet.less m v'
          (Eq.symm T.generate_refl ▸ mem_iff.1 ih.2) n hnm⟩
    · intro hv; exact generateSet.mem v hv
    , by
      apply not_imp_not.2 Set.not_nonempty_iff_eq_empty.2; simp only [not_not]
      exact ⟨[], by simp [*]⟩
  ⟩

scoped[RLTree] notation T "↾(" n ")" => @truncation T n

@[simp] lemma truncation_zero : T↾(0) = ⊥ := by
  simp only [truncation, nonpos_iff_eq_zero, List.length_eq_zero_iff, rootTree_bot, rootTree_eq,
    mk.injEq]; congr; ext v; constructor
  · intro h; rw [h.1]; rfl
  · intro h; simp [Set.mem_singleton_iff.1 h]

lemma truncation_height_at_most (n : ℕ) : ‖T↾(n)‖ₕ ≤ n := by
  simp only [height, truncation]; apply @iSup₂_le (WithTop ℕ); intro v hv
  exact ENat.coe_le_coe.2 hv.1

@[simp] lemma truncation_mem_length_at_most (n : ℕ) : ∀ v ∈ T↾(n), ‖v‖ₕ ≤ n := by
  intro v hv; have := le_trans (mem_length_at_most_height v hv) (@truncation_height_at_most T n)
  simp only [Nat.cast_le] at this; exact this

@[simp] lemma truncation_truncation : T↾(n)↾(m) = T↾(min n m) := by
  simp [truncation, mem_iff]; grind

@[simp] lemma mem_of_mem_truncation {n : ℕ} {v : 𝕍} (hv : v ∈ T↾(n)) : v ∈ T := hv.2

@[simp] lemma truncation_subset {n : ℕ} : T↾(n) ⊆ T := by
  dsimp [instHasSubset]; simp only [Set.subset_def]; exact @mem_of_mem_truncation T n

@[simp] lemma mem_higher_truncation_of_mem_truncation (hnm : n < m) {v : 𝕍} (hv : v ∈ T↾(n)) :
  v ∈ T↾(m) := by simp only [truncation, mem_iff, Set.mem_setOf_eq] at *; exact ⟨by omega, hv.2⟩

@[simp] lemma mem_truncation_of_mem {n : ℕ} {v : 𝕍} (hv : ‖v‖ₕ ≤ n) (hv' : v ∈ T) : v ∈ T↾(n) := by
  simp only [mem_iff, truncation, Set.mem_setOf_eq] at *; exact ⟨by omega, hv'⟩

@[simp] lemma mem_truncation_of_mem_other_truncation {v : 𝕍} (hv : ‖v‖ₕ ≤ n)
  (hv' : v ∈ T↾(m)) : v ∈ T↾(n) := by
  simp only [truncation, mem_iff, Set.mem_setOf_eq] at *; exact ⟨by omega, hv'.2⟩

lemma ext_of_truncation (h : ∀ n, T1↾(n) = T2↾(n)) : T1 = T2 := by
  apply ext_of_set; ext v; cases v with
  | nil => constructor <;> intro <;> exact nil_mem
  | cons m v' =>
    have := set_eq_of_eq <| h (‖v'‖ₕ + 1); simp only [truncation, setOf] at this
    have := congr this (@rfl _ (m :: v')); simpa

@[simp] lemma finite_truncation_of_finite {T : 𝕋₀} (hT : Set.Finite T.set) (n : ℕ) :
  Set.Finite (T↾(n)).set := by
  have := @truncation_subset T n; simp only [instHasSubset] at this
  have : (T.set \ (T.set \ (T↾(n)).set)) = (T↾(n)).set := by simp [*]
  exact this ▸ @Finite.Set.finite_diff _ T.set (T.set \ (T↾(n)).set) hT

end RLTree
