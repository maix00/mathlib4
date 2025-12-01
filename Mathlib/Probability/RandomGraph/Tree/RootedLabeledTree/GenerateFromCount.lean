import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.Children
import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.GenerationSize

open TreeNode ENNReal NNReal ENat Cardinal

namespace RLTree

variable (X : 𝕍 → ℕ)

def setFromCountChildren : Set 𝕍 :=
  {v | ∀ n, v.get n < X (v.drop (n + 1))}

@[simp] lemma generateSetFromCountChildren_id :
  generateSet (setFromCountChildren X) = setFromCountChildren X := by
  ext v; constructor
  · simp only [setFromCountChildren]
    intro hv
    rw [generateSet_eq_generate_tail_then_less {v | ∀ n, v.get n < X (v.drop (n + 1))}
      (by apply Ne.symm; apply Set.nonempty_iff_empty_ne.1; refine ⟨[], ?_⟩; simp)] at hv
    simp only [List.get_eq_getElem, Set.mem_setOf_eq]; by_cases hv' : v = []
    · grind
    · simp only [List.get_eq_getElem, Set.singleton_union, Set.mem_insert_iff, hv', false_or] at hv
      have := v.cons_head_tail hv'
      obtain ⟨m, hm, hm'⟩ := cons_mem_of_mem_generate_less _ (by simp) _ _ (this ▸ hv)
      simp only [generate_tail, Set.coe_setOf, Set.mem_setOf_eq, Set.mem_diff, Set.mem_iUnion,
        Subtype.exists, exists_prop, Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true,
        and_true] at hm'
      obtain ⟨u', hu'1, hu'2⟩ := hm'
      simp only [generate_tail_of_single, Set.iUnion_singleton_eq_range, Set.mem_range] at hu'2
      obtain ⟨m', hu'2⟩ := hu'2
      intro n
      specialize hu'1 ⟨n.val + m'.val, by
        have hu'3 := congrArg List.length hu'2; simp at hu'3; grind⟩
      simp only at hu'1
      have := (show m'.val + (n.val + 1) = n.val + m'.val + 1 from by omega)
        ▸ @List.drop_drop _ (n.val + 1) ↑m' u'
      rw [←this] at hu'1
      conv at hu'1 => right; congr; arg 2; rw [hu'2]
      have h₀ (k : ℕ) : (m :: v.tail).drop (k + 1) = v.drop (k + 1) := by simp
      conv at hu'1 => right; congr; rw [h₀ ↑n]
      by_cases hn : n = ⟨0, by grind⟩
      · rw [hn] at hu'1; simp only [zero_add, List.drop_one] at hu'1
        have : u'[m'.val]'(by grind) = m := by
          have := @List.getElem_drop _ u' ↑m' 0 (by grind)
          simp only [hu'2, List.getElem_cons_zero, add_zero] at this; exact Eq.symm this
        rw [this] at hu'1
        rw [hn]; simp [List.getElem_zero_eq_head]; grind
      · have : u'[n.val + m'.val]'(by grind) = v[n.val]'(by grind) := by
          have := @List.getElem_drop _ u' ↑m' ↑n (by grind)
          conv at this => left; arg 1; rw [hu'2]
          conv at this => right; arg 2; rw [Nat.add_comm]
          have h₀ : (m :: v.tail)[n.val]'(by grind) = v[n.val]'(by grind) := by
            rw [List.getElem_cons]; conv at hn => congr; rw [←Fin.val_inj]
            grind
          grind
        grind
  · intro hv; exact generateSet.mem v hv

def generateFromCountChildren : 𝕋₀ :=
  generateTree (setFromCountChildren X) (by
    rw [←Set.nonempty_iff_ne_empty]; exact ⟨[], by simp [setFromCountChildren]⟩)

lemma generateFromCountChildren_false_ge (u : 𝕍) (n : ℕ)
  (h : X u ≤ n) (h' : n :: u ∈ generateFromCountChildren X) : False := by
  simp only [generateFromCountChildren, generateTree, generateSetFromCountChildren_id,
    RLTree.mem_iff] at h'
  simp only [setFromCountChildren, List.get_eq_getElem, Set.mem_setOf_eq, List.length_cons,
    List.drop_succ_cons] at h'; specialize h' 0; simp at h'; grind

lemma generateFromCountChildren_less_mem (u : 𝕍) (n : ℕ)
  (h : n < X u) (hu : u ∈ setFromCountChildren X) : n :: u ∈ generateFromCountChildren X := by
  simp only [generateFromCountChildren, generateTree, generateSetFromCountChildren_id,
    RLTree.mem_iff];
  simp only [setFromCountChildren, List.get_eq_getElem, Set.mem_setOf_eq, List.length_cons,
    List.drop_succ_cons] at hu ⊢; intro ⟨m, hm⟩; by_cases h' : m = 0
  · simp [h', h]
  · specialize hu ⟨m - 1, by grind⟩; grind

instance instDecidableMemSetFromCountChildren (u : 𝕍) :
  Decidable (u ∈ setFromCountChildren X) := by
  simp only [setFromCountChildren, List.get_eq_getElem, Set.mem_setOf_eq]; infer_instance

lemma generateFromCountChildren_countChildren_eq (u : 𝕍) :
  ♯{generateFromCountChildren X, u→}ₑ = if u ∈ setFromCountChildren X then X u else 0 := by
  set T := generateFromCountChildren X with hT
  by_cases h : ♯{T, u→}ₑ = ⊤
  · exact False.elim <| generateFromCountChildren_false_ge X u (X u) (by omega)
      <| countChildren_eq_top_iff.1 h <| X u
  · have : ♯{T, u→}ₑ =
      ((♯{T, u→}ₑ).lift (WithTop.lt_top_iff_ne_top.2 h) : ℕ∞) := by simp
    rw [this]; apply ENat.coe_inj.2; apply Nat.eq_iff_le_and_ge.2
    simp only [RLTree.countChildren, lift_le_iff, Nat.cast_ite, CharP.cast_eq_zero,
      ENat.le_lift_iff]; constructor
    · apply @iSup₂_le (WithTop ℕ) ℕ (fun m => m :: u ∈ T) _ _
        (fun m => fun _ => ↑m + 1) ?_; intro m' hm'; simp only
      by_cases h'' : u ∈ setFromCountChildren X
      · by_contra h'; exact generateFromCountChildren_false_ge X u m' (by
        simp only [h'', ↓reduceIte, not_le] at h'
        rw[(show (m' : WithTop ℕ) + 1 = ↑(m' + 1) from by simp)] at h'
        have h' := WithTop.coe_lt_coe.1 h'; simp at h'; omega) hm'
      · simp only [h'', ↓reduceIte, nonpos_iff_eq_zero, add_eq_zero, Nat.cast_eq_zero, one_ne_zero,
        and_false];
        have := @tail_mem _ _ _ hm'
        simp [T, generateFromCountChildren, generateTree, RLTree.mem_iff] at this
        contradiction
    · by_cases h' : X u = 0 ∨ u ∉ setFromCountChildren X
      · have : (if u ∈ setFromCountChildren X then (X u : ℕ∞) else 0) = 0 := by
          simp only [ite_eq_right_iff, Nat.cast_eq_zero]; intro h; grind
        simp [this]
      · simp only [not_or, Decidable.not_not] at h'
        have : (if u ∈ setFromCountChildren X then (X u : ℕ∞) else 0) = X u := by simp [h'.2]
        rw [this]
        conv => left; congr; rw [(show X u = X u - 1 + 1 from by omega)]
        conv => left; simp only [Nat.cast_add, Nat.cast_one]
        apply countChildren_ge
        exact generateFromCountChildren_less_mem X u (X u - 1) (by omega) h'.2

lemma generateFromCountChildren_countChildren_le (u : 𝕍) :
  ♯{generateFromCountChildren X, u→}ₑ ≤ X u := by
  rw [generateFromCountChildren_countChildren_eq X u]; apply WithTop.coe_le_coe.2
  split_ifs <;> simp

namespace LocallyFinite

def generateFromCountChildren : 𝕋 :=
  let T := RLTree.generateFromCountChildren X; @mk T (by
    simp only [isLocallyFinite_iff_forall_truncation_finite]; intro n; induction n with
    | zero => simp
    | succ n ih =>
      simp only [truncation_succ]; refine Set.finite_union.2 ⟨ih, ?_⟩
      rw [←@Set.iUnion_subtype 𝕍 𝕍 (fun v => v ∈ 𝕍{T, n})
        (fun v => ⋃ m ∈ {m : ℕ | m + 1 ≤ ♯{T, v→}ₑ}, {m :: v})]
      refine @Set.finite_iUnion _ _ ?_ _ ?_
      · apply Set.finite_coe_iff.2; simp only [setOfLevel_as_seqDiff_truncation]
        apply Set.finite_coe_iff.1
        refine @Finite.Set.finite_diff _ _ _ ?_; apply Set.finite_coe_iff.2; exact ih
      · intro u; rw [←@Set.iUnion_subtype ℕ 𝕍
          (fun m => m ∈ {m : ℕ | m + 1 ≤ ♯{T, u→}ₑ}) (fun m => {m.val :: u.val})]
        refine @Set.finite_iUnion _ _ ?_ _ ?_
        · apply Set.finite_coe_iff.2
          have : {m : ℕ | ↑m + 1 ≤ ♯{T, ↑u→}ₑ} ⊆ {m : ℕ | ↑m + 1 ≤ ↑(X u)} := by
            have := generateFromCountChildren_countChildren_le X u
            simp only [Set.setOf_subset_setOf, T]
            intro n h; have := le_trans h this; apply WithTop.coe_le_coe.1
            simp only [WithTop.coe_add, ENat.some_eq_coe, WithTop.coe_one]; exact this
          refine Set.Finite.subset ?_ this; conv => congr; congr; ext m; rw[Nat.add_one_le_iff];
          simp [Set.finite_lt_nat]
        · intro; simp)

lemma generateFromCountChildren_countChildren_eq (u : 𝕍) :
  ♯{generateFromCountChildren X, u→} = if u ∈ setFromCountChildren X then X u else 0 := by
  simp only [countChildren]; apply ENat.coe_inj.1; simp [generateFromCountChildren,
    RLTree.generateFromCountChildren_countChildren_eq]

lemma generateFromCountChildren_countChildren_le (u : 𝕍) :
  ♯{generateFromCountChildren X, u→} ≤ X u := by
  simp only [countChildren, generateFromCountChildren, lift_le_iff]
  exact RLTree.generateFromCountChildren_countChildren_le _ _

lemma generateFromCountChildren_false_ge (u : 𝕍) (n : ℕ)
  (h : X u ≤ n) (h' : n :: u ∈ generateFromCountChildren X) : False := by
  simp only [generateFromCountChildren, mem_iff] at h';
  exact RLTree.generateFromCountChildren_false_ge _ _ _ h h'

lemma generateFromCountChildren_less_mem (u : 𝕍) (n : ℕ)
  (h : n < X u) (hu : u ∈ setFromCountChildren X) : n :: u ∈ generateFromCountChildren X := by
  simp only [generateFromCountChildren, mem_iff]
  exact RLTree.generateFromCountChildren_less_mem _ _ _ h hu

end LocallyFinite

end RLTree
