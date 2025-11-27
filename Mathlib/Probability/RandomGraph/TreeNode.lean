import Mathlib.Probability.RandomGraph.Basic

-- ## TreeNode

@[reducible] def TreeNode := List ℕ

namespace TreeNode

instance : Coe TreeNode (List ℕ) where
  coe l := l

end TreeNode

namespace Set

variable {T : Type*} (seq : ℕ → Set T)

def seqDiff : ℕ → Set T := fun m =>
  Set.Accumulate seq m \ (if m = 0 then ∅ else Set.Accumulate seq (m - 1))

lemma seqDiff_def : seqDiff seq = fun m => if m = 0 then seq 0 else
  Set.Accumulate seq m \ Set.Accumulate seq (m - 1) := by
  unfold seqDiff; ext; split_ifs <;> simp only [diff_empty, mem_accumulate]; grind

lemma accumulate_of_mono (hseq : Monotone seq) : Set.Accumulate seq = seq := by
  ext m x; simp [Set.Accumulate]; constructor
  · intro ⟨n, hn, hn'⟩; exact Set.mem_of_subset_of_mem (hseq hn) hn'
  · intro; use m

lemma seqDiff_def_of_mono (hseq : Monotone seq) : seqDiff seq = fun m => if m = 0 then seq 0 else
  seq m \ seq (m - 1) := by simp only [seqDiff_def]; rwa [accumulate_of_mono]

lemma iUnion₂_le_succ (m : ℕ) :
  ⋃ n ≤ m + 1, seq n = (⋃ n ≤ m, seq n) ∪ seq (m + 1) := by
      ext; simp only [Set.mem_iUnion, exists_prop, Set.mem_union]; grind

lemma accumulate_eq_seqDiff_acculumate :
  Set.Accumulate seq = Set.Accumulate (Set.seqDiff seq) := by
  ext m x; constructor
  · intro hx; simp only [Set.Accumulate] at hx ⊢; induction m with
    | zero => simp at hx; simp [Set.seqDiff, *]
    | succ m ih =>
      rw [Set.iUnion₂_le_succ seq m] at hx
      rw [Set.iUnion₂_le_succ (Set.seqDiff seq) m]
      simp only [Set.mem_union] at hx ⊢
      by_cases hx' : x ∈ ⋃ n ≤ m, seq n
      · left; exact ih hx'
      · right; have hx := Or.resolve_left hx hx'; simp [Set.seqDiff]; constructor
        · use m + 1
        · simp at hx'; exact hx'
  · intro hx; simp only [Set.Accumulate] at hx ⊢; induction m with
    | zero => simp [Set.seqDiff] at hx; simp [*]
    | succ m ih =>
      rw [Set.iUnion₂_le_succ seq m]
      rw [Set.iUnion₂_le_succ (Set.seqDiff seq) m] at hx
      simp only [Set.mem_union] at hx ⊢
      by_cases hx' : x ∈ ⋃ n ≤ m, Set.seqDiff seq n
      · left; exact ih hx'
      · right; have hx := Or.resolve_left hx hx'; simp [Set.seqDiff] at hx
        obtain ⟨⟨n, hn, hn'⟩, hn''⟩ := hx
        exact (show n = m + 1 from by by_contra; exact hn'' n (by omega) hn') ▸ hn'

@[simp] lemma seqDiff_pairwise_disjoint :
  Pairwise (Function.onFun Disjoint (Set.seqDiff seq)) := by
  simp [pairwise_disjoint_on, Disjoint]; intro m n hmn x hxm hxn
  unfold Set.seqDiff at hxm; simp [Set.Accumulate] at hxm; induction m with
  | zero =>
    simp at hxm; cases n with
    | zero => contradiction
    | succ n =>
      simp [Set.seqDiff, Set.Accumulate, Set.subset_diff, Disjoint] at hxn
      exact @hxn.2 x (by simp) (by
        apply trans hxm; apply Set.subset_iUnion₂ (s := fun i => fun (_ : i ≤ n) => seq i) 0; omega)
  | succ m ih =>
    cases n with
    | zero => contradiction
    | succ n =>
      simp [Set.seqDiff, Set.Accumulate, Set.subset_diff, Disjoint] at hxn
      simp [Set.iUnion₂_le_succ seq m, Set.subset_diff] at hxm
      exact @hxn.2 x (by simp) (by
        apply trans hxm.1
        apply Set.subset_iUnion₂ (s := fun i => fun (_ : i ≤ n) => seq i) (m + 1); omega)

@[simp] lemma seqDiff_sigma_snd_injective : Function.Injective
  fun (x : Sigma (fun n => Set.seqDiff seq n)) => x.snd.val := by
  intro x1 x2 h12; simp at h12; ext
  · by_contra h; have h := Set.seqDiff_pairwise_disjoint seq h; simp [Disjoint] at h
    specialize @h {x1.snd.val} (by simp) (by simp [h12]); absurd h; simp
  · assumption

@[simp] lemma seqDiff_disjoint_of_mono (hseq : Monotone seq) {i j : ℕ} (hij : i < j) :
  Disjoint (seq i) (Set.seqDiff seq j) := by
  rw [←congr (Set.accumulate_of_mono seq hseq) (@rfl _ i),
    Set.accumulate_eq_seqDiff_acculumate]; exact Set.disjoint_accumulate (by simp) hij

@[simp] lemma seqDiff_finite_of_finite (hseq : ∀ n, Set.Finite (seq n)) (n : ℕ) :
  Set.Finite (Set.seqDiff seq n) := by
  simp [Set.seqDiff, Set.Accumulate]
  apply fun h => @Finite.Set.finite_diff _ _ _ h
  apply Set.finite_coe_iff.2
  have : ⋃ m, ⋃ (_ : m ≤ n), seq m = ⋃ (m : {m // m ≤ n}), seq ↑m := by
    ext; simp_all only [Set.mem_iUnion, exists_prop, Subtype.exists]
  rw [this]; apply Set.finite_iUnion; simp; intro m _; exact hseq m

noncomputable instance instFintypeSeqDiffOfFinite (hseq : ∀ n, Set.Finite (seq n))
  (n : ℕ) : Fintype ↑(Set.seqDiff seq n) := Set.Finite.fintype <| (by simp [*])

end Set

namespace TreeNode

def setOfLevel (n : ℕ) : Set TreeNode := {ν | ν.length = n}

def setOfLevelAtMost (n : ℕ) : Set TreeNode := {ν | ν.length ≤ n}

instance instCountableSetTreeNodeOfLength (n : ℕ) :
  Countable (setOfLevel n) := by
  simp [setOfLevel]; exact Subtype.countable

instance instCountableSetTreeNodeOfLengthAtMost (n : ℕ) :
  Countable (setOfLevelAtMost n) := by
  simp [setOfLevelAtMost]; exact Subtype.countable

lemma setOfLevelAtMost_eq_iUnion_finset_setOfLevel (n : ℕ) :
  setOfLevelAtMost n = ⋃ k : Finset.range (n + 1), setOfLevel k := by
  simp [setOfLevelAtMost, setOfLevel]; ext v; simp; omega

def setOfLevelOfValAtMost (n m : ℕ) : Set TreeNode :=
  ⋃ f : Fin n → Fin (m + 1), {(List.ofFn f).map Fin.val}

@[simp] lemma setOfLevelOfValAtMost_zero : setOfLevelOfValAtMost 0 = fun _ => {[]} := by
  ext; simp [setOfLevelOfValAtMost]

@[simp] lemma setOfLevelOfValAtMost_zero_seqDiff :
  Set.seqDiff (setOfLevelOfValAtMost 0) = fun m => if m = 0 then {[]} else ∅ := by
  simp; unfold Set.seqDiff; simp [Set.Accumulate]; ext m v; by_cases h : m = 0
  · simp [h]
  · conv => left; congr; arg 2; simp [h]
    conv => right; congr; simp [h]
    have (m : ℕ) : ⋃ y, ⋃ (_ : y ≤ m), {([] : List ℕ)} = {[]} := by ext; simp; intro; use 0; omega
    rw [this m, this (m - 1)]; simp

instance instFiniteSetTreeNodeOfLengthTruncated (n m : ℕ) :
  Set.Finite (setOfLevelOfValAtMost n m) := by
  simp only [setOfLevelOfValAtMost]; apply Finite.Set.finite_iUnion

noncomputable instance instFintypeSetTreeNodeOfLengthTruncated (n m : ℕ) :
  Fintype (setOfLevelOfValAtMost n m) :=
  Set.Finite.fintype <| instFiniteSetTreeNodeOfLengthTruncated n m

@[simp] lemma setOfLevelOfValAtMost_subset_setOfLevel (n m : ℕ) :
  setOfLevelOfValAtMost n m ⊆ setOfLevel n := by
  simp [Set.subset_def, setOfLevelOfValAtMost, setOfLevel]

@[simp] lemma setOfLevelOfValAtMost_mono (n : ℕ) :
  Monotone (setOfLevelOfValAtMost n) := by
  intro m1 m2 h12; simp [Set.subset_def, setOfLevelOfValAtMost]; intro f
  use Fin.castLE (show m1 + 1 ≤ m2 + 1 from by omega) ∘ f; ext; simp

@[simp] lemma setOfLevelOfValAtMost_union_eq_setOfLevel (n : ℕ) :
  ⋃ m : ℕ, setOfLevelOfValAtMost n m = setOfLevel n := by
  ext v; simp only [Set.mem_iUnion]; constructor
  · intro ⟨m, h⟩; exact Set.mem_of_subset_of_mem (by simp) h
  · intro h; by_cases h' : n = 0
    · simp [setOfLevel] at h
      have : v = [] := List.eq_nil_iff_length_eq_zero.2 <| h' ▸ h
      use 0; simp [setOfLevelOfValAtMost, *]
    · simp only [setOfLevel, Set.mem_setOf_eq] at h
      set m := v.max? with hm
      have : ∃ m', m = some m' := by
        match v with
        | [] => absurd h; simp; exact Ne.symm h'
        | n' :: v' => simp only [List.max?_cons] at hm; simp only [hm, Option.some.injEq,
          exists_eq']
      obtain ⟨m', hm'⟩ := this; use m'; simp [setOfLevelOfValAtMost]
      use fun ⟨i, hi⟩ => ⟨v[i], by
        have := List.le_max?_get_of_mem (show v[i] ∈ v from by simp)
        conv at this => right; congr; simp [←(hm' ▸ hm)]
        simp at this; omega⟩; simp only; conv => congr; congr; ext i; simp
      ext; aesop

instance instFiniteSetTreeNodeOfLengthTruncatedSeqDiff (n m : ℕ) :
  Set.Finite (Set.seqDiff (setOfLevelOfValAtMost n) m) := by
  apply Set.seqDiff_finite_of_finite; exact TreeNode.instFiniteSetTreeNodeOfLengthTruncated n

noncomputable instance instFintypeSetTreeNodeOfLengthTruncatedSeqDiff (n m : ℕ) :
  Fintype (Set.seqDiff (setOfLevelOfValAtMost n) m) :=
  Set.Finite.fintype <| instFiniteSetTreeNodeOfLengthTruncatedSeqDiff n m

variable {α : Type*}

noncomputable def tsumOfLevel [AddCommMonoid α] [TopologicalSpace α] (f : TreeNode → α) (n : ℕ) : α
  := ∑' (ν : setOfLevel n), f ν

lemma tsumOfLevel_eq_tsum_sum' [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α] [T3Space α]
  (f : TreeNode → α) (n : ℕ)
  (hf1 : ∀ m, Summable fun c =>
    (fun v : @Sigma ℕ (fun m => Set.seqDiff (setOfLevelOfValAtMost n) m) => f v.snd) ⟨m, c⟩)
  (hf2 : Summable fun v : @Sigma ℕ (fun m => Set.seqDiff (setOfLevelOfValAtMost n) m) => f v.snd) :
  tsumOfLevel f n = ∑' m : ℕ, ∑ ν : Set.seqDiff (setOfLevelOfValAtMost n) m, f ν := by
  set seqDiff := Set.seqDiff <| setOfLevelOfValAtMost n with hseqDiff
  have h0 (m : ℕ) : ∑' v : seqDiff m, f v = ∑ v : seqDiff m, f v := by rw [tsum_eq_sum]; simp
  have h1 := @Summable.tsum_sigma' α ℕ _ _ _ _ (fun m => Set.Elem <| seqDiff m) (fun x => f x.2)
    hf1 hf2; simp at h1
  have h2 := TreeNode.setOfLevelOfValAtMost_union_eq_setOfLevel n
  rw [←Set.iUnion_accumulate, Set.accumulate_eq_seqDiff_acculumate, ←hseqDiff,
    Set.iUnion_accumulate, Set.iUnion_eq_range_sigma] at h2
  have h3 := @tsum_range α TreeNode (@Sigma ℕ fun b ↦ ↑(seqDiff b))
    _ _ (fun a => ↑a.snd) (fun v => f v) (by simp [seqDiff]); simp at h3
  have := h1 ▸ h2 ▸ h3; conv at this => right; congr; ext m; rw [h0 m]
  exact this

lemma tsumOfLevel_eq_tsum_sum [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
  [CompleteSpace α] [T0Space α] (f : TreeNode → α) (n : ℕ)
  (hf : Summable fun v : @Sigma ℕ (fun m => Set.seqDiff (setOfLevelOfValAtMost n) m) => f v.snd) :
  tsumOfLevel f n = ∑' m : ℕ, ∑ ν : Set.seqDiff (setOfLevelOfValAtMost n) m, f ν := by
  set seqDiff := Set.seqDiff <| setOfLevelOfValAtMost n with hseqDiff
  have h0 (m : ℕ) : ∑' v : seqDiff m, f v = ∑ v : seqDiff m, f v := by rw [tsum_eq_sum]; simp
  have h1 := @Summable.tsum_sigma α ℕ _ _ _ _ _ (fun m => Set.Elem <| seqDiff m) (fun x => f x.2)
    hf; simp at h1
  have h2 := TreeNode.setOfLevelOfValAtMost_union_eq_setOfLevel n
  rw [←Set.iUnion_accumulate, Set.accumulate_eq_seqDiff_acculumate, ←hseqDiff,
    Set.iUnion_accumulate, Set.iUnion_eq_range_sigma] at h2
  have h3 := @tsum_range α TreeNode (@Sigma ℕ fun b ↦ ↑(seqDiff b))
    _ _ (fun a => ↑a.snd) (fun v => f v) (by simp [seqDiff]); simp at h3
  have := h1 ▸ h2 ▸ h3; conv at this => right; congr; ext m; rw [h0 m]
  exact this

end TreeNode
