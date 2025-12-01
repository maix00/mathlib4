import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.Children
import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.Truncation
import Mathlib.Data.Set.Card.Arithmetic

open TreeNode ENNReal NNReal ENat Cardinal

namespace RLTree

variable {T T1 T2 : 𝕋₀} {v : 𝕍}

-- ## setOfLevelAtMost

protected def setOfLevelAtMost (T : 𝕋₀) (n : ℕ) : Set 𝕍 := (T↾(n)).set

scoped[RLTree] notation "𝕍{" T ",≤" n "}" => @RLTree.setOfLevelAtMost T n

instance instMonotoneSetOfLevelAtMost : Monotone T.setOfLevelAtMost := by
  intro m n hmn; by_cases h : m = n
  · subst m; simp
  · exact @mem_higher_truncation_of_mem_truncation T m n (by omega)

variable {T : 𝕋₀} {n : ℕ}

lemma setOfLevelAtMost_as_truncation_set : 𝕍{T,≤n} = (T↾(n)).set := by
  simp [RLTree.setOfLevelAtMost]

lemma setOfLevelAtMost_as_intersect_OfLevelAtMost : 𝕍{T,≤n} = T.set ∩ 𝕍{≤n} := by
  ext; simp [setOfLevelAtMost_as_truncation_set, truncation, TreeNode.setOfLevelAtMost]
  grind [mem_iff]

-- ## setOfLevel

protected def setOfLevel (T : 𝕋₀) (n : ℕ) : Set 𝕍 :=
  (T↾(n)).set \ if n = 0 then ∅ else (T↾(n - 1)).set

scoped[RLTree] notation "𝕍{" T "," n "}" => @RLTree.setOfLevel T n

lemma setOfLevel_as_seqDiff_truncation {T : 𝕋₀} {n : ℕ} : 𝕍{T,n} =
  (T↾(n)).set \ if n = 0 then ∅ else (T↾(n - 1)).set := by simp [RLTree.setOfLevel]

lemma setOfLevel_as_seqDiff_AtMost : T.setOfLevel = Set.seqDiff T.setOfLevelAtMost := by
  ext n v; by_cases h : n = 0
  · simp [setOfLevelAtMost_as_truncation_set, setOfLevel_as_seqDiff_truncation, Set.seqDiff, h]
  · simp only [setOfLevelAtMost_as_truncation_set, Set.seqDiff, setOfLevel_as_seqDiff_truncation, h,
      Set.accumulate_of_mono T.setOfLevelAtMost T.instMonotoneSetOfLevelAtMost]

lemma setOfLevel_as_intersect_OfLevel : 𝕍{T, n} = T.set ∩ 𝕍{n} := by
  ext; simp [setOfLevel_as_seqDiff_truncation, truncation, TreeNode.setOfLevel]; grind [mem_iff]

lemma setOfLevelAtMost_as_iUnion_finset_setOfLevel :
  𝕍{T,≤n} = ⋃ k : Finset.range (n + 1), 𝕍{T,k} := by
  simp only [setOfLevelAtMost_as_truncation_set, truncation, setOfLevel_as_intersect_OfLevel,
    setOfLevel]; ext v; simp [mem_iff]; grind

@[simp] lemma setOfLevel_zero : 𝕍{T, 0} = {[]} := by simp [setOfLevel_as_seqDiff_truncation]

@[simp] lemma setOfLevel_height {n : ℕ} : ∀ v ∈ 𝕍{T,n}, ‖v‖ₕ = n := by
  intro v hv; simp only [setOfLevel_as_seqDiff_truncation, truncation, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_ite_empty_left, not_and] at hv; by_cases h : n = 0
  · have := h ▸ hv.1.1; omega
  · have := (not_imp_not.2 <| hv.2 h) (not_not.2 hv.1.2); omega

@[simp] lemma finite_setOfLevel_of_finite (hT : Set.Finite T.set)
  (n : ℕ) : Set.Finite 𝕍{T,n} := by
  simp only [setOfLevel_as_seqDiff_truncation]; by_cases h : n = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact @Finite.Set.finite_diff _ _ _ (finite_truncation_of_finite hT n)

@[simp] lemma setOfLevel_subset_setOfLevel {n : ℕ} : 𝕍{T,n} ⊆ 𝕍{n} := by
  simp only [setOfLevel, Set.subset_def, Set.mem_setOf_eq]; exact RLTree.setOfLevel_height

lemma truncation_succ (T : 𝕋₀) (n : ℕ) : (T↾(n + 1)).set = (T↾(n)).set ∪
  ⋃ v ∈ 𝕍{T,n}, ⋃ m ∈ { m : ℕ | m + 1 ≤ ♯{T, v→}ₑ}, {m :: v} := by
  ext v; simp only [truncation, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion,
    Set.mem_singleton_iff, exists_prop]; constructor
  · intro ⟨hv1, hv2⟩; by_cases hv3 : ‖v‖ₕ ≤ n
    · left; grind
    · right; use v.tail, (by
        simp only [setOfLevel_as_seqDiff_truncation, truncation, Set.mem_diff, Set.mem_setOf_eq,
          List.length_tail, tsub_le_iff_right, Set.mem_ite_empty_left, not_and]; constructor
        · exact ⟨hv1, @tail_mem' T v hv2⟩
        · omega), v.head (by grind), (by
          simp only [countChildren]
          refine @le_iSup₂ _ ℕ _ _ (fun m => fun _ : m :: v.tail ∈ T => (m : WithTop ℕ) + 1 )
            (v.head (by grind)) (by grind)); grind
  · intro h; rcases h with (⟨hv1, hv2⟩|⟨vt, hv3, vh, hv4, hv5⟩)
    · grind
    · have hv6 : ‖vt‖ₕ = n := setOfLevel_height vt hv3
      have hv7 : vh :: vt ∈ T := countChildren_ge_iff.2 hv4
      grind

lemma setOfLevel_as_iUnion_children_previous :
  𝕍{T, n} = if n = 0 then {[]} else ⋃ v ∈ 𝕍{T, n - 1}, 𝕍{T, v→} := by
  by_cases h : n = 0
  · simp [h]
  · simp only [h, ↓reduceIte]; ext v; simp only [setOfLevel_as_intersect_OfLevel, setOfLevel,
    Set.mem_inter_iff, Set.mem_setOf_eq, children, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop]
    constructor
    · intro h; use v.tail; simp only [List.length_tail, h, and_true]
      have h' := v.cons_head_tail (by grind)
      use tail_mem <| h' ▸ h.1, v.head (by grind), mem_iff.2 <| Eq.symm h' ▸ h.1, Eq.symm h'
    · grind [mem_iff]

-- ## generationSizeFromLevel

protected noncomputable def generationSizeFromLevel (T : 𝕋₀)
  := tsumOfLevel (ENat.toENNReal ∘ T.countChildren)

scoped[RLTree] notation "♯{" T ",ℒ(" n ")→}ₑ" => @RLTree.generationSizeFromLevel T n

lemma generationSizeFromLevel_as_tsumOfLevel_countChildren_toENNReal {T : 𝕋₀} {n : ℕ} :
  ♯{T,ℒ(n)→}ₑ = ∑' v : 𝕍{n}, (♯{T, v→}ₑ : ℝ≥0∞):= by
    simp [RLTree.generationSizeFromLevel, tsumOfLevel]

lemma generationSizeFromLevel_eq_tsum_sum (T : 𝕋₀) (n : ℕ) :
  ♯{T,ℒ(n)→}ₑ = ∑' m, ∑ v : 𝕍{n,m}, ↑(♯{T, ↑v→}ₑ)
  := tsumOfLevel_eq_tsum_sum' _ n (by simp) (by simp)

@[simp] lemma generationSizeFromLevel_zero : ♯{T,ℒ(0)→}ₑ = T.countChildren [] := by
  simp only [generationSizeFromLevel_as_tsumOfLevel_countChildren_toENNReal]
  rw [TreeNode.setOfLevel_zero]; exact tsum_singleton ([] : 𝕍) (fun v => (♯{T, v→}ₑ : ℝ≥0∞))

lemma setOfLevel_card_eq_generationSizeFromLevel_previous :
  card 𝕍{T, n} = if n = 0 then 1 else ♯{T,ℒ(n - 1)→}ₑ := by
  cases n with
  | zero => simp
  | succ n' =>
    cases n' with
    | zero =>
      rw [setOfLevel_as_iUnion_children_previous]; simp [RLTree.countChildren_as_children_card]
    | succ n'' =>
      rw [setOfLevel_as_iUnion_children_previous]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, ↓reduceIte,
        add_tsub_cancel_right, card_coe_set_eq,
        generationSizeFromLevel_as_tsumOfLevel_countChildren_toENNReal]
      set S := {v | ♯{T, v→}ₑ = 0} with hS
      have h1 := @tsum_setElem_eq_tsum_setElem_diff ℝ≥0∞ 𝕍 _ _ (fun v => ♯{T, v→}ₑ) 𝕍{n'' + 1} S (by
        simp only [hS, Set.mem_setOf_eq]; intro v hv
        have := ENat.toENNReal_inj.2 hv; simpa); rw [h1]; simp only
      have h2 : 𝕍{n'' + 1} \ S ⊆ 𝕍{T, n'' + 1} := by
        apply Set.diff_subset_iff.2; intro v hv; simp only [hS, Set.mem_union, Set.mem_setOf_eq]
        by_cases hv' : v ∈ 𝕍{T, n'' + 1}
        · right; exact hv'
        · left; refine RLTree.countChildren_eq_zero_of_not_mem ?_; by_contra hv''
          have : v ∈ 𝕍{T, n'' + 1} := by
            simp [setOfLevel_as_intersect_OfLevel, RLTree.mem_iff.1 hv'', *]
          contradiction
      set S' := 𝕍{T, n'' + 1} \ (𝕍{n'' + 1} \ S) with hS'
      have h5 : 𝕍{T, n'' + 1} = S' ∪ (𝕍{n'' + 1} \ S) := (by grind)
      have h6 : (⋃ v ∈ (S' ∪ 𝕍{n'' + 1} \ S), 𝕍{T, v→}) =
        (⋃ v ∈ S', 𝕍{T, v→}) ∪ (⋃ v ∈ (𝕍{n'' + 1} \ S), 𝕍{T, v→}) := by ext; simp; grind
      have h7 (U V : Set 𝕍) (h : Disjoint U V) := @Set.encard_union_eq _ (⋃ v ∈ U, 𝕍{T, v→})
        (⋃ v ∈ V, 𝕍{T, v→}) (by
        simp only [Set.disjoint_iUnion_right, Set.disjoint_iUnion_left]; intro v hv u hu s hsu hsv
        by_contra hs; simp only [Set.bot_eq_empty, Set.le_eq_subset, Set.subset_empty_iff] at hs
        have h8 := not_imp_not.2 Set.eq_empty_iff_forall_notMem.2 hs; simp only [not_forall,
          not_not] at h8; obtain ⟨w, hws⟩ := h8
        have hwu := Set.mem_of_subset_of_mem hsu hws
        have hwv := Set.mem_of_subset_of_mem hsv hws
        simp only [children, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hwu hwv
        obtain ⟨m, hm, hwu⟩ := hwu; obtain ⟨n, hn, hwv⟩ := hwv;
        have h9 : u = v := by grind
        simp only [Disjoint, Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff] at h
        specialize @h {u} (by grind) (by grind); absurd h; simp)
      have h7' := h7 S' (𝕍{n'' + 1} \ S) (by
        simp only [S']; intro s h10 h11; have ⟨h12, h13⟩ := Set.subset_diff.1 h10
        simp only [Set.bot_eq_empty, Set.le_eq_subset, Set.subset_empty_iff]
        exact (Set.disjoint_of_subset_iff_left_eq_empty h11).1 h13)
      have h14 : ⋃ v ∈ S', T.children v = ∅ := by
        simp only [Set.mem_diff, not_and, Decidable.not_not, children, Set.iUnion_eq_empty,
          Set.singleton_ne_empty, imp_false, and_imp, S']; intro v h15 h16 m
        specialize h16 <| setOfLevel_subset_setOfLevel h15
        simp only [Set.mem_setOf_eq, S] at h16; have h16 := RLTree.countChildren_eq_zero_iff.1 h16;
        exact h16 m
      conv at h7' => right; simp only [h14, Set.encard_empty, zero_add]
      have h7' := h5 ▸ h6 ▸ h7'; rw [h7']; clear h5 h6 h7' h14
      by_cases h17 : ∃ v ∈ 𝕍{n'' + 1} \ S, ♯{T, v→}ₑ = ⊤
      · obtain ⟨v, hv1, hv2⟩ := h17
        have h18 := @ENNReal.le_tsum (Set.Elem (𝕍{n'' + 1} \ S)) (fun u => ♯{T, ↑u→}ₑ) ⟨v, hv1⟩
        simp only [hv2, toENNReal_top, top_le_iff] at h18; rw [h18]
        have h19 := @RLTree.countChildren_as_children_card T v; simp only [hv2,
          card_coe_set_eq] at h19
        have h7' := h7 {v} ((𝕍{n'' + 1} \ S) \ {v}) (by
          intro s h20 h21; have ⟨h22, h23⟩ := Set.subset_diff.1 h21
          simp only [Set.bot_eq_empty, Set.le_eq_subset, Set.subset_empty_iff]
          exact (Set.disjoint_of_subset_iff_left_eq_empty h20).1 h23)
        conv at h7'=> right; arg 1; simp [←h19]
        have h20 : (⋃ u ∈ (𝕍{n'' + 1} \ S), 𝕍{T, u→}) =
          (⋃ u ∈ ({v} : Set 𝕍), 𝕍{T, u→}) ∪ (⋃ u ∈ ((𝕍{n'' + 1} \ S) \ {v}), 𝕍{T, u→}) := by
          ext; simp; grind
        have h7' := h20 ▸ h7'; rw [h7']; simp
      · have h4 : ∀ v ∈ 𝕍{n'' + 1} \ S, ♯{T, v→}ₑ > 0 := by
          simp only [Set.mem_diff, Set.mem_setOf_eq, gt_iff_lt, and_imp, S]
          intro v hv hv'; simpa [pos_iff_ne_zero]
        have h4 : ∀ v ∈ 𝕍{n'' + 1} \ S, ♯{T, v→}ₑ ≥ 1 := by
          intro v hv; specialize h4 v hv; grind [ENat.one_le_iff_ne_zero]
        have h21 := @ENNReal.tsum_le_tsum ↑(𝕍{n'' + 1} \ S) (fun _ => (1 : ℝ≥0∞))
          (fun u => ♯{T, u→}ₑ) (by
            intro u; specialize h4 u u.property; have h4 := ENat.toENNReal_le.2 h4
            simp only [toENNReal_one, ge_iff_le] at ⊢ h4
            exact h4); simp only [tsum_one, card_coe_set_eq] at h21
        have h3 := @Set.iUnion_subtype 𝕍 𝕍 (fun v => v ∈ (𝕍{n'' + 1} \ S)) (fun v => 𝕍{T, v→})
        by_cases h22 : Set.Infinite (𝕍{n'' + 1} \ S)
        · have h23 := Set.encard_eq_top_iff.2 h22; simp only [h23, toENNReal_top,
          top_le_iff] at h21; rw[h21]
          simp only [toENNReal_eq_top, Set.encard_eq_top_iff]
          by_contra h'; simp only [Set.not_infinite] at h'; rw [←h3] at h'
          have ⟨h24, h25⟩ := (@Set.finite_iUnion_iff 𝕍 ↑(𝕍{n'' + 1} \ S)
            (fun v => 𝕍{T, v→}) (by
              intro ⟨u, hu⟩ ⟨v, hv⟩ huv s hsu hsv; by_contra hs
              simp only [Set.bot_eq_empty, Set.le_eq_subset, Set.subset_empty_iff] at hs
              have h26 := not_imp_not.2 Set.eq_empty_iff_forall_notMem.2 hs
              simp only [not_forall, not_not] at h26
              obtain ⟨w, hws⟩ := h26
              have hwu := Set.mem_of_subset_of_mem hsu hws
              have hwv := Set.mem_of_subset_of_mem hsv hws
              simp only [children, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hwu hwv
              obtain ⟨m, hm, hwu⟩ := hwu; obtain ⟨n, hn, hwv⟩ := hwv;
              have h27 : u = v := (by grind only); absurd huv; congr)).1 h'
          have h27 : {v : ↑(𝕍{n'' + 1} \ S) | 𝕍{T, v→}.Nonempty} = @Set.univ ↑(𝕍{n'' + 1} \ S) := by
            ext ⟨u, hu⟩; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; specialize h4 u hu
            have h28 := @RLTree.countChildren_as_children_card T u; rw [h28] at h4
            simp only [card_coe_set_eq, ge_iff_le, Set.one_le_encard_iff_nonempty] at h4; exact h4
          rw [h27] at h25; have ⟨h25⟩ := Set.univ_finite_iff_nonempty_fintype.1 h25
          exact h22 <| Set.finite_coe_iff.1 <| Fintype.finite h25
        · simp only [Set.not_infinite] at h22
          have h30 := @tsum_eq_finsum ℝ≥0∞ ↑(𝕍{n'' + 1} \ S) _ _ (fun u => ♯{T, ↑u→}ₑ)
            (SummationFilter.unconditional ↑(𝕍{n'' + 1} \ S)) _ (by
            simp only [Function.support, ne_eq]
            have h31 : {v : ↑(𝕍{n'' + 1} \ S) | ¬(♯{T, ↑v→}ₑ : ℝ≥0∞) = 0}
              = @Set.univ ↑(𝕍{n'' + 1} \ S) := by
              ext ⟨v, hv⟩; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
              simp only [Set.mem_diff, Set.mem_setOf_eq, S] at hv; by_contra h29
              rw [←ENat.toENNReal_zero] at h29; exact hv.2 <| ENat.toENNReal_inj.1 h29
            rw [h31]; exact Set.univ_finite_iff_nonempty_fintype.2
              ⟨@Fintype.ofFinite _ <| Set.finite_coe_iff.2 h22⟩); rw [h30, ←h3]
          have h32 := @Set.encard_iUnion_of_finite 𝕍 ↑(𝕍{n'' + 1} \ S) (Set.finite_coe_iff.2 h22)
            (fun u => 𝕍{T, ↑u→}) (by
              intro ⟨u, hu⟩ ⟨v, hv⟩ huv s hsu hsv; by_contra hs; simp only [Set.bot_eq_empty,
                Set.le_eq_subset, Set.subset_empty_iff] at hs
              have h33 := not_imp_not.2 Set.eq_empty_iff_forall_notMem.2 hs; simp only [not_forall,
                not_not] at h33
              obtain ⟨w, hws⟩ := h33
              have hwu := Set.mem_of_subset_of_mem hsu hws
              have hwv := Set.mem_of_subset_of_mem hsv hws
              simp only [children, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hwu hwv
              obtain ⟨m, hm, hwu⟩ := hwu; obtain ⟨n, hn, hwv⟩ := hwv;
              have h34 : u = v := (by
                have hwu : u = w.tail := by simp only [hwu, List.tail_cons]
                have hwv : v = w.tail := by simp only [hwv, List.tail_cons]
                exact Eq.trans hwu <| Eq.symm hwv); absurd huv; congr)
          rw [h32]; simp only
          have h35 (u : 𝕍) := @RLTree.countChildren_as_children_card T u
          simp only [card_coe_set_eq] at h35
          conv => left; congr; congr; ext u; simp only [← h35 ↑u]
          set h36 := Set.Finite.toFinset <| Set.univ_finite_iff_nonempty_fintype.2
            ⟨@Fintype.ofFinite _ <| Set.finite_coe_iff.2 h22⟩
          have h37 := @finsum_eq_finset_sum_of_support_subset ↑(𝕍{n'' + 1} \ S) ℕ∞ _
            (fun u => ♯{T, ↑u→}ₑ) h36 (by intro; simp [h36])
          have h38 := @finsum_eq_finset_sum_of_support_subset ↑(𝕍{n'' + 1} \ S) ℝ≥0∞ _
            (fun u => ♯{T, ↑u→}ₑ) h36 (by intro; simp [h36])
          rw [h37, h38]
          have h39 := @map_sum ↑(𝕍{n'' + 1} \ S) ℕ∞ ℝ≥0∞ _ _ _ _ _ ENat.toENNRealRingHom
            (fun u => ♯{T, ↑u→}ₑ) h36; simp only [toENNRealRingHom_apply] at h39
          exact h39

lemma generationSizeFromLevel_as_setOfLevel_succ_card : ♯{T,ℒ(n)→}ₑ = card 𝕍{T, n + 1} := by
  simp only [setOfLevel_card_eq_generationSizeFromLevel_previous]; simp

namespace LocallyFinite

variable (T : 𝕋) (v : 𝕍) (n : ℕ)

-- ## LocallyFinite.setOfLevel

@[simp] lemma setOfLevel_finite : Set.Finite 𝕍{T, n} := by
  simp only [setOfLevel_as_seqDiff_truncation]; by_cases n = 0
  · simp [*]
  · simp only [↓reduceIte, *]; apply Set.Finite.diff; exact T.locally_finite n

noncomputable instance : Fintype 𝕍{T, n} :=
  @Fintype.ofFinite _ <| Set.finite_coe_iff.2 <| setOfLevel_finite T n

lemma setOfLevel_card_lt_top : card 𝕍{T, n} < ⊤ := by simp

lemma _root_.RLTree.isLocallyFinite_iff_setOfLevel_finite (T : 𝕋₀) :
  T.IsLocallyFinite ↔ ∀ n, 𝕍{T, n}.Finite := by
  constructor
  · intro hT; set T' := RLTree.LocallyFinite.mk T hT
    have (n : ℕ) : 𝕍{T', n}.Finite := setOfLevel_finite T' n
    simp only [T'] at this; exact this
  · simp only [isLocallyFinite_iff_forall_truncation_finite,
      ←setOfLevelAtMost_as_truncation_set, setOfLevelAtMost_as_iUnion_finset_setOfLevel]
    intro hT _; refine Set.finite_iUnion ?_; intro ⟨m, _⟩; exact hT m

lemma _root_.RLTree.isLocallyFinite_iff_setOfLevel_card_lt_top (T : 𝕋₀) :
  T.IsLocallyFinite ↔ ∀ n, card 𝕍{T, n} < ⊤ := by
  simp [isLocallyFinite_iff_setOfLevel_finite]

-- ## LocallyFinite.generationSizeFromLevel
section
variable {T : 𝕋} (n : ℕ)

protected noncomputable def generationSizeFromLevel := tsumOfLevel T.countChildren

scoped[RLTree.LocallyFinite] notation "♯{" T ",ℒ(" n ")→}" =>
  @RLTree.LocallyFinite.generationSizeFromLevel T n

lemma generationSizeFromLevel_as_tsumOfLevel_countChildren :
  ♯{T,ℒ(n)→} = ∑' v : 𝕍{n}, ♯{T, v→} := by
  simp [RLTree.LocallyFinite.generationSizeFromLevel, tsumOfLevel]

private lemma generationSizeFromLevel_def_aux_1 :
  ♯{T,ℒ(n)→} = ∑ v ∈ Finset.subtype (fun v : 𝕍 ↦ ‖v‖ₕ = n) 𝕍{T, n}.toFinset, ♯{T, ↑v→} := by
  simp only [generationSizeFromLevel_as_tsumOfLevel_countChildren]
  have heq := @tsum_eq_sum ℕ 𝕍{n} Nat.instAddCommMonoid instTopologicalSpaceNat
    (fun v => ♯{T, ↑v→}) (SummationFilter.unconditional ↑𝕍{n}) _
    (by simp only [setOfLevel, Set.coe_setOf]; apply Finset.subtype; exact 𝕍{T, n}.toFinset) (by
    simp only [id_eq, Finset.mem_subtype, Set.mem_toFinset, Subtype.forall]; intro v hv hv'
    exact countChildren_eq_zero_of_not_mem T v (by
    by_contra h; have : v ∈ 𝕍{T, n} := by
      simp only [RLTree.setOfLevel, RLTree.truncation, Set.mem_diff, Set.mem_setOf_eq,
        Set.mem_ite_empty_left, not_and]
      simp only [setOfLevel, Set.mem_setOf_eq] at hv; by_cases n = 0
      · simp only [le_refl, true_and, not_true_eq_false, zero_tsub, forall_const,
          IsEmpty.forall_iff, and_true, *]; exact h
      · simp only [le_refl, true_and, not_false_eq_true, isEmpty_Prop, not_le,
        (show n > n - 1 from by omega), IsEmpty.forall_iff, imp_self, and_true, *]; exact h
    contradiction))
  simp only [id_eq] at heq; exact heq

private lemma generationSizeFromLevel_def_aux_2 :
  ♯{T,ℒ(n)→}ₑ = ∑ v ∈ Finset.subtype (fun v : 𝕍 ↦ ‖v‖ₕ = n) 𝕍{T, n}.toFinset, ♯{T, ↑v→}ₑ := by
  simp only [generationSizeFromLevel_as_tsumOfLevel_countChildren_toENNReal]
  have heq := @tsum_eq_sum ℝ≥0∞ 𝕍{n} _ _ (fun v => ♯{T, ↑v→}) (SummationFilter.unconditional ↑𝕍{n})
    _ (by simp only [setOfLevel, Set.coe_setOf]; apply Finset.subtype; exact 𝕍{T, n}.toFinset) (by
    simp only [id_eq, Finset.mem_subtype, Set.mem_toFinset, Nat.cast_eq_zero, Subtype.forall]
    intro v hv hv'; exact countChildren_eq_zero_of_not_mem T v (by
    by_contra h; have : v ∈ 𝕍{T, n} := by
      simp only [RLTree.setOfLevel, RLTree.truncation, Set.mem_diff, Set.mem_setOf_eq,
        Set.mem_ite_empty_left, not_and]
      simp [TreeNode.setOfLevel] at hv; by_cases n = 0
      · simpa [*]
      · simp only [le_refl, true_and, not_false_eq_true, isEmpty_Prop, not_le,
        (show n > n - 1 from by omega), IsEmpty.forall_iff, imp_self, and_true, *]; exact h
    contradiction))
  simp only [id_eq] at heq
  have (n : ℕ∞) (hn : n < ⊤) : n.lift hn = (n : ℝ≥0∞) := by
    have (n : ℕ) : (n : ℕ∞) = (n : ℝ≥0∞) := (by simp); rw [←this]; simp
  conv at heq => left; simp [countChildren, this]
  exact Eq.trans heq (by
  simp only [countChildren]; conv => left; arg 2; ext; rw[this]
  apply Eq.symm; exact @map_sum {v : 𝕍 // ‖v‖ₕ = n} ℕ∞ ℝ≥0∞ _ _ _ _ _
    ENat.toENNRealRingHom (fun v => ♯{T, ↑v→}ₑ)
    (Finset.subtype (fun v : 𝕍 ↦ ‖v‖ₕ = n) 𝕍{T, n}.toFinset))

lemma generationSizeFromLevel_def_toRLTree : (♯{T,ℒ(n)→} : ℝ≥0∞) = ♯{T,ℒ(n)→}ₑ := by
  simp only [generationSizeFromLevel_def_aux_1, generationSizeFromLevel_def_aux_2, countChildren];
  rw [←ENat.toENNReal_coe]; apply ENat.toENNReal_inj.2; simp only [Nat.cast_sum, ENat.coe_lift,
    Finset.sum_subtype_eq_sum_filter]

lemma generationSizeFromLevel_as_sum : ♯{T,ℒ(n)→} = ∑ v ∈ 𝕍{T, n}.toFinset, ♯{T, v→} := by
  apply Eq.trans <| T.generationSizeFromLevel_def_aux_1 n
  simp only [Finset.sum_subtype_eq_sum_filter]; congr; simp only [Finset.filter_eq_self,
    Set.mem_toFinset]
  exact @setOfLevel_height T.toRLTree n

lemma setOfLevel_as_iUnion_children_previous_finite :
  𝕍{T, n} = if n = 0 then {[]} else ⋃ v ∈ 𝕍{T, n - 1}.toFinset, 𝕍{T, v→} := by
  rw [setOfLevel_as_iUnion_children_previous]; simp

lemma setOfLevel_card_eq_generationSizeFromLevel_previous :
  card 𝕍{T, n} = if n = 0 then 1 else ♯{T,ℒ(n - 1)→} := by
  cases n with
  | zero => simp
  | succ n' =>
    apply ENat.toENNReal_inj.1
    conv => right; simp; rw [T.generationSizeFromLevel_def_toRLTree n']
    rw [RLTree.setOfLevel_card_eq_generationSizeFromLevel_previous]; simp

end

end LocallyFinite

end RLTree
