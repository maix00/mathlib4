import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.Defs
import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.Truncation
import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.LocallyFinite

open TreeNode ENNReal NNReal ENat Cardinal

namespace RLTree

variable {T T1 T2 : 𝕋₀} {v : 𝕍}

-- ## children

def children (T : 𝕋₀) (v : 𝕍) : Set 𝕍 := ⋃ (m : ℕ) (_ : m :: v ∈ T), {m :: v}

scoped[RLTree] notation "𝕍{" T ", " v "→}" => @children T v

@[simp]
lemma children_pairwise_disjoint_on : Pairwise (Function.onFun Disjoint fun u ↦ T.children u) := by
  intro u v huv s hsu hsv; by_contra hs; simp only [Set.bot_eq_empty,
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
    exact Eq.trans hwu <| Eq.symm hwv); absurd huv; congr

-- ## countChildren

noncomputable def countChildren (T : 𝕋₀) (v : 𝕍) : ℕ∞ :=
  (⨆ (m : ℕ) (_ : m :: v ∈ T), m + 1 : WithTop ℕ)

scoped[RLTree] notation "♯{" T ", " v "→}ₑ" => @countChildren T v

@[simp] lemma countChildren_eq_zero (h : ∀ m, m :: v ∉ T) : ♯{T, v→}ₑ = 0 := by
  simp [countChildren, *]

@[simp] lemma countChildren_eq_zero_of_not_mem (h : v ∉ T) : ♯{T, v→}ₑ = 0 := by
  apply countChildren_eq_zero; intro m; by_contra h; have := tail_mem h; contradiction

lemma countChildren_eq_zero_iff : ♯{T, v→}ₑ = 0 ↔ ∀ m, m :: v ∉ T := by
  constructor
  · intro h; have h := ENat.coe_le_coe.2 <| le_zero_iff.2 (show ♯{T, v→}ₑ.lift (by simp [h]) = 0
      from by simp [h])
    conv at h => left; simp
    conv at h => right; simp
    simp only [countChildren] at h
    have h := (@iSup₂_le_iff (WithTop ℕ) ℕ (fun m => m :: v ∈ T) _ (0 : ℕ∞)
      (fun m => fun _ => (m : ℕ∞) + (1 : ℕ∞))).1 h
    intro m; by_contra hm; specialize h m hm; have := @ENat.add_one_pos ↑m; grind
  · intro; simp [*]

@[simp] lemma countChildren_eq_top (h : ∀ m, m :: v ∈ T) : ♯{T, v→}ₑ = ⊤ := by
    simp only [countChildren, iSup_pos, h]
    rw [iSup_eq_top (fun (m : ℕ) => (m + 1 : WithTop ℕ))]
    intro b hb
    match b with
    | ⊤ => contradiction
    | some b' =>
      use b'; apply WithTop.lt_iff_exists.2
      use b'; simp only [WithTop.some_eq_coe, ENat.some_eq_coe, true_and]; intro c hc
      have : c = b' + 1 := by have := WithTop.add_eq_coe.1 hc; aesop
      simp [*]

@[simp] lemma countChildren_eq_top_iff : ♯{T, v→}ₑ = ⊤ ↔ (∀ m, m :: v ∈ T) := by
  constructor
  · intro h; simp only [countChildren] at h
    rw [iSup₂_eq_top (fun m => fun (_ : m :: v ∈ T) => (m + 1 : WithTop ℕ))] at h
    intro m; obtain ⟨n, hn, hmn⟩ := h (m + 1) (by simp)
    obtain ⟨m', hm', h'⟩ := WithTop.lt_iff_exists.1 hmn
    specialize h' (n + 1) (by simp)
    rw [show (m : WithTop ℕ) + 1 = ↑(m + 1) from by simp] at hm'
    rw [←(@WithTop.coe_inj ℕ (m + 1) m').1 hm'] at h'; simp at h'
    exact mem_iff.2 <| T.generate_refl ▸ generateSet.less n v
      (Eq.symm T.generate_refl ▸ mem_iff.1 hn) m (by omega)
  · exact countChildren_eq_top

@[simp] lemma countChildren_ge {m : ℕ} (h : m :: v ∈ T) : m + 1 ≤ ♯{T, v→}ₑ := by
  simp only [countChildren]; exact @le_iSup₂ (WithTop ℕ) ℕ _ _ _ _ h

lemma countChildren_mem {h : ♯{T, v→}ₑ ≠ ⊤} {h' : ♯{T, v→}ₑ ≠ 0} :
  ∃ m : ℕ, m :: v ∈ T ∧ ♯{T, v→}ₑ = m + 1 := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  have : n ≠ 0 := by by_contra h'; have := Eq.symm <| h' ▸ hn; simp at this; contradiction
  use (n - 1); constructor
  · have : ↑n - 1 < ♯{T, v→}ₑ := by
      rw [←hn]; have := WithTop.coe_inj.2 (show n - 1 = n - 1 from rfl); conv at this => left; simp
      rw [this]; exact WithTop.coe_lt_coe.2 (show n - 1 < n from by omega)
    rw [countChildren, iSup_subtype', iSup] at hn this
    obtain ⟨n', hn'1, hn'2⟩ := (@lt_sSup_iff (WithTop ℕ) _ _ _).1 this
    have hn'5 := hn ▸ le_sSup hn'1
    have : n' = ↑n := by
      have : n' ≠ ⊤ := by aesop
      have h0 : n' = ↑(n'.untop this) := (WithTop.untop_eq_iff this).1 rfl
      set n'' := n'.untop this; rw [h0] at ⊢ hn'2 hn'5
      have : n'' = n := by
        have := WithTop.coe_lt_coe.1 hn'2; simp at this
        have := WithTop.coe_le_coe.1 hn'5; simp at this
        omega
      exact WithTop.coe_inj.2 this
    subst n'
    simp only [Set.mem_range, Subtype.exists, exists_prop] at hn'1; obtain ⟨n', hn'3, hn'4⟩ := hn'1
    have : n' = n - 1 := by have := WithTop.coe_inj.1 hn'4; simp at this; omega
    exact this ▸ hn'3
  · rw [show ↑(n - 1) + 1 = (n : WithTop ℕ) from by
      set n' := n - 1 with hn'; rw [show n = n' + 1 from by omega]; aesop];
    exact Eq.symm hn

lemma countChildren_ge_iff {m : ℕ} : m :: v ∈ T ↔ m + 1 ≤ ♯{T, v→}ₑ := by
  constructor
  · exact countChildren_ge
  · intro h
    by_cases ♯{T, v→}ₑ = ⊤
    · exact countChildren_eq_top_iff.1 ‹_› m
    · set n := ♯{T, v→}ₑ.untop ‹_› with hn
      have hn : ↑n = ♯{T, v→}ₑ := Eq.symm <| (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hn
      have : m + 1 ≤ n := by
        rw [←hn] at h
        obtain ⟨m', hm', h'⟩ := WithTop.le_coe_iff.1 h
        rw [show (m : WithTop ℕ) + 1 = ↑(m + 1) from by simp] at hm'
        have := (@WithTop.coe_inj ℕ (m + 1) m').1 hm'
        rw [←(@WithTop.coe_inj ℕ (m + 1) m').1 hm'] at h'; exact h'
      have : n ≠ 0 := by omega
      have : (n - 1) :: v ∈ T := by
        obtain ⟨k, hk, hk'⟩ := @T.countChildren_mem v ‹_›
          (by rw [←hn]; exact not_imp_not.2 WithTop.coe_inj.1 this)
        rw [←hn] at hk'
        have : k = n - 1 := by
          have := WithTop.coe_inj.1 hk'; simp at this; omega
        exact this ▸ hk
      exact mem_iff.2 <| T.generate_refl ▸ generateSet.less (n - 1) v
        (Eq.symm T.generate_refl ▸ mem_iff.1 this) m (by omega)

private def ext_of_countChildren_aux (h : ∀ v, ♯{T1, v→}ₑ = ♯{T2, v→}ₑ) (v : 𝕍) :
  v ∈ T1 → v ∈ T2 := by
  intro hv; cases v with
  | nil => exact T2.nil_mem
  | cons m v' => exact countChildren_ge_iff.2 <| h v' ▸ T1.countChildren_ge hv

@[ext] def ext_of_countChildren (T1 T2 : 𝕋₀) (h : ∀ v, ♯{T1, v→}ₑ = ♯{T2, v→}ₑ) : T1 = T2 := by
  ext v; constructor
  · exact ext_of_countChildren_aux h v
  · exact ext_of_countChildren_aux (fun v => Eq.symm <| h v) v

noncomputable instance : FunLike 𝕋₀ 𝕍 ℕ∞ where
  coe T := T.countChildren
  coe_injective' T1 T2 h := by
    ext v; simp only at h; have := congrArg (fun f => f v) h; simpa using this

lemma children_as_iUnion_lt_countChildren :
  𝕍{T, v→} = ⋃ (m : ℕ) (_ : m + 1 ≤ ♯{T, v→}ₑ), {m :: v} := by
  simp [children, countChildren_ge_iff]

lemma countChildren_as_children_card : ♯{T, v→}ₑ = card 𝕍{T, v→} := by
  by_cases h : ♯{T, v→}ₑ = ⊤
  · simp only [h, children_as_iUnion_lt_countChildren, le_top, Set.iUnion_true,
    Set.iUnion_singleton_eq_range, card_coe_set_eq]; apply Eq.symm; apply card_eq_top.2
    apply Set.infinite_coe_iff.2; apply Set.infinite_range_of_injective; intro n m; simp
  · simp only [children_as_iUnion_lt_countChildren, card_coe_set_eq]
    set c := ♯{T, v→}ₑ.lift <| WithTop.lt_top_iff_ne_top.2 h with hc
    have hc' : ♯{T, v→}ₑ = c := by simp only [hc, coe_lift]
    rw [hc']
    have (m : ℕ): (m : ℕ∞) + 1 ≤ (c : ℕ∞) ↔ m + 1 ≤ c := ENat.coe_le_coe
    conv => right; congr; congr; ext m; rw [this]
    have := Set.iUnion_subtype (fun m : ℕ => m + 1 ≤ c) (fun m => {m.val :: v})
    simp only [Set.iUnion_singleton_eq_range] at this; rw [←this]
    have := @Set.encard_preimage_of_injective_subset_range {x // x + 1 ≤ c} (List ℕ)
      (Set.range (fun x : {x // x + 1 ≤ c} => ↑x :: v)) (fun x => ↑x :: v)
      (by intro _ _ ; simp [Subtype.val_inj]) (by simp); simp only [Set.preimage_range,
        Set.encard_univ] at this; rw [←this]
    set c' := Set.encard {x | x + 1 ≤ c} with hc'
    let hc'' := hc'; simp only [Set.encard, Set.coe_setOf] at hc''; rw [←hc'']
    have (c : ℕ) : {x | x + 1 ≤ c}.encard = c := by
      induction c with
      | zero => simp
      | succ k ih =>
        have := (show {x | x + 1 ≤ k + 1} = {x | x + 1 ≤ k} ∪ {k} from by ext; grind)
        have : ({x | x + 1 ≤ k} ∪ {k}).encard = {x | x + 1 ≤ k}.encard + 1 := by
          have := @Set.encard_union_eq _ {x | x + 1 ≤ k} {k} (by simp); simp at this; simp [this]
        grind
    rw [this c] at hc'; exact Eq.symm hc'

namespace LocallyFinite

variable (T : 𝕋) (v : 𝕍) (n : ℕ)

-- ## LocallyFinite.countChildren

@[simp] lemma countChildren_ne_top : ♯{T, v→}ₑ ≠ ⊤ := by
  simp only [ne_eq, countChildren_eq_top_iff, not_forall]
  set S := T.toRLTree↾(‖v‖ₕ + 1) with hS
  have hT := (@Nat.card_eq_fintype_card _
    <| hS ▸ (@Fintype.ofFinite _ <| T.locally_finite (‖v‖ₕ + 1)))
    ▸ hS ▸ (@Finite.equivFin _ <| T.locally_finite (‖v‖ₕ + 1))
  set n := @Fintype.card _ <| hS ▸ (@Fintype.ofFinite _ <| T.locally_finite (‖v‖ₕ + 1)) with hn
  use n; by_contra h; have h := hS ▸ @mem_truncation_of_mem _ (‖v‖ₕ + 1) _ (by simp) h
  let F (m : Fin (n + 1)) : S.set.Elem := ⟨m :: v, @less_mem S n _ v h (by omega)⟩
  have := Fintype.card_le_of_injective F (by simp [Function.Injective, F]; omega); simp [hn] at this

@[simp] lemma countChildren_lt_top : countChildren ↑T v < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top]; exact countChildren_ne_top T v

noncomputable def countChildren : ℕ := (T.toRLTree.countChildren v).lift (by simp)

scoped[RLTree.LocallyFinite] notation "♯{" T ", " v "→}" => @countChildren T v

lemma countChildren_eq_toNat : ♯{T, v→} = ♯{T, v→}ₑ.toNat := ENat.lift_eq_toNat_of_lt_top (by simp)

lemma countChildren_toENat : (♯{T, v→} : ℕ∞) = ♯{T, v→}ₑ := by
  simp [countChildren]

@[ext] def ext_of_countChildren (T1 T2 : 𝕋) (h : ∀ l, ♯{T1, l→} = ♯{T2, l→}) : T1 = T2 :=
  toRLTree_inj <| RLTree.ext_of_countChildren _ _ (by
    intro v; specialize h v; simp only [countChildren] at h
    exact @ENat.coe_lift ♯{T1, v→}ₑ (by simp) ▸ h ▸ @ENat.coe_lift ♯{T2, v→}ₑ (by simp))

@[simp] lemma countChildren_eq_zero_of_not_mem (hv : v ∉ T) : ♯{T, v→} = 0 := by
  simp only [countChildren, ENat.lift, RLTree.countChildren, WithTop.untop_eq_iff, WithTop.coe_zero]
  have {m : ℕ∞} (hm : m ≤ 0) : m = 0 := by simp only [nonpos_iff_eq_zero] at hm; exact hm
  apply this; apply (@iSup₂_le_iff (WithTop ℕ) ℕ (fun m => m :: v ∈ T) _).2; intro m hm
  simp only [nonpos_iff_eq_zero, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false]
  exact hv <| @tail_mem _ _ _ hm

lemma countChildren_as_children_card : ♯{T, v→} = card 𝕍{T, v→} := by
  simp [countChildren, RLTree.countChildren_as_children_card]

-- ## LocallyFinite.children

lemma children_finite : Set.Finite 𝕍{T, v→} :=
  Set.finite_of_encard_eq_coe <| Eq.symm <| @countChildren_as_children_card T v

noncomputable instance : Fintype 𝕍{T, v→} :=
  @Fintype.ofFinite _ <| Set.finite_coe_iff.2 <| children_finite T v

noncomputable instance : FunLike 𝕋 𝕍 ℕ where
  coe T := T.countChildren
  coe_injective' T1 T2 h := by
    ext v; simp only at h; have := congrArg (fun f => f v) h; simpa using this

-- -- ## Measurable countChildren
-- section
-- variable {T : 𝕋} (v : 𝕍) (n : ℕ)

-- @[measurability]
-- theorem countChildren_measurable : Measurable (fun T => ♯{T, v→}) := by sorry

-- @[measurability]
-- theorem generationSizeFromLevel_measurable : Measurable (fun T => ♯{T,ℒ(n)→}) := by sorry

-- end

end LocallyFinite

end RLTree
