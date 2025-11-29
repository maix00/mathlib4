import Mathlib.Probability.RandomGraph.RootedForest
import Mathlib.Probability.RandomGraph.TreeNode
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Instances.ENat
import Mathlib.Probability.Independence.Basic

/- ## RootedLabeledTree
## generateSet
## RootedLabeledTree
## generateTree
## countChildren
## generate
## descendantTreeAt
## height
## truncation
## heightCongr
## treeDist
## MetricSpace
## CompleteSpace
## setOfLevelAtMost
## setOfLevel
## generationSizeFromLevel
## LocallyFinite
## LocallyFinite.truncation
## LocallyFinite.MetricSpace
## LocallyFinite.CompleteSpace
##
-/

open TreeNode ENNReal NNReal ENat

-- ## generateSet
namespace RootedLabeledTree

inductive generateSet (s : Set 𝕍) : Set 𝕍
  | mem : (l : 𝕍) → s l → generateSet s l
  | tail : (m : ℕ) → (l : 𝕍) → generateSet s (m :: l) → generateSet s l
  | less : (m : ℕ) → (l : _) → generateSet s (m :: l) → (n : ℕ) → n ≤ m → generateSet s (n :: l)

def _root_.RootedLabeledTree := {s // generateSet s = s ∧ s ≠ ∅}

scoped[RootedLabeledTree] notation "𝕋₀" => RootedLabeledTree

variable {T : 𝕋₀} {v : 𝕍}

instance : Coe 𝕋₀ (Set 𝕍) where
  coe T := T.val

instance : Membership 𝕍 𝕋₀ where
  mem T l := l ∈ T.val

lemma mem_iff : v ∈ T ↔ v ∈ T.val := ⟨by
  intro h; exact h, by simp [instMembershipTreeNode]⟩

@[simp] lemma mem_set {h : v ∈ T.val} : v ∈ T := mem_iff.2 h

lemma set_eq_of_eq {T1 T2 : 𝕋₀} (h : T1 = T2) : T1.val = T2.val :=
  congrArg Subtype.val h

instance : HasSubset 𝕋₀ where
  Subset T1 T2 := T1.val ⊆ T2.val

@[simp] lemma nil_generate : generateSet ∅ = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false]; by_contra hv; induction hv <;> assumption

@[simp] lemma generateSet_eq_self_of_val : generateSet T.val = T.val := T.property.1

@[simp] lemma nonempty_of_val : T.val ≠ ∅ := T.property.2

lemma generateSet_mono : Monotone generateSet := by
  intro _ _ _; simp only [Set.le_eq_subset, Set.subset_def]; intro _ h; induction h with
  | mem => exact generateSet.mem _ <| Set.mem_of_subset_of_mem ‹_› ‹_›
  | tail => exact generateSet.tail _ _ ‹_›
  | less => exact generateSet.less _ _ ‹_› _ ‹_›

lemma generateSet_subset (s : Set 𝕍) : s ⊆ generateSet s := by
  intro _ _; exact generateSet.mem _ ‹_›

lemma generateSet_proj (s : Set 𝕍) :
  generateSet (generateSet s) = generateSet s := by
  ext; constructor
  · intro h; induction h with
      | mem => assumption
      | tail => exact generateSet.tail _ _ ‹_›
      | less => exact generateSet.less _ _ ‹_› _ ‹_›
  · intro; exact generateSet.mem _ ‹_›

lemma generateSet_idempotent : @IsIdempotentElem _ ⟨Function.comp⟩ generateSet := by
  simp [IsIdempotentElem]; ext; constructor
  · intro h; induction h with
      | mem => assumption
      | tail => exact generateSet.tail _ _ ‹_›
      | less => exact generateSet.less _ _ ‹_› _ ‹_›
  · intro; exact generateSet.mem _ ‹_›

lemma nonempty_of_nonempty (s : Set 𝕍) (hs : s ≠ ∅) : generateSet s ≠ ∅ := by
  obtain ⟨l, hv⟩ := not_not.1 <| not_imp_not.2 Set.not_nonempty_iff_eq_empty.1 hs
  apply not_imp_not.2 (@Set.not_nonempty_iff_eq_empty _ (generateSet s)).2; apply not_not.2
  exact ⟨l, generateSet.mem l hv⟩

@[simp] lemma nil_mem {T : 𝕋₀} : [] ∈ T := by
  obtain ⟨l, h⟩ := Set.nonempty_iff_ne_empty.2 T.property.2; induction l with
  | nil => exact h
  | cons m v' ih => exact ih <| T.property.1 ▸ generateSet.tail m v' <| T.property.1 ▸ h

@[simp] lemma tail_mem {T : 𝕋₀} {m : ℕ} {l : 𝕍} (h : m :: l ∈ T) : l ∈ T :=
  T.property.1 ▸ generateSet.tail m l <| T.property.1 ▸ mem_iff.1 h

@[simp] lemma tail_mem' {T : 𝕋₀} {l : 𝕍} {h : l ∈ T} : l.tail ∈ T := by
  cases l <;> grind [tail_mem]

@[simp] lemma drop_mem {T : 𝕋₀} {l : 𝕍} {h : l ∈ T} {n : ℕ} :
  l.drop n ∈ T := by
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [←@List.drop_drop _ 1 n l, List.drop_one]; exact @tail_mem' T (l.drop n) ih

@[simp] lemma less_mem {T : 𝕋₀} {m n : ℕ} {l : 𝕍} (h : m :: l ∈ T)
  (hnm : n ≤ m) : n :: l ∈ T :=  mem_iff.2 <| T.property.1 ▸ generateSet.less m l
  (Eq.symm T.property.1 ▸ mem_iff.1 h) n hnm

-- ## generateTree

def generateTree (s : Set 𝕍) (hs : s ≠ ∅) : 𝕋₀ :=
  ⟨generateSet s, generateSet_proj s, nonempty_of_nonempty s hs⟩

@[simp] lemma generateTree_val (T : 𝕋₀) : generateTree T.val T.nonempty_of_val = T := by
  simp [generateTree]

def rootTree := generateTree {[]} (by simp)

@[simp] lemma rootTree_aux : generateSet {[]} = {[]} := by
  ext; constructor
  · intro h; induction h <;> first | assumption | contradiction
  · exact generateSet.mem _

@[simp] lemma rootTree_eq : rootTree = ⟨({[]} : Set 𝕍), rootTree_aux, by simp⟩  := by
  simp [rootTree, generateTree]

-- ## countChildren

noncomputable def countChildren (T : 𝕋₀) (v : 𝕍) : ℕ∞ :=
  (⨆ (m : ℕ) (_ : m :: v ∈ T), m + 1 : WithTop ℕ)

scoped[RootedLabeledTree] notation "#{" T ", " v "}ₑ" => @countChildren T v

@[simp] lemma countChildren_eq_zero {T : 𝕋₀} {v : 𝕍} (h : ∀ m, m :: v ∉ T) : #{T, v}ₑ = 0 := by
  simp [countChildren, *]

@[simp] lemma countChildren_eq_top {T : 𝕋₀} {v : 𝕍} (h : ∀ m, m :: v ∈ T) : #{T, v}ₑ = ⊤ := by
    simp [countChildren, *]
    rw [iSup_eq_top (fun (m : ℕ) => (m + 1 : WithTop ℕ))]
    intro b hb
    match b with
    | ⊤ => contradiction
    | some b' =>
      use b'; apply WithTop.lt_iff_exists.2
      use b'; simp [WithTop.some_eq_coe]; intro c hc
      have : c = b' + 1 := by have := WithTop.add_eq_coe.1 hc; aesop
      simp [*]

@[simp] lemma countChildren_eq_top_iff {T : 𝕋₀} {v : 𝕍} : (∀ m, m :: v ∈ T) ↔ #{T, v}ₑ = ⊤ := by
  constructor
  · exact countChildren_eq_top
  · intro h; simp [countChildren] at h
    rw [iSup₂_eq_top (fun m => fun (_ : m :: v ∈ T) => (m + 1 : WithTop ℕ))] at h
    intro m; obtain ⟨n, hn, hmn⟩ := h (m + 1) (by simp)
    obtain ⟨m', hm', h'⟩ := WithTop.lt_iff_exists.1 hmn
    specialize h' (n + 1) (by simp)
    rw [show (m : WithTop ℕ) + 1 = ↑(m + 1) from by simp] at hm'
    rw [←(@WithTop.coe_inj ℕ (m + 1) m').1 hm'] at h'; simp at h'
    exact mem_iff.2 <| T.property.1 ▸ generateSet.less n v
      (Eq.symm T.property.1 ▸ mem_iff.1 hn) m (by omega)

@[simp] lemma countChildren_ge {T : 𝕋₀} {v : 𝕍} {m : ℕ} (h : m :: v ∈ T) : m + 1 ≤ #{T, v}ₑ := by
  simp [countChildren]; exact @le_iSup₂ (WithTop ℕ) ℕ _ _ _ _ h

lemma countChildren_mem {T : 𝕋₀} {v : 𝕍} {h : #{T, v}ₑ ≠ ⊤} {h' : #{T, v}ₑ ≠ 0} :
  ∃ m : ℕ, m :: v ∈ T ∧ #{T, v}ₑ = m + 1 := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  have : n ≠ 0 := by by_contra h'; have := Eq.symm <| h' ▸ hn; simp at this; contradiction
  use (n - 1); constructor
  · have : ↑n - 1 < #{T, v}ₑ := by
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
    simp at hn'1; obtain ⟨n', hn'3, hn'4⟩ := hn'1
    have : n' = n - 1 := by have := WithTop.coe_inj.1 hn'4; simp at this; omega
    exact this ▸ hn'3
  · rw [show ↑(n - 1) + 1 = (n : WithTop ℕ) from by
      set n' := n - 1 with hn'; rw [show n = n' + 1 from by omega]; aesop];
    exact Eq.symm hn

lemma countChildren_ge_iff {T : 𝕋₀} {v : 𝕍} {m : ℕ} : m :: v ∈ T ↔ m + 1 ≤ #{T, v}ₑ := by
  constructor
  · exact countChildren_ge
  · intro h
    by_cases #{T, v}ₑ = ⊤
    · exact countChildren_eq_top_iff.2 ‹_› m
    · set n := #{T, v}ₑ.untop ‹_› with hn
      have hn : ↑n = #{T, v}ₑ := Eq.symm <| (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hn
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
      exact mem_iff.2 <| T.property.1 ▸ generateSet.less (n - 1) v
        (Eq.symm T.property.1 ▸ mem_iff.1 this) m (by omega)

private def ext_of_countChildren_aux {T1 T2 : 𝕋₀} (h : ∀ v, #{T1, v}ₑ = #{T2, v}ₑ) (v : 𝕍) :
  v ∈ T1 → v ∈ T2 := by
  intro hv; cases v with
  | nil => exact T2.nil_mem
  | cons m v' => exact countChildren_ge_iff.2 <| h v' ▸ T1.countChildren_ge hv

@[ext] def ext_of_countChildren (T1 T2 : 𝕋₀) (h : ∀ v, #{T1, v}ₑ = #{T2, v}ₑ) : T1 = T2 := by
  apply Subtype.ext_iff.2; ext v; constructor
  · exact ext_of_countChildren_aux h v
  · exact ext_of_countChildren_aux (fun v => Eq.symm <| h v) v

noncomputable instance : FunLike 𝕋₀ 𝕍 ℕ∞ where
  coe T := T.countChildren
  coe_injective' T1 T2 h := by
    ext l; simp at h; have := congrArg (fun f => f l) h; simpa using this

-- ## descendantTreeAt

def descendantTreeAt {T : 𝕋₀} (x : 𝕍) (hx : x ∈ T) : 𝕋₀ := ⟨
  {x' | x' ++ x ∈ T}, by
    obtain ⟨h1, h2⟩ := T.property
    ext l; constructor
    · intro hv
      induction hv with
      | mem => assumption
      | tail m v' hv' ih =>
        exact mem_iff.2 <| T.property.1 ▸ generateSet.tail m (v' ++ x)
          <| Eq.symm T.property.1 ▸ mem_iff.1 ih
      | less m v' hv' n hnm ih =>
        exact mem_iff.2 <| T.property.1 ▸ generateSet.less m (v' ++ x)
          (Eq.symm T.property.1 ▸ mem_iff.1 ih) n hnm
    · intro hv; exact generateSet.mem l hv
    , by
      apply not_imp_not.2 Set.not_nonempty_iff_eq_empty.2; simp only [not_not]
      exact ⟨[], by simp [*]⟩
  ⟩

-- ## height

noncomputable def height (T : 𝕋₀) : ℕ∞ := (⨆ (v : 𝕍) (_ : v ∈ T), ‖v‖ₕ : WithTop ℕ)

scoped[RootedLabeledTree] notation "‖" T "‖ₕ" => height T

@[simp] lemma mem_length_at_most_height {T : 𝕋₀} : ∀ v ∈ T, ‖v‖ₕ ≤ ‖T‖ₕ := by
  simp [height]; exact @le_iSup₂ _ _ _ _ (fun v => fun (_ : v ∈ T) => (‖v‖ₕ : WithTop ℕ))

-- ## truncation
section
variable {T : 𝕋₀}

def truncation (T : 𝕋₀) (n : ℕ) : 𝕋₀ := ⟨{v | ‖v‖ₕ ≤ n ∧ v ∈ T}, by
    obtain ⟨h1, h2⟩ := T.property; ext l; constructor
    · intro hv; simp
      induction hv with
      | mem v' ih=> simp [setOf] at ih; exact ih
      | tail m v' hv' ih =>
        exact ⟨by grind, mem_iff.2 <| T.property.1 ▸ generateSet.tail m v'
          <| Eq.symm T.property.1 ▸ mem_iff.1 ih.2⟩
      | less m v' hv' n hnm ih =>
        exact ⟨by grind, mem_iff.2 <| T.property.1 ▸ generateSet.less m v'
          (Eq.symm T.property.1 ▸ mem_iff.1 ih.2) n hnm⟩
    · intro hv; exact generateSet.mem l hv
    , by
      apply not_imp_not.2 Set.not_nonempty_iff_eq_empty.2; simp only [not_not]
      exact ⟨[], by simp [*]⟩
  ⟩

scoped[RootedLabeledTree] notation T "↾(" n ")" => @truncation T n

@[simp] lemma truncation_zero : T↾(0) = rootTree := by
  rw [rootTree_eq, truncation]; apply Subtype.ext; simp; ext; constructor <;> simp <;> aesop

lemma truncation_height_at_most (n : ℕ) : ‖T↾(n)‖ₕ ≤ n := by
  simp [truncation, height]; apply @iSup₂_le (WithTop ℕ); intro l hv; exact ENat.coe_le_coe.2 hv.1

@[simp] lemma truncation_mem_length_at_most (n : ℕ) : ∀ v ∈ T↾(n), ‖v‖ₕ ≤ n := by
  intro v hv; have := le_trans (mem_length_at_most_height v hv) (@truncation_height_at_most T n)
  simp at this; exact this

@[simp] lemma truncation_truncation {n m : ℕ} : T↾(n)↾(m) = T↾(min n m) := by
  simp [truncation, mem_iff]; apply Subtype.val_inj.1; ext u; simp; aesop

@[simp] lemma mem_of_mem_truncation {n : ℕ} {l : 𝕍} (hv : l ∈ T↾(n)) : l ∈ T := hv.2

@[simp] lemma truncation_subset {n : ℕ} : T↾(n) ⊆ T := by
  dsimp [instHasSubset]; simp [Set.subset_def]; exact @mem_of_mem_truncation T n

@[simp] lemma mem_higher_truncation_of_mem_truncation {n m : ℕ} (hnm : n < m) {l : 𝕍}
  (hv : l ∈ T↾(n)) : l ∈ T↾(m) := by simp [mem_iff, truncation] at *; exact ⟨by omega, hv.2⟩

@[simp] lemma mem_truncation_of_mem {n : ℕ} {v : 𝕍} (hv : ‖v‖ₕ ≤ n) (hv' : v ∈ T) : v ∈ T↾(n) := by
  simp [mem_iff, truncation] at *; exact ⟨by omega, hv'⟩

@[simp] lemma mem_truncation_of_mem_other_truncation {n m : ℕ} {v : 𝕍} (hv : ‖v‖ₕ ≤ n)
  (hv' : v ∈ T↾(m)) : v ∈ T↾(n) := by simp [mem_iff, truncation] at *; exact ⟨by omega, hv'.2⟩

lemma ext_of_truncation {T1 T2 : 𝕋₀} (h : ∀ n, T1↾(n) = T2↾(n)) : T1 = T2 := by
  apply Subtype.ext_iff.2; ext l; cases l with
  | nil => constructor <;> intro <;> exact nil_mem
  | cons m v' =>
    have := set_eq_of_eq <| h (‖v'‖ₕ + 1); simp [truncation, setOf] at this
    have := congr this (@rfl _ (m :: v')); simpa
end

-- ## heightCongr

noncomputable def heightCongr (T1 T2 : 𝕋₀) : ℕ∞ :=
  (⨆ (n : ℕ) (_ : T1↾(n) = T2↾(n)), n : WithTop ℕ)

scoped[RootedLabeledTree] notation "‖" T1 ", " T2 "‖ₕ" => heightCongr T1 T2

@[simp] lemma heightCongr_comm {T1 T2 : 𝕋₀} : ‖T1, T2‖ₕ = ‖T2, T1‖ₕ := by
  simp [heightCongr, eq_comm]

lemma ext_of_top_heightCongr {T1 T2 : 𝕋₀} (h : ‖T1, T2‖ₕ = ⊤) : T1 = T2 := by
  simp [heightCongr] at h
  have h' := (@iSup₂_eq_top (WithTop ℕ) ℕ _ _ (fun n => fun _ => n)).1 h
  apply ext_of_truncation; intro n; obtain ⟨m, hm, hnm⟩ := h' n (by simp)
  have := ENat.coe_lt_coe.1 hnm
  have := congrArg (fun T : 𝕋₀ => T↾(n)) hm
  simp [(show min m n = n from by omega)] at this; exact this

@[simp] lemma heightCongr_self_eq_top {T : 𝕋₀} : ‖T, T‖ₕ = ⊤ := by
  simp [heightCongr]; apply (@iSup_eq_top (WithTop ℕ) ℕ _ _).2; intro n hn
  set n' := n.untop (by aesop) with hn'; have := (WithTop.untop_eq_iff _).1 (Eq.symm hn')
  use n' + 1; rw [this]; exact WithTop.coe_lt_coe.2 (show n' < n' + 1 from by omega)

@[simp] lemma heightCongr_apply {T T' : 𝕋₀} (n : ℕ) (hn : n ≤ ‖T, T'‖ₕ) : T↾(n) = T'↾(n) := by
  by_cases h : ‖T, T'‖ₕ = ⊤
  · exact congrArg (fun T => T↾(n)) <| ext_of_top_heightCongr h
  · by_cases n = 0
    · subst_vars; simp
    · have : n - 1 < ‖T, T'‖ₕ := by
        obtain ⟨n', hn'⟩ := WithTop.ne_top_iff_exists.1 h
        rw [←hn'] at ⊢ hn; simp at ⊢ hn; apply ENat.coe_lt_coe.2; omega
      rw [heightCongr, iSup_subtype', iSup] at hn this
      obtain ⟨n', hn'1, hn'2⟩ := (@lt_sSup_iff (WithTop ℕ) _ _ _).1 this
      simp at hn'1; obtain ⟨n'', hn'3, hn'4⟩ := hn'1
      simp [←hn'4] at hn'2; have := ENat.coe_lt_coe.1 hn'2
      have := congrArg (fun T => T↾(n)) hn'3
      simp [show min n'' n = n from by omega] at this; exact this

@[simp] lemma heightCongr_apply_iff {T T' : 𝕋₀} (n : ℕ) :
  n ≤ ‖T, T'‖ₕ ↔ T↾(n) = T'↾(n) := by
  constructor
  · exact heightCongr_apply n
  · intro hn; rw [heightCongr, iSup_subtype', iSup]
    apply (@le_sSup_iff (WithTop ℕ) _ _ _).2; simp [upperBounds]
    intro m hm; exact hm n hn

lemma heightCongr_ultra (T1 T2 T3 : 𝕋₀) :
  min ‖T1, T2‖ₕ ‖T2, T3‖ₕ ≤ ‖T1, T3‖ₕ := by
  by_cases h' : ‖T1, T3‖ₕ = ⊤
  · simp [*]
  · by_contra h; simp at h
    set m := ‖T1, T3‖ₕ with hm
    set m' := m.untop ‹_› with hm'
    have hm'' := (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hm'
    have : T1↾(m' + 1) = T2↾(m' + 1) :=
      @heightCongr_apply T1 T2 (m' + 1) (by
        have := hm'' ▸ h.1
        by_cases ‖T1, T2‖ₕ = ⊤
        · simp [*]
        · set n := ‖T1, T2‖ₕ with hn
          set n' := n.untop ‹_› with hn'
          have hn'' := (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hn'
          have := ENat.coe_lt_coe.1 <| hn'' ▸ this
          rw [hn'']; apply ENat.coe_le_coe.2; omega
        )
    have : T2↾(m' + 1) = T3↾(m' + 1) :=
      @heightCongr_apply T2 T3 (m' + 1) (by
        have := hm'' ▸ h.2
        by_cases ‖T2, T3‖ₕ = ⊤
        · simp [*]
        · set n := ‖T2, T3‖ₕ with hn
          set n' := n.untop ‹_› with hn'
          have hn'' := (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hn'
          have := ENat.coe_lt_coe.1 <| hn'' ▸ this
          rw [hn'']; apply ENat.coe_le_coe.2; omega
        )
    have : T1↾(m' + 1) = T3↾(m' + 1) := Eq.trans ‹_› ‹_›
    have := @le_iSup₂_of_le (WithTop ℕ) ℕ (fun n => T1↾(n) = T3↾(n)) _
      (m' + 1) (fun n => fun _ => (n : WithTop ℕ)) (m' + 1) ‹_› (by simp); simp at this
    have heq := @rfl _ ‖T1, T3‖ₕ; conv at heq => left; simp [heightCongr]
    conv at this => rhs; rw [heq, ←hm, hm'']
    have := ENat.coe_le_coe.1 this; simp at this

-- ## treeDist

noncomputable def treeDist (T1 T2 : 𝕋₀) : ℝ :=
  ((1 + (‖T1, T2‖ₕ : ℝ≥0∞))⁻¹).toReal

scoped[RootedLabeledTree] notation "‖" T1 ", " T2 "‖ₜ₁" => treeDist T1 T2

lemma ext_of_zero_treeDist {T1 T2 : 𝕋₀} (h12 : ‖T1, T2‖ₜ₁ = 0) : T1 = T2 := by
  simp [treeDist, ENNReal.toReal, ENNReal.toNNReal] at h12
  rcases h12 with (h12|h12)
  · have h12 := ENNReal.inv_eq_zero.1 h12; simp at h12
    exact ext_of_top_heightCongr h12
  · have := ENNReal.inv_eq_top.1 h12; aesop

private lemma treeDist_eq_aux {T1 T2 : 𝕋₀} : (fun (x : ℕ∞)
  => - ((1 + (x : ℝ≥0∞))⁻¹).toReal) ‖T1, T2‖ₕ = - ‖T1, T2‖ₜ₁ := by simp [treeDist]

private lemma treeDist_mono' : StrictMono fun (x : ℕ∞) => - ((1 + (x : ℝ≥0∞))⁻¹).toReal := by
  simp only [StrictMono]; intro a b hab
  have : a.toENNReal < b.toENNReal := by simp [*]
  have : 1 + a.toENNReal < 1 + b.toENNReal := by
    apply (ENNReal.add_lt_add_iff_left (show 1 ≠ ⊤ from by simp)).2; simp [*]
  have := ENNReal.inv_lt_inv.2 this
  have := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 this
  simp only [neg_lt_neg_iff, *]

private lemma treeDist_mono : Monotone fun (x : ℕ∞) => - ((1 + (x : ℝ≥0∞))⁻¹).toReal := by
  apply StrictMono.monotone; exact treeDist_mono'

lemma treeDist_ultra (T1 T2 T3 : 𝕋₀) :
  ‖T1, T3‖ₜ₁ ≤ max ‖T1, T2‖ₜ₁ ‖T2, T3‖ₜ₁ := by
  simp; by_contra h; simp at h
  have := heightCongr_ultra T1 T2 T3; contrapose this; simp; constructor
  · by_contra h'; simp at h'; have := treeDist_mono h'
    conv at this => left; rw [@treeDist_eq_aux T1 T2]
    conv at this => right; rw [@treeDist_eq_aux T1 T3]
    simp at this; exact lt_iff_not_ge.1 h.1 this
  · by_contra h'; simp at h'; have := treeDist_mono h'
    conv at this => left; rw [@treeDist_eq_aux T2 T3]
    conv at this => right; rw [@treeDist_eq_aux T1 T3]
    simp at this; exact lt_iff_not_ge.1 h.2 this

-- ## MetricSpace

noncomputable instance : MetricSpace 𝕋₀ where
  dist := treeDist
  dist_self := by simp [treeDist]
  dist_comm := by simp [treeDist]
  dist_triangle T1 T2 T3 := le_trans (treeDist_ultra T1 T2 T3) <| max_le_add_of_nonneg (by
    simp [treeDist]) (by simp [treeDist])
  eq_of_dist_eq_zero := ext_of_zero_treeDist

instance : IsUltrametricDist 𝕋₀ where
  dist_triangle_max := treeDist_ultra

--  ## CompleteSpace

private instance instUniformityBasis' : (uniformity 𝕋₀).HasBasis
  (fun _ => True) (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ℝ≥0∞))⁻¹}) :=
  EMetric.mk_uniformity_basis (by simp) (by
    simp; intro ε hε; obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε); use n
    simp [ENNReal.inv_lt_iff_inv_lt] at hn; simp [ENNReal.inv_le_iff_inv_le]
    exact le_of_lt <| lt_trans hn (by apply ENNReal.coe_lt_coe.2; simp))

def uniformityBasis := fun n => {p : 𝕋₀ × 𝕋₀ | (p.1)↾(n + 1) = (p.2)↾(n + 1)}

private lemma uniformityBasis_eq_aux : (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ℝ≥0∞))⁻¹})
  = uniformityBasis := by
  ext n p; simp [uniformityBasis, edist, PseudoMetricSpace.edist, treeDist]; constructor
  · intro h; have h := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 h
    simp [-ENNReal.toReal_inv, ←ENNReal.toReal_inv] at h
    have h := (ENNReal.add_lt_add_iff_left (by simp)).1 h
    rw [show (n : ℝ≥0∞) = ((n : ℕ∞) : ℝ≥0∞) from by simp] at h
    simp [-ENat.toENNReal_coe] at h
    exact heightCongr_apply _ <| (ENat.add_one_le_iff (by simp)).2 h
  · intro h
    have := (heightCongr_apply_iff _).2 h
    set m := heightCongr p.1 p.2 with hm
    conv => left; congr; congr; congr; congr; right; congr; rw [←hm]
    apply (ENNReal.toReal_lt_toReal (by simp) (by simp)).1
    simp [-ENNReal.toReal_inv, ←ENNReal.toReal_inv]
    by_cases h' : m = ⊤
    · simp [h']
    · have := (ENat.lt_add_one_iff h').2 this
      have := ENat.toENNReal_lt.2 this; simp at this
      conv => lhs; rw [add_comm]
      conv => rhs; rw [add_comm]
      exact this

instance instUniformityBasis : (uniformity 𝕋₀).HasBasis
  (fun _ => True) uniformityBasis := uniformityBasis_eq_aux ▸ instUniformityBasis'

instance : CompleteSpace 𝕋₀ where
  complete := by
    intro f hf; have hf' := (by simpa [Cauchy] using hf)
    let E (n : ℕ) := {p : 𝕋₀ × 𝕋₀ | (p.1)↾(n) = (p.2)↾(n)}
    have memE (n : ℕ): E n ∈ uniformity 𝕋₀ := by
      by_cases h : n = 0
      · simp [h, E]
      · have : E n = uniformityBasis (n - 1) := by
          simp only [uniformityBasis, E]; conv => right; rw [(show n - 1 + 1 = n from by omega)]
        exact (Filter.HasBasis.mem_iff instUniformityBasis).2 (by use (n - 1); simp [this])
    have (n : ℕ) : ∃ Sn ∈ f, Sn.Nonempty ∧ Sn ×ˢ Sn ⊆ E n := by
      simp only [LE.le] at hf'; have hf'2 := @hf'.2 (E n) (memE n)
      obtain ⟨Sn, hSmem, _⟩ := Filter.mem_prod_same_iff.1 hf'2; use Sn
      simp only [and_true, true_and, *]; by_contra h
      exact (not_imp_not.2 Filter.empty_mem_iff_bot.1 <| Filter.neBot_iff.1 hf'.1)
        <| (Set.not_nonempty_iff_eq_empty.1 h) ▸ hSmem
    choose S hSmem hSne hSsub using this
    have hSsub' (n : ℕ) (T1 T2) : T1 ∈ S n → T2 ∈ S n → T1↾(n) = T2↾(n) := by
      intro h1 h2; have : (T1, T2) ∈ (S n) ×ˢ (S n) := by
        simp only [Set.mem_prod, and_self, h1, h2]
      have := Set.mem_of_subset_of_mem (hSsub n) this;
      simp only [Set.mem_setOf_eq, E] at this; exact this
    choose T' hT'mem using hSne
    have hT'tr (n m : ℕ) : (T' (n + m))↾(n) = (T' n)↾(n) := by
      obtain ⟨U, hU⟩ : (S (n + m) ∩ S n).Nonempty := by
        by_contra h; exact (not_imp_not.2 Filter.empty_mem_iff_bot.1 <| Filter.neBot_iff.1 hf'.1)
          <| (Set.not_nonempty_iff_eq_empty.1 h) ▸ f.inter_mem (hSmem (n + m)) (hSmem n)
      have h1 := hSsub' (n + m) U (T' (n + m)) ((Set.mem_inter_iff _ _ _).1 hU).1 (hT'mem (n + m))
      have h2 := hSsub' n U (T' n) ((Set.mem_inter_iff _ _ _).1 hU).2 (hT'mem n)
      have h1 := congrArg (fun T => T↾(n)) h1; simp at h1
      exact h1 ▸ h2
    set Tval : Set 𝕍 := {l | l ∈ (T' ‖l‖ₕ)↾(‖l‖ₕ)}
    set T : 𝕋₀ := ⟨Tval, by
      ext l; constructor
      · intro hv; induction hv with
        | mem v' hv' => assumption
        | tail m v' hv' ih =>
          simp [Tval, ←hT'tr ‖v'‖ₕ 1]
          exact mem_truncation_of_mem_other_truncation (by omega) <| tail_mem ih
        | less m v' hv' n hnm ih =>
          exact @less_mem ((T' (‖v'‖ₕ + 1))↾(‖v'‖ₕ + 1)) m n v' ih hnm
      · exact generateSet.mem l
      , Set.nonempty_iff_ne_empty.1 ⟨[], by simp [Tval]⟩⟩
    use T; have := @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T
    simp only [uniformityBasis, Set.mem_setOf_eq] at this
    refine (this.ge_iff.mpr ?_); simp only [forall_const]
    have hTtr (n : ℕ) : T↾(n) = (T' n)↾(n) := by
      simp [truncation]; apply Subtype.coe_inj.1; ext l; simp; intro hv
      simp [mem_iff, T, Tval, truncation]
      have := (show ‖l‖ₕ + (n - ‖l‖ₕ) = n from by omega) ▸ hT'tr ‖l‖ₕ (n - ‖l‖ₕ)
      constructor
      · intro hv'; exact @mem_of_mem_truncation _ ‖l‖ₕ _
          (this ▸ mem_truncation_of_mem (by omega) hv')
      · intro hv'; exact @mem_of_mem_truncation _ ‖l‖ₕ _
          (Eq.symm this ▸ mem_truncation_of_mem (by omega) hv')
    intro n; exact f.sets_of_superset (hSmem (n + 1)) (by
      simp only [Set.subset_def, Set.mem_setOf_eq]; intro U hU; rw [hTtr (n + 1)]
      exact hSsub' (n + 1) U (T' (n + 1)) hU (hT'mem (n + 1)))

instance : MeasurableSpace 𝕋₀ := borel 𝕋₀

-- ## generateSet

private def generate_tail_of_single (l : 𝕍) : Set 𝕍 :=
  ⋃ (n : Fin (‖l‖ₕ + 1)), {l.drop n}

@[simp] private lemma finite_generate_tail_of_single (l : 𝕍) :
  (generate_tail_of_single l).Finite := by
  simp only [generate_tail_of_single]; apply Set.finite_iUnion; simp

@[simp] private lemma mem_self_generate_tail_of_single (l : 𝕍) :
  l ∈ generate_tail_of_single l := by simp [generate_tail_of_single]; use 0; simp

@[simp] private lemma treeNode_eq_of_mem_generate_tail_of_single_of_same_length (v u : 𝕍)
  (hvu : ‖v‖ₕ = ‖u‖ₕ) (hu : u ∈ generate_tail_of_single v) : u = v := by
  simp [generate_tail_of_single] at hu; obtain ⟨n, hn⟩ := hu
  have := n.is_lt; set n' : ℕ := ↑n with hn'
  have := Eq.symm hvu ▸ congrArg List.length hn; simp at this
  have := (show n' = 0 from by omega) ▸ hn; simp at this; exact Eq.symm this

private def generate_tail (s : Set 𝕍) : Set 𝕍 := ⋃ l : ↑s, generate_tail_of_single l

@[simp] private lemma finite_generate_tail_of_finite (s : Set 𝕍) (hs : s.Finite) :
  (generate_tail s).Finite := by
  simp only [generate_tail]
  apply fun h => @Set.finite_iUnion _ _ (Set.finite_coe_iff.2 hs) _ h; simp

@[simp] private lemma mem_self_generate_tail (l : 𝕍) (s : Set 𝕍) (h : l ∈ ↑s) :
  l ∈ generate_tail s := by simp [generate_tail]; use l; simp [*]

@[simp] private lemma tail_mem_of_mem_generate_tail (m : ℕ) (l : 𝕍) (s : Set 𝕍)
  (h : m :: l ∈ generate_tail s) : l ∈ generate_tail s := by
  simp [generate_tail] at h ⊢; obtain ⟨v', hv'1, hv'2⟩ := h
  simp [generate_tail_of_single] at hv'2 ⊢; obtain ⟨⟨n, hn⟩, hv'2⟩ := hv'2; simp at hv'2
  by_cases hv'3 : n = ‖v'‖ₕ
  · simp [hv'3] at hv'2
  · use v'; simp [*]; use ⟨n + 1, by omega⟩; simp only [←@List.drop_drop _ 1 n v', hv'2,
    List.drop_succ_cons, List.drop_zero]

private def generate_less_of_single (l : 𝕍) (hv : l ≠ []) : Set 𝕍 :=
  ⋃ (n : Fin (l.head hv + 1)), {(n : ℕ) :: l.tail}

@[simp] private lemma finite_generate_less_of_single (l : 𝕍) (hv : l ≠ []) :
  (generate_less_of_single l hv).Finite := by
  simp only [generate_less_of_single]; apply Set.finite_iUnion; simp

@[simp] private lemma mem_self_generate_less_of_single (l : 𝕍) (hv : l ≠ []) :
  l ∈ generate_less_of_single l hv := by
  simp [generate_less_of_single]; use ⟨l.head hv, by omega⟩; simp

@[simp] private lemma same_length_of_mem_generate_less_of_single (v u : 𝕍) (hv : v ≠ [])
  (hu : u ∈ generate_less_of_single v hv) : ‖v‖ₕ = ‖u‖ₕ := by
  simp [generate_less_of_single] at hu; obtain ⟨m, hu'⟩ := hu
  have : ‖v‖ₕ ≠ 0 := (by simp [hv]); have := congrArg List.length hu'; simp at this
  rw [(show ‖v‖ₕ - 1 + 1 = ‖v‖ₕ from by omega)] at this; exact this

private def generate_less (s : Set 𝕍) (hs : [] ∉ s) :=
  ⋃ l : ↑s, generate_less_of_single l (by aesop)

@[simp] private lemma finite_generate_less (s : Set 𝕍) (hs : [] ∉ s) (hs' : s.Finite) :
  (generate_less s hs).Finite := by
  simp only [generate_less]
  apply fun h => @Set.finite_iUnion _ _ (Set.finite_coe_iff.2 hs') _ h; simp

@[simp] private lemma mem_self_generate_less (l : 𝕍) (s : Set 𝕍) (hs : [] ∉ s)
  (hv' : l ∈ ↑s) : l ∈ generate_less s hs := by simp [generate_less]; use l, hv'; simp

@[simp] private lemma cons_mem_of_mem_generate_less (s : Set 𝕍) (hs : [] ∉ s) (m : ℕ)
  (l : 𝕍) (hv : m :: l ∈ generate_less s hs) : ∃ n, m ≤ n ∧ n :: l ∈ s := by
  simp [generate_less] at hv; obtain ⟨v', hv'1, hv'2⟩ := hv
  simp [generate_less_of_single] at hv'2; obtain ⟨⟨⟨m', hm'⟩, hv'2⟩, hv'3⟩ := hv'2
  cases v' with
  | nil => exact False.elim <| hs hv'1
  | cons n v' =>
    use n; simp_all only [List.tail_cons]; simp only [List.head_cons] at hm'; subst_vars
    exact ⟨by omega, hv'1⟩

@[simp] private lemma less_mem_of_mem_generate_less (s : Set 𝕍) (hs : [] ∉ s) (n m : ℕ)
  (hmn : n ≤ m) (l : 𝕍) (hv : m :: l ∈ generate_less s hs) : n :: l ∈ generate_less s hs
  := by
  obtain ⟨n', hmn', hv'⟩ := cons_mem_of_mem_generate_less s hs m l hv
  simp [generate_less]; use n' :: l, hv'; simp [generate_less_of_single]; use ⟨n, by omega⟩

private lemma generateSet_eq_generate_tail_then_less (s : Set 𝕍) (hs : s ≠ ∅) :
  generateSet s = {[]} ∪ generate_less (generate_tail s \ {[]}) (by simp) := by
  ext l; simp only [Set.singleton_union, Set.mem_insert_iff]; constructor
  · intro hv; by_cases hv'1 : l = []
    · left; exact hv'1
    · right; induction hv with
      | mem v' hv'2 =>
        exact mem_self_generate_less v' _ _ (by simp [*]; exact mem_self_generate_tail v' s hv'2)
      | tail m v' hv'2 ih =>
        simp only [reduceCtorEq, not_false_eq_true, forall_const] at ih
        obtain ⟨n, hmn, ih⟩ := cons_mem_of_mem_generate_less _ _ m v' ih
        simp only [generate_less, Set.iUnion_coe_set, Set.mem_diff, Set.mem_singleton_iff,
          Set.mem_iUnion]; use v'
        simp only [Set.mem_diff, Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true,
          and_true] at ih; use ⟨tail_mem_of_mem_generate_tail n v' s ih, hv'1⟩
        exact mem_self_generate_less_of_single v' hv'1
      | less m v' hv'2 n hnm ih =>
        simp only [reduceCtorEq, not_false_eq_true, forall_const] at ih
        exact less_mem_of_mem_generate_less _ _ n m hnm v' ih
  · intro hv; by_cases hv'1 : l = []
    · exact hv'1 ▸ @nil_mem (generateTree s hs)
    · simp [hv'1, generate_less] at hv; obtain ⟨v', ⟨hv'2, hv'3⟩, hv'4⟩ := hv
      simp [generate_tail] at hv'2; obtain ⟨v'', hv'2, hv'5⟩ := hv'2
      simp [generate_tail_of_single] at hv'5; obtain ⟨⟨n, hn⟩, hv'5⟩ := hv'5; simp only at hv'5
      simp [generate_less_of_single] at hv'4; obtain ⟨⟨m, hm⟩, hv'4⟩ := hv'4; simp only at hv'4
      have := List.cons_head_tail hv'3 ▸ hv'5 ▸
        @drop_mem (generateTree s hs) v'' (generateSet.mem v'' hv'2) n
      exact hv'4 ▸ @less_mem (generateTree s hs) (v'.head hv'3) m v'.tail this (by omega)

@[simp] lemma finite_of_generateSet_finite {s : Set 𝕍} (hs : s.Finite) :
  Set.Finite (generateSet s) := by
  by_cases s = ∅
  · simp [nil_generate, *]
  · simp only [generateSet_eq_generate_tail_then_less s ‹_›, Set.singleton_union, Set.finite_insert]
    exact finite_generate_less _ (by aesop)
      <| @Finite.Set.finite_diff _ _ {[]} <| finite_generate_tail_of_finite s hs

@[simp] lemma finite_of_generate_finite {s : Set 𝕍} (hs : s ≠ ∅) (hs' : s.Finite) :
  Set.Finite (generateTree s hs).val := by
  simp [generateTree, finite_of_generateSet_finite hs']

@[simp] lemma finite_truncation_of_finite {T : 𝕋₀} (hT : Set.Finite T.val) (n : ℕ) :
  Set.Finite (T↾(n)).val := by
  have := @truncation_subset T n; simp only [instHasSubset] at this
  have : (T.val \ (T.val \ (T↾(n)).val)) = (T↾(n)).val := by simp [*]
  exact this ▸ @Finite.Set.finite_diff _ T.val (T.val \ (T↾(n)).val) hT

open TreeNode

variable (T : 𝕋₀)

-- ## setOfLevelAtMost

@[simp] def setOfLevelAtMost (n : ℕ) : Set 𝕍 := (T↾(n)).val

scoped[RootedLabeledTree] notation "𝕍{" T ",≤" n "}" => @setOfLevelAtMost T n

instance instMonotoneSetOfLevelAtMost : Monotone T.setOfLevelAtMost := by
  intro m n hmn; by_cases h : m = n
  · subst m; simp
  · exact @mem_higher_truncation_of_mem_truncation T m n (by omega)

-- ## setOfLevel

def setOfLevel (n : ℕ) : Set 𝕍 :=
  (T↾(n)).val \ if n = 0 then ∅ else (T↾(n - 1)).val

scoped[RootedLabeledTree] notation "𝕍{" T "," n "}" => @setOfLevel T n

lemma setOfLevel_def (T : 𝕋₀) :
  T.setOfLevel = Set.seqDiff T.setOfLevelAtMost := by
  ext n v; by_cases h : n = 0
  · simp [setOfLevel, Set.seqDiff, h]
  · simp only [Set.seqDiff, setOfLevel, h, setOfLevelAtMost,
      Set.accumulate_of_mono T.setOfLevelAtMost T.instMonotoneSetOfLevelAtMost]

variable {T : 𝕋₀}

@[simp] lemma setOfLevel_zero : 𝕍{T, 0} = {[]} := by
  simp [setOfLevel]

@[simp] lemma setOfLevel_same_length {n : ℕ} : ∀ ν ∈ 𝕍{T,n}, ‖ν‖ₕ = n := by
  intro v hv; simp [setOfLevel, truncation] at hv; by_cases h : n = 0
  · have := h ▸ hv.1.1; omega
  · have := (not_imp_not.2 <| hv.2 h) (not_not.2 hv.1.2); omega

@[simp] lemma finite_setOfLevel_of_finite (hT : Set.Finite T.val)
  (n : ℕ) : Set.Finite 𝕍{T,n} := by
  simp [setOfLevel]; by_cases h : n = 0
  · simp [h]
  · simp [h]; exact @Finite.Set.finite_diff _ _ _ (finite_truncation_of_finite hT n)

@[simp] lemma setOfLevel_subset_setOfLevel {n : ℕ} : 𝕍{T,n} ⊆ 𝕍{n} := by
  simp [TreeNode.setOfLevel, Set.subset_def]; exact RootedLabeledTree.setOfLevel_same_length

lemma truncation_succ (T : 𝕋₀) (n : ℕ) : (T↾(n + 1)).val = (T↾(n)).val ∪
  ⋃ v ∈ 𝕍{T,n}, ⋃ m ∈ { m : ℕ | m + 1 ≤ #{T, v}ₑ}, {m :: v} := by
  ext v; simp [truncation]; constructor
  · intro ⟨hv1, hv2⟩; by_cases hv3 : ‖v‖ₕ ≤ n
    · left; grind
    · right; use v.tail, (by
        simp [setOfLevel, truncation]; constructor
        · exact ⟨hv1, @tail_mem' T v hv2⟩
        · omega), v.head (by grind), (by
          simp [countChildren]
          refine @le_iSup₂ _ ℕ _ _ (fun m => fun _ : m :: v.tail ∈ T => (m : WithTop ℕ) + 1 )
            (v.head (by grind)) (by grind)); grind
  · intro h; rcases h with (⟨hv1, hv2⟩|⟨vt, hv3, vh, hv4, hv5⟩)
    · grind
    · have hv6 : ‖vt‖ₕ = n := setOfLevel_same_length vt hv3
      have hv7 : vh :: vt ∈ T := countChildren_ge_iff.2 hv4
      grind

-- ## generationSizeFromLevel

noncomputable def generationSizeFromLevel (T : 𝕋₀) :=
  tsumOfLevel (ENat.toENNReal ∘ T.countChildren)

scoped[RootedLabeledTree] notation "#{" T ", " n "}ₑ" => @generationSizeFromLevel T n

lemma generationSizeFromLevel_eq_tsum_sum (T : 𝕋₀) (n : ℕ) :
  #{T, n}ₑ = ∑' m, ∑ ν : 𝕍{n,m}, ↑(#{T, ↑ν}ₑ) := tsumOfLevel_eq_tsum_sum' _ n (by simp) (by simp)

-- instance _root_.ENat.instTopologicalSpace : TopologicalSpace ℕ∞ :=
--   TopologicalSpace.induced ENat.toENNReal inferInstance

-- noncomputable def generationSizeFromLevel (T : 𝕋₀) :=
--   tsumOfLevel T.countChildren

-- #check ENNReal.aemeasurable_of_tendsto'
-- #check ENNReal.aemeasurable_of_tendsto

-- private lemma partial_sums_tendsto_tsum {f : ℕ → ENNReal} :
--   Filter.Tendsto (fun m => ∑ i ∈ Finset.range m, f i) Filter.atTop (nhds (∑' i, f i)) := by
--   apply Summable.tendsto_sum_tsum_nat; simp

-- ## LocallyFinite

def IsLocallyFinite (T : 𝕋₀) := ∀ n, Set.Finite (T↾(n)).val

protected def LocallyFinite := {T : 𝕋₀ // T.IsLocallyFinite}

scoped[RootedLabeledTree.LocallyFinite] notation "𝕋" => RootedLabeledTree.LocallyFinite

open LocallyFinite

protected def Finite := {T : 𝕋 // Set.Finite T.val.val}

scoped[RootedLabeledTree.Finite] notation "𝕋ᵉ" => RootedLabeledTree.Finite

namespace Finite

lemma finite_eq : 𝕋ᵉ = {T : 𝕋 // ‖T.val‖ₕ < ∞} := by sorry

end Finite

open Finite

lemma isLocallyFinite_of_truncation (hT : T.IsLocallyFinite) (n : ℕ) :
  IsLocallyFinite (T↾(n)) := by simp [IsLocallyFinite] at ⊢ hT; intro m; exact hT (min n m)

def LocallyFinite.generateFinite (s : Set 𝕍) (hs : s ≠ ∅) (hs' : s.Finite) : 𝕋 :=
  ⟨generateTree s hs, by
    simp [IsLocallyFinite]; exact finite_truncation_of_finite <| finite_of_generate_finite hs hs'⟩

namespace LocallyFinite

noncomputable instance : MetricSpace 𝕋 := Subtype.metricSpace

instance : IsUltrametricDist 𝕋 where
  dist_triangle_max T1 T2 T3 := treeDist_ultra T1.val T2.val T3.val

instance : Coe 𝕋 (Set 𝕍) where
  coe T := T.val

instance : Membership 𝕍 𝕋 where
  mem T l := l ∈ T.val

lemma mem_iff {v : 𝕍} {T : 𝕋} : v ∈ T ↔ v ∈ T.val := ⟨by
  intro h; exact h, by simp [instMembershipTreeNode]⟩

instance : HasSubset 𝕋 where
  Subset T1 T2 := T1.val ⊆ T2.val

-- ## LocallyFinite.truncation

@[simp] def truncation (T : 𝕋) (n : ℕ) : 𝕋 :=
  ⟨T.val↾(n), isLocallyFinite_of_truncation T.property n⟩

scoped[RootedLabeledTree.LocallyFinite] notation T "↾(" n ")" => @truncation T n

private instance instUniformityBasis' : (uniformity 𝕋).HasBasis
  (fun _ => True) (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ℝ≥0∞))⁻¹}) :=
  EMetric.mk_uniformity_basis (by simp) (by
    simp; intro ε hε; obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε); use n
    simp [ENNReal.inv_lt_iff_inv_lt] at hn; simp [ENNReal.inv_le_iff_inv_le]
    exact le_of_lt <| lt_trans hn (by apply ENNReal.coe_lt_coe.2; simp))

def uniformityBasis := fun n => {p : 𝕋 × 𝕋 | (p.1)↾(n + 1) = (p.2)↾(n + 1)}

private lemma uniformityBasis_eq_aux : (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ℝ≥0∞))⁻¹})
  = uniformityBasis := by
  ext n p; simp [uniformityBasis, edist, PseudoMetricSpace.edist, treeDist]; constructor
  · intro h; have h := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 h
    simp [-ENNReal.toReal_inv, ←ENNReal.toReal_inv] at h
    have h := (ENNReal.add_lt_add_iff_left (by simp)).1 h
    rw [show (n : ℝ≥0∞) = ((n : ℕ∞) : ℝ≥0∞) from by simp] at h
    simp [-ENat.toENNReal_coe] at h; apply Subtype.coe_inj.1; simp
    exact heightCongr_apply _ <| (ENat.add_one_le_iff (by simp)).2 h
  · intro h; have h := Subtype.coe_inj.2 h; simp at h
    have := (heightCongr_apply_iff _).2 h
    set m := heightCongr p.1.val p.2.val with hm
    conv => left; congr; congr; congr; congr; right; congr; rw [←hm]
    apply (ENNReal.toReal_lt_toReal (by simp) (by simp)).1
    simp [-ENNReal.toReal_inv, ←ENNReal.toReal_inv]
    by_cases h' : m = ⊤
    · simp [h']
    · have := (ENat.lt_add_one_iff h').2 this
      have := ENat.toENNReal_lt.2 this; simp at this
      conv => lhs; rw [add_comm]
      conv => rhs; rw [add_comm]
      exact this

instance instUniformityBasis : (uniformity 𝕋).HasBasis
  (fun _ => True) uniformityBasis := uniformityBasis_eq_aux ▸ instUniformityBasis'

instance : CompleteSpace 𝕋 where
  complete := by
    intro f hf; have hf' := (by simpa [Cauchy] using hf)
    let E (n : ℕ) := {p : 𝕋 × 𝕋 | (p.1.val)↾(n) = (p.2.val)↾(n)}
    have memE (n : ℕ): E n ∈ uniformity 𝕋 := by
      by_cases h : n = 0
      · simp [h, E]
      · have : E n = uniformityBasis (n - 1) := by
          simp only [uniformityBasis, truncation, E]
          conv => right; congr; ext p; rw [(show n - 1 + 1 = n from by omega), ←Subtype.coe_inj]
        exact (Filter.HasBasis.mem_iff instUniformityBasis).2 (by
          use (n - 1); simp only [this, subset_refl, and_self])
    have (n : ℕ) : ∃ Sn ∈ f, Sn.Nonempty ∧ Sn ×ˢ Sn ⊆ E n := by
      simp only [LE.le] at hf'; have hf'2 := @hf'.2 (E n) (memE n)
      obtain ⟨Sn, hSmem, _⟩ := Filter.mem_prod_same_iff.1 hf'2; use Sn
      simp only [and_true, true_and, *]; by_contra h
      exact (not_imp_not.2 Filter.empty_mem_iff_bot.1 <| Filter.neBot_iff.1 hf'.1)
        <| (Set.not_nonempty_iff_eq_empty.1 h) ▸ hSmem
    choose S hSmem hSne hSsub using this
    have hSsub' (n : ℕ) (T1 T2) : T1 ∈ S n → T2 ∈ S n → T1↾(n) = T2↾(n) := by
      intro h1 h2; have : (T1, T2) ∈ (S n) ×ˢ (S n) := by
        simp only [Set.mem_prod, and_self, h1, h2]
      have := Set.mem_of_subset_of_mem (hSsub n) this; simp only [Set.mem_setOf_eq, E] at this
      apply Subtype.coe_inj.1; exact this
    choose T' hT'mem using hSne
    have hT'tr (n m : ℕ) : (T' (n + m))↾(n) = (T' n)↾(n) := by
      obtain ⟨U, hU⟩ : (S (n + m) ∩ S n).Nonempty := by
        by_contra h; exact (not_imp_not.2 Filter.empty_mem_iff_bot.1 <| Filter.neBot_iff.1 hf'.1)
          <| (Set.not_nonempty_iff_eq_empty.1 h) ▸ f.inter_mem (hSmem (n + m)) (hSmem n)
      have h1 := hSsub' (n + m) U (T' (n + m)) ((Set.mem_inter_iff _ _ _).1 hU).1 (hT'mem (n + m))
      have h2 := hSsub' n U (T' n) ((Set.mem_inter_iff _ _ _).1 hU).2 (hT'mem n)
      have h1 := congrArg (fun T : 𝕋 => T↾(n)) h1; simp at h1 h2; have := h1 ▸ h2; exact this
    let Tval : Set 𝕍 := {l | l ∈ ((T' ‖l‖ₕ)↾(‖l‖ₕ))}
    set _T : 𝕋₀ := ⟨Tval, by
      ext l; constructor
      · intro hv; induction hv with
        | mem v' hv' => assumption
        | tail m v' hv' ih =>
          have := hT'tr ‖v'‖ₕ 1; simp only [truncation] at this
          rw [←Subtype.coe_inj, ←Subtype.coe_inj] at this; simp only [ne_eq] at this
          simp [mem_iff, RootedLabeledTree.mem_iff, Tval, ←this]
          exact mem_truncation_of_mem_other_truncation (by omega) <| tail_mem ih
        | less m v' hv' n hnm ih =>
          exact @less_mem ((T' (‖v'‖ₕ + 1))↾(‖v'‖ₕ + 1)).val m n v' ih hnm
      · exact generateSet.mem l
      , Set.nonempty_iff_ne_empty.1 ⟨[], by simp [mem_iff, RootedLabeledTree.mem_iff, Tval]⟩⟩
    have hTtr (n : ℕ) : _T↾(n) = (T' n).val↾(n) := by
      simp only [RootedLabeledTree.truncation, ne_eq, truncation, _T, Tval]
      apply Subtype.coe_inj.1; ext l; simp; intro hv
      simp [mem_iff, RootedLabeledTree.mem_iff]
      have := (show ‖l‖ₕ + (n - ‖l‖ₕ) = n from by omega) ▸ hT'tr ‖l‖ₕ (n - ‖l‖ₕ)
      simp only [truncation] at this; rw [←Subtype.coe_inj] at this; simp only at this
      constructor
      · intro hv'; exact @mem_of_mem_truncation _ ‖l‖ₕ _
          (this ▸ mem_truncation_of_mem (by omega) hv')
      · intro hv'; exact @mem_of_mem_truncation _ ‖l‖ₕ _
          (Eq.symm this ▸ mem_truncation_of_mem (by omega) hv')
    set T : 𝕋 := ⟨_T, by
      simp only [IsLocallyFinite, ne_eq]; intro n; rw [hTtr n]
      have := ((T' n)↾(n)).property; simp [IsLocallyFinite] at this
      have := (show min n n = n from by omega) ▸ this n; exact this⟩
    use T; have := @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T
    simp only [uniformityBasis, Set.mem_setOf_eq] at this
    refine (this.ge_iff.mpr ?_); simp only [forall_const]
    have hTtr (n : ℕ) : T↾(n) = (T' n)↾(n) := by
      simp only [T, truncation]; apply Subtype.coe_inj.1; simp only; exact hTtr n
    intro n; exact f.sets_of_superset (hSmem (n + 1)) (by
      simp only [Set.subset_def]; intro U hU; rw [hTtr (n + 1)]
      exact hSsub' (n + 1) U (T' (n + 1)) hU (hT'mem (n + 1)))

instance instNhdsBasis (T : 𝕋) : (nhds T).HasBasis (fun _ => True)
  fun n => {T' | T'↾(n + 1) = T↾(n + 1)} :=
  @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T

noncomputable instance instFintypeTruncate (T : 𝕋) (n : ℕ) :
  Fintype (T.val↾(n)).val := by
  exact @Fintype.ofFinite _ <| Set.finite_coe_iff.2 <| T.property n

instance : TopologicalSpace.SeparableSpace 𝕋 where
  exists_countable_dense := by
    let F := { s : Finset 𝕍 // s.Nonempty }
    let embed : F → 𝕋 := fun s => generateFinite s
      (by simp [Finset.nonempty_iff_ne_empty.1 s.property]) (by simp only [Finset.finite_toSet])
    -- `Countable` is inferred in `use` from `Set.countable_range` and `Countable F`, which in turn
    -- is inferred from `Subtype.countable`, `Finset.countable`, and `Countable TreeNode`
    use Set.range embed; constructor
    · exact Set.countable_range embed
    · simp [Dense]; intro T; simp [mem_closure_iff_nhds_basis (instNhdsBasis T)]; intro n
      -- In `Set.toFinset`, `Fintype ↑(T.val↾(n)).val` is required for element in `F`
      -- this means `LocallyFinite` is required here, because otherwise it is not `Fintype`
      use ⟨Set.toFinset (T.val↾(n + 1)).val, by
        use []; -- In `Set.mem_toFinset`, `Fintype (T.val↾(n)).val` is required likewise
        simp only [ne_eq, Set.mem_toFinset]; exact RootedLabeledTree.mem_iff.1 nil_mem⟩
      simp only [generateFinite, ne_eq, Set.coe_toFinset, generateTree_val,
        truncation_truncation, min_self, embed]

instance : MeasurableSpace 𝕋 := borel 𝕋

instance : Coe 𝕋 𝕋₀ where
  coe T := T.val

variable (T : 𝕋) (ν : 𝕍) (n : ℕ)

@[simp] lemma countChildren_ne_top : #{T, ν}ₑ ≠ ⊤ := by
  simp [←countChildren_eq_top_iff]
  set S := T.val↾(‖ν‖ₕ + 1) with hS
  have hT := (@Nat.card_eq_fintype_card _
    <| hS ▸ (@Fintype.ofFinite _ <| T.property (‖ν‖ₕ + 1)))
    ▸ hS ▸ (@Finite.equivFin _ <| T.property (‖ν‖ₕ + 1))
  set n := @Fintype.card _ <| hS ▸ (@Fintype.ofFinite _ <| T.property (‖ν‖ₕ + 1)) with hn
  use n; by_contra h; have h := hS ▸ @mem_truncation_of_mem _ (‖ν‖ₕ + 1) _ (by simp) h
  let F (m : Fin (n + 1)) : S.val.Elem := ⟨m :: ν, @less_mem S n _ ν h (by omega)⟩
  have := Fintype.card_le_of_injective F (by simp [Function.Injective, F]; omega); simp [hn] at this

@[simp] lemma countChildren_lt_top : countChildren ↑T ν < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top]; exact countChildren_ne_top T ν

noncomputable def countChildren : ℕ := (T.val.countChildren ν).lift (by simp)

scoped[RootedLabeledTree.LocallyFinite] notation "#{" T ", " v "}" => @countChildren T v

lemma countChildren_eq_toNat : #{T, ν} = #{T, ν}ₑ.toNat := ENat.lift_eq_toNat_of_lt_top (by simp)

lemma countChildren_toENat : (#{T, ν} : ℕ∞) = #{T, ν}ₑ := by
  simp [countChildren]

@[ext] def ext_of_countChildren (T1 T2 : 𝕋) (h : ∀ l, #{T1, l} = #{T2, l}) : T1 = T2 :=
  Subtype.coe_inj.1 <| RootedLabeledTree.ext_of_countChildren _ _ (by
    intro l; specialize h l; simp [countChildren] at h
    exact @ENat.coe_lift #{T1, l}ₑ (by simp)
      ▸ h ▸ @ENat.coe_lift #{T2, l}ₑ (by simp))

@[simp] lemma countChildren_eq_zero_of_not_mem (hv : ν ∉ T) : #{T, ν} = 0 := by
  simp [countChildren, RootedLabeledTree.countChildren, ENat.lift, WithTop.untop_eq_iff]
  have {m : ℕ∞} (hm : m ≤ 0) : m = 0 := by simp only [nonpos_iff_eq_zero] at hm; exact hm
  apply this; apply (@iSup₂_le_iff (WithTop ℕ) ℕ (fun m => m :: ν ∈ T) _).2; intro m hm
  simp; exact hv <| @tail_mem _ _ _ hm

noncomputable instance : FunLike 𝕋 𝕍 ℕ where
  coe T := T.countChildren
  coe_injective' T1 T2 h := by
    ext l; simp at h; have := congrArg (fun f => f l) h; simpa using this

@[simp] lemma setOfLevel_finite : Set.Finite 𝕍{T, n} := by
  simp [setOfLevel]; by_cases n = 0
  · simp [*]
  · simp [*]; apply Set.Finite.diff; exact T.property n

noncomputable instance : Fintype ↑𝕍{T, n} :=
  @Fintype.ofFinite _ <| Set.finite_coe_iff.2 <| setOfLevel_finite T n

section

noncomputable def _root_.NNReal.toNat := FloorSemiring.floor (α := NNReal)

noncomputable def _root_.ENNReal.toNat := fun x : ℝ≥0∞ => x.toNNReal.toNat

noncomputable def _root_.ENNReal.toENat := fun x : ℝ≥0∞ => match x with
  | ⊤ => (⊤ : ℕ∞)
  | some x => x.toNat

-- instance _root_.ENat.instTopologicalSpace : TopologicalSpace ℕ∞ :=
--   TopologicalSpace.induced ENat.toENNReal inferInstance

-- #check EMetricSpace

-- theorem _root_.ENat.isEmbedding_coe : Topology.IsEmbedding ((↑) : ℕ → ENat) := by sorry
  -- ENat.coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe']; exact ordConnected_Iio

-- @[fun_prop]
-- theorem _root_.ENat.continuous_coe : Continuous ((↑) : ℕ → ENat) :=
--   ENat.isEmbedding_coe.continuous

-- @[measurability]
-- theorem _root_.ENat.measurable_coe_nat_enat : Measurable ((↑) : ℕ → ENat) :=
--   ENat.continuous_coe.measurable

@[simp] lemma _root_.NNReal.ofNat_toNat (n : ℕ) : (n : ℝ≥0).toNat = n := by
  simp [NNReal.toNat, FloorSemiring.floor]

@[simp] lemma _root_.ENNReal.ofNat_toNat (n : ℕ) : (n : ℝ≥0∞).toNat = n := by
  simp [ENNReal.toNat]

@[simp] lemma _root_.ENNReal.ofNat_toENat (n : ℕ) : (n : ℝ≥0∞).toENat = n := by
  simp [ENNReal.toENat]

@[simp] lemma _root_.ENNReal.ofENat_toENat (n : ℕ∞) : (n : ℝ≥0∞).toENat = n := by
  cases n <;> simp [ENNReal.toENat]

@[measurability]
lemma _root_.NNReal.measurable_toNat : Measurable NNReal.toNat := by
  apply measurable_of_isOpen; simp only [isOpen_discrete, forall_const]; intro s
  rw [←Set.iUnion_of_singleton_coe s, Set.preimage_iUnion]
  apply MeasurableSet.iUnion; intro n
  simp only [NNReal.toNat, FloorSemiring.floor, Set.preimage, Set.mem_singleton_iff]
  conv => congr; congr; ext r; rw [Nat.floor_eq_iff r.property]
  exact measurableSet_Ico (a := ((n : ℕ) : NNReal)) (b := ((n : ℕ) : NNReal) + 1)

-- lemma _root_.ENNReal.measurable_toENat : Measurable ENNReal.toENat := by
--   apply measurable_of_measurable_on_compl_singleton ⊤
--   apply MeasurableEquiv.ennrealEquivNNReal.symm.measurable_comp_iff.1
--   have : Measurable fun p : NNReal => (p : ℝ≥0∞).toENat := by
--     conv => congr; ext p; simp only [ENNReal.toENat]

--     apply NNReal.measurable_toNat.comp
--     sorry
--   exact this

variable {α : Type*} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α}

lemma _root_.Measurable.nnreal_toNat {f : α → NNReal} (hf : Measurable f) :
  Measurable fun x => (f x).toNat := NNReal.measurable_toNat.comp hf

lemma _root_.AEMeasurable.nnreal_toNat {f : α → NNReal} (hf : AEMeasurable f μ) :
  AEMeasurable (fun x => (f x).toNat) μ := NNReal.measurable_toNat.comp_aemeasurable hf

lemma _root_.Measurable.ennreal_toNat {f : α → ENNReal} (hf : Measurable f) :
  Measurable fun x => (f x).toNat := NNReal.measurable_toNat.comp <| Measurable.ennreal_toNNReal hf

lemma _root_.AEMeasurable.ennreal_toNat {f : α → ENNReal} (hf : AEMeasurable f μ) :
  AEMeasurable (fun x => (f x).toNat) μ :=
  NNReal.measurable_toNat.comp_aemeasurable <| AEMeasurable.ennreal_toNNReal hf

-- lemma _root_.Measurable.ennreal_toENat {f : α → ENNReal} (hf : Measurable f) :
--   Measurable fun x => (f x).toENat := ENNReal.measurable_toENat.comp hf

-- lemma _root_.AEMeasurable.ennreal_toENat {f : α → ENNReal} (hf : AEMeasurable f μ) :
--   AEMeasurable (fun x => (f x).toENat) μ := ENNReal.measurable_toENat.comp_aemeasurable hf

-- lemma _root_.Measurable.ennreal_ofENat_toENat {f : α → ENat}
--   (hf : Measurable fun x => (f x : ℝ≥0∞)) : Measurable f := by
--   rw [show f = fun x => (f x : ℝ≥0∞).toENat from by simp]; exact Measurable.ennreal_toENat hf

-- lemma _root_.AEMeasurable.ennreal_ofENat_toENat {f : α → ENat}
--   (hf : AEMeasurable (fun x => (f x : ℝ≥0∞)) μ) : AEMeasurable f μ := by
--   rw [show f = fun x => (f x : ℝ≥0∞).toENat from by simp]; exact AEMeasurable.ennreal_toENat hf

lemma _root_.Measurable.ennreal_ofNat_toNat {f : α → ℕ}
  (hf : Measurable fun x => (f x : ℝ≥0∞)) : Measurable f := by
  rw [show f = fun x => (f x : ℝ≥0∞).toNat from by simp]; exact Measurable.ennreal_toNat hf

lemma _root_.AEMeasurable.ennreal_ofNat_toNat {f : α → ℕ}
  (hf : AEMeasurable (fun x => (f x : ℝ≥0∞)) μ) : AEMeasurable f μ := by
  rw [show f = fun x => (f x : ℝ≥0∞).toNat from by simp]; exact AEMeasurable.ennreal_toNat hf

@[measurability]
theorem ENNReal.measurable_nat_cast : Measurable ((↑) : ℕ → ENNReal) := by
  apply measurable_of_Ici; simp

lemma _root_.Measurable.nat_ofNat_toENNReal {f : α → ℕ}
  (hf : Measurable f) : Measurable (fun x => (f x : ℝ≥0∞)) := by
  exact Measurable.comp (by measurability) hf

lemma _root_.AEMeasurable.nat_ofNat_toENNReal {f : α → ℕ}
  (hf : AEMeasurable f μ) : AEMeasurable (fun x => (f x : ℝ≥0∞)) μ := by
  exact Measurable.comp_aemeasurable (by measurability) hf

end

-- ## generationSizeFromLevel
section
variable {T : 𝕋} (n : ℕ)

noncomputable def generationSizeFromLevel := tsumOfLevel T.countChildren

scoped[RootedLabeledTree.LocallyFinite] notation "#{" T ", " n "}" => @generationSizeFromLevel T n

private lemma generationSizeFromLevel_def_aux_1 :
  #{T, n} = ∑ v ∈ Finset.subtype (fun ν : 𝕍 ↦ ‖ν‖ₕ = n) 𝕍{T, n}.toFinset, #{T, ↑v} := by
  simp only [generationSizeFromLevel, tsumOfLevel]
  have heq := @tsum_eq_sum ℕ 𝕍{n} Nat.instAddCommMonoid instTopologicalSpaceNat
    (fun v => #{T, ↑v}) (SummationFilter.unconditional ↑𝕍{n}) _
    (by simp [TreeNode.setOfLevel]; apply Finset.subtype; exact 𝕍{T, n}.toFinset) (by
    simp; intro v hv hv'; exact countChildren_eq_zero_of_not_mem T v (by
    by_contra h; have : v ∈ 𝕍{T, n} := by
      simp [RootedLabeledTree.setOfLevel, RootedLabeledTree.truncation]
      simp [TreeNode.setOfLevel] at hv; by_cases n = 0
      · simp [*]; exact h
      · simp [*, (show n > n - 1 from by omega)]; exact h
    contradiction))
  simp [id_eq] at heq; exact heq

private lemma generationSizeFromLevel_def_aux_2 :
  #{T, n}ₑ = ∑ v ∈ Finset.subtype (fun ν : 𝕍 ↦ ‖ν‖ₕ = n)
  𝕍{T, n}.toFinset, #{T, ↑v}ₑ := by
  simp only [RootedLabeledTree.generationSizeFromLevel, tsumOfLevel, Function.comp_apply]
  have heq := @tsum_eq_sum ℝ≥0∞ 𝕍{n} _ _ (fun v => #{T, ↑v}) (SummationFilter.unconditional ↑𝕍{n})
    _ (by simp [TreeNode.setOfLevel]; apply Finset.subtype; exact 𝕍{T, n}.toFinset) (by
    simp; intro v hv hv'; exact countChildren_eq_zero_of_not_mem T v (by
    by_contra h; have : v ∈ 𝕍{T, n} := by
      simp [RootedLabeledTree.setOfLevel, RootedLabeledTree.truncation]
      simp [TreeNode.setOfLevel] at hv; by_cases n = 0
      · simp [*]; exact h
      · simp [*, (show n > n - 1 from by omega)]; exact h
    contradiction))
  simp [id_eq] at heq
  have (n : ℕ∞) (hn : n < ⊤) : n.lift hn = (n : ℝ≥0∞) := by
    have (n : ℕ) : (n : ℕ∞) = (n : ℝ≥0∞) := (by simp); rw [←this]; simp
  conv at heq => left; simp [countChildren, this]
  exact Eq.trans heq (by
  simp only [countChildren]; conv => left; arg 2; ext; rw[this]
  apply Eq.symm; exact @map_sum {v : 𝕍 // ‖v‖ₕ = n} ℕ∞ ℝ≥0∞ _ _ _ _ _
    ENat.toENNRealRingHom (fun v => #{T, ↑v}ₑ)
    (Finset.subtype (fun ν : 𝕍 ↦ ‖ν‖ₕ = n) 𝕍{T, n}.toFinset))

lemma generationSizeFromLevel_def_toRootedLabeledTree : (#{T, n} : ℝ≥0∞) = #{T, n}ₑ := by
  simp only [generationSizeFromLevel_def_aux_1, generationSizeFromLevel_def_aux_2, countChildren];
  rw [←ENat.toENNReal_coe]; apply ENat.toENNReal_inj.2; simp only [Nat.cast_sum, ENat.coe_lift,
    Finset.sum_subtype_eq_sum_filter]

lemma generationSizeFromLevel_def_toSum : #{T, n} = ∑ v ∈ 𝕍{T, n}.toFinset, #{T, v} := by
  apply Eq.trans <| T.generationSizeFromLevel_def_aux_1 n; simp; congr; simp
  exact @setOfLevel_same_length T.val n
end

-- ## generateFromCountChildren
section
variable (X : 𝕍 → ℕ)

def _root_.RootedLabeledTree.setFromCountChildren : Set 𝕍 :=
  {v | ∀ n, v.get n < X (v.drop (n + 1))}

@[simp] lemma _root_.RootedLabeledTree.generateSetFromCountChildren_id :
  generateSet (setFromCountChildren X) = setFromCountChildren X := by
  ext v; constructor
  · simp only [setFromCountChildren]
    intro hv
    rw [generateSet_eq_generate_tail_then_less {v | ∀ n, v.get n < X (v.drop (n + 1))}
      (by apply Ne.symm; apply Set.nonempty_iff_empty_ne.1; refine ⟨[], ?_⟩; simp)] at hv
    simp; by_cases hv' : v = []
    · grind
    · simp [hv'] at hv
      have := v.cons_head_tail hv'
      obtain ⟨m, hm, hm'⟩ := cons_mem_of_mem_generate_less _ (by simp) _ _ (this ▸ hv)
      simp [generate_tail] at hm'
      obtain ⟨u', hu'1, hu'2⟩ := hm'
      simp [generate_tail_of_single] at hu'2
      obtain ⟨m', hu'2⟩ := hu'2
      intro n
      specialize hu'1 ⟨n.val + m'.val, by
        have hu'3 := congrArg List.length hu'2; simp at hu'3; grind⟩
      simp at hu'1
      have := (show m'.val + (n.val + 1) = n.val + m'.val + 1 from by omega)
        ▸ @List.drop_drop _ (n.val + 1) ↑m' u'
      rw [←this] at hu'1
      conv at hu'1 => right; congr; arg 2; rw [hu'2]
      have h₀ (k : ℕ) : (m :: v.tail).drop (k + 1) = v.drop (k + 1) := by simp
      conv at hu'1 => right; congr; rw [h₀ ↑n]
      by_cases hn : n = ⟨0, by grind⟩
      · rw [hn] at hu'1; simp at hu'1
        have : u'[m'.val]'(by grind) = m := by
          have := @List.getElem_drop _ u' ↑m' 0 (by grind)
          simp [hu'2] at this; exact Eq.symm this
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

def _root_.RootedLabeledTree.generateFromCountChildren : 𝕋₀ :=
  generateTree (setFromCountChildren X) (by
    rw [←Set.nonempty_iff_ne_empty]; exact ⟨[], by simp [setFromCountChildren]⟩)

lemma _root_.RootedLabeledTree.generateFromCountChildren_false_ge (u : 𝕍) (n : ℕ)
  (h : X u ≤ n) (h' : n :: u ∈ generateFromCountChildren X) : False := by
  simp [RootedLabeledTree.mem_iff, generateFromCountChildren, generateTree] at h'
  simp [setFromCountChildren] at h'; specialize h' 0; simp at h'; grind

lemma _root_.RootedLabeledTree.generateFromCountChildren_less_mem (u : 𝕍) (n : ℕ)
  (h : n < X u) (hu : u ∈ setFromCountChildren X) : n :: u ∈ generateFromCountChildren X := by
  simp [generateFromCountChildren, generateTree, RootedLabeledTree.mem_iff];
  simp [setFromCountChildren] at hu ⊢; intro ⟨m, hm⟩; by_cases h' : m = 0
  · simp [h', h]
  · specialize hu ⟨m - 1, by grind⟩; grind

instance _root_.RootedLabeledTree.instDecidableMemSetFromCountChildren (u : 𝕍) :
  Decidable (u ∈ setFromCountChildren X) := by simp [setFromCountChildren]; infer_instance

lemma _root_.RootedLabeledTree.generateFromCountChildren_countChildren_eq (u : 𝕍) :
  #{generateFromCountChildren X, u}ₑ = if u ∈ setFromCountChildren X then X u else 0 := by
  set T := generateFromCountChildren X with hT
  by_cases h : #{T, u}ₑ = ⊤
  · exact False.elim <| generateFromCountChildren_false_ge X u (X u) (by omega)
      <| countChildren_eq_top_iff.2 h <| X u
  · have : #{T, u}ₑ =
      ((#{T, u}ₑ).lift (WithTop.lt_top_iff_ne_top.2 h) : ℕ∞) := by simp
    rw [this]; apply ENat.coe_inj.2; apply Nat.eq_iff_le_and_ge.2
    simp [RootedLabeledTree.countChildren]; constructor
    · apply @iSup₂_le (WithTop ℕ) ℕ (fun m => m :: u ∈ T) _ _
        (fun m => fun _ => ↑m + 1) ?_; intro m' hm'; simp
      by_cases h'' : u ∈ setFromCountChildren X
      · by_contra h'; exact generateFromCountChildren_false_ge X u m' (by
        simp [h''] at h'; rw[(show (m' : WithTop ℕ) + 1 = ↑(m' + 1) from by simp)] at h'
        have h' := WithTop.coe_lt_coe.1 h'; simp at h'; omega) hm'
      · simp [h''];
        have := @tail_mem _ _ _ hm'
        simp [T, generateFromCountChildren, generateTree, RootedLabeledTree.mem_iff] at this
        contradiction
    · by_cases h' : X u = 0 ∨ u ∉ setFromCountChildren X
      · have : (if u ∈ setFromCountChildren X then (X u : ℕ∞) else 0) = 0 := by
          simp; intro h; grind
        simp [this]
      · simp at h'
        have : (if u ∈ setFromCountChildren X then (X u : ℕ∞) else 0) = X u := by simp [h'.2]
        rw [this]
        conv => left; congr; rw [(show X u = X u - 1 + 1 from by omega)]
        conv => left; simp only [Nat.cast_add, Nat.cast_one]
        apply countChildren_ge
        exact generateFromCountChildren_less_mem X u (X u - 1) (by omega) h'.2

lemma _root_.RootedLabeledTree.generateFromCountChildren_countChildren_le (u : 𝕍) :
  #{generateFromCountChildren X, u}ₑ ≤ X u := by
  rw [generateFromCountChildren_countChildren_eq X u]; apply WithTop.coe_le_coe.2
  split_ifs <;> simp

def generateFromCountChildren : 𝕋 :=
  let T := RootedLabeledTree.generateFromCountChildren X; ⟨T, by
    simp only [IsLocallyFinite]; intro n; induction n with
    | zero => simp
    | succ n ih =>
      simp only [truncation_succ]; refine Set.finite_union.2 ⟨ih, ?_⟩
      rw [←@Set.iUnion_subtype 𝕍 𝕍 (fun v => v ∈ 𝕍{T, n})
        (fun v => ⋃ m ∈ {m : ℕ | m + 1 ≤ #{T, v}ₑ}, {m :: v})]
      refine @Set.finite_iUnion _ _ ?_ _ ?_
      · apply Set.finite_coe_iff.2; simp [setOfLevel]; apply Set.finite_coe_iff.1
        refine @Finite.Set.finite_diff _ _ _ ?_; apply Set.finite_coe_iff.2; exact ih
      · intro u; rw [←@Set.iUnion_subtype ℕ 𝕍
          (fun m => m ∈ {m : ℕ | m + 1 ≤ #{T, u}ₑ}) (fun m => {m.val :: u.val})]
        refine @Set.finite_iUnion _ _ ?_ _ ?_
        · apply Set.finite_coe_iff.2
          have : {m : ℕ | ↑m + 1 ≤ #{T, ↑u}ₑ} ⊆ {m : ℕ | ↑m + 1 ≤ ↑(X u)} := by
            have := generateFromCountChildren_countChildren_le X u
            simp [T]
            intro n h; have := le_trans h this; apply WithTop.coe_le_coe.1; simp; exact this
          refine Set.Finite.subset ?_ this; conv => congr; congr; ext m; rw[Nat.add_one_le_iff];
          simp [Set.finite_lt_nat]
        · intro; simp⟩

lemma generateFromCountChildren_countChildren_eq (u : 𝕍) :
  #{generateFromCountChildren X, u} = if u ∈ setFromCountChildren X then X u else 0 := by
  simp [countChildren]; apply ENat.coe_inj.1; simp [generateFromCountChildren,
    RootedLabeledTree.generateFromCountChildren_countChildren_eq]

lemma generateFromCountChildren_countChildren_le (u : 𝕍) :
  #{generateFromCountChildren X, u} ≤ X u := by
  simp [countChildren, generateFromCountChildren]
  exact RootedLabeledTree.generateFromCountChildren_countChildren_le _ _

lemma generateFromCountChildren_false_ge (u : 𝕍) (n : ℕ)
  (h : X u ≤ n) (h' : n :: u ∈ generateFromCountChildren X) : False := by
  simp [generateFromCountChildren, mem_iff] at h';
  exact RootedLabeledTree.generateFromCountChildren_false_ge _ _ _ h h'

lemma generateFromCountChildren_less_mem (u : 𝕍) (n : ℕ)
  (h : n < X u) (hu : u ∈ setFromCountChildren X) : n :: u ∈ generateFromCountChildren X := by
  simp [generateFromCountChildren, mem_iff]
  exact RootedLabeledTree.generateFromCountChildren_less_mem _ _ _ h hu

end

-- ## Measurable countChildren
section
variable {T : 𝕋} (v : 𝕍) (n : ℕ)

@[measurability]
theorem countChildren_measurable : Measurable (fun T => #{T, v}) := by sorry

@[measurability]
theorem generationSizeFromLevel_measurable : Measurable (fun T => #{T, n}) := by sorry

end
end LocallyFinite

-- section RootedForest

-- instance : Coe (WithBot 𝕍) 𝕍 where
--   coe v := match v with
--     | ⊥ => []
--     | some v => v

-- axiom bot_eq_some_nil : (⊥ : WithBot 𝕍) = some ([] : 𝕍)

-- lemma exists_some (v : WithBot 𝕍) : ∃ l, v = some l := by
--   match v with
--   | ⊥ => use []; rw [bot_eq_some_nil]
--   | some l => use l

-- def toRootedForest (T : 𝕋₀) : RootedForest 𝕍
--   (fun v => { i : ℕ // match T v with | ⊤ => True | some k => i < k }) where
--   branch v i := (i : ℕ) :: v
--   parent_child u v := ↑v ∈ T ∧ ∃ m : ℕ, v = m :: u
--   parent_child_def u v := by
--     obtain ⟨u, hu⟩ := exists_some u; obtain ⟨v, hv⟩ := exists_some v; simp [*]; constructor
--     · intro h; obtain ⟨hvT, m, hmuv⟩ := h; use m; match h : T u with
--       | ⊤ => simp [*]
--       | some k =>
--         have := h ▸ (show #{T, u}ₑ = T u from by simp [instFunLikeTreeNodeENat])
--           ▸ countChildren_ge_iff.1 <| (WithBot.coe_inj.1 hmuv) ▸ hvT
--         conv at this => left; rw [(show (m : WithTop ℕ) + 1 = ↑(m + 1) from by simp)]
--         have := ENat.coe_le_coe.1 this; simp [*]; omega
--     · intro h; obtain ⟨m, hmT, h'⟩ := h; match h : T u with
--       | ⊤ => use WithBot.coe_inj.1 h' ▸ countChildren_eq_top_iff.2 h m, m; simp [*]
--       | some k =>
--         simp [*] at hmT; have := ENat.coe_le_coe.2 (show m + 1 ≤ k from by omega)
--         conv at this => left; simp
--         conv at this => right; rw [←ENat.some_eq_coe, ←WithTop.some_eq_coe k, ←h,
--           ←(show #{T, u}ₑ = T u from by simp [instFunLikeTreeNodeENat])]
--         use (WithBot.coe_inj.1 h') ▸ countChildren_ge_iff.2 this, m; simp [*]
--   root_no_parent := by simp
--   acyclic := by
--     simp; intro u v w; cases u <;> cases v <;> simp_all [bot_eq_some_nil]
--     · sorry
--     · sorry
--   loopless := by simp; intro u m; cases u <;> simp
--   wellfounded := sorry
--   IsOrigin v := match v with
--     | ⊥ => False
--     | some v => ‖v‖ₕ = 1
--   isOrigin_def := by simp; sorry
--   root_bij := sorry
--   node_bij := sorry

-- end RootedForest

end RootedLabeledTree
