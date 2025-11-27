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
## generationSizeAtLevel
## LocallyFinite
## LocallyFinite.truncation
## LocallyFinite.MetricSpace
## LocallyFinite.CompleteSpace
##
-/

-- ## generateSet
namespace RootedLabeledTree

inductive generateSet (s : Set TreeNode) : Set TreeNode
  | mem : (l : TreeNode) → s l → generateSet s l
  | tail : (m : ℕ) → (l : TreeNode) → generateSet s (m :: l) → generateSet s l
  | less : (m : ℕ) → (l : _) → generateSet s (m :: l) → (n : ℕ) → n ≤ m → generateSet s (n :: l)

def _root_.RootedLabeledTree := {s // generateSet s = s ∧ s ≠ ∅}

instance : Coe RootedLabeledTree (Set TreeNode) where
  coe T := T.val

instance instMembershipTreeNode : Membership TreeNode RootedLabeledTree where
  mem T l := l ∈ T.val

instance : HasSubset RootedLabeledTree where
  Subset T1 T2 := T1.val ⊆ T2.val

@[simp] lemma nil_generate : generateSet ∅ = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false]; by_contra hl; induction hl <;> assumption

@[simp] lemma generateSet_eq_self_of_val (T : RootedLabeledTree) :
  generateSet T.val = T.val := T.property.1

@[simp] lemma nonempty_of_val (T : RootedLabeledTree) : T.val ≠ ∅ := T.property.2

lemma generateSet_mono : Monotone generateSet := by
  intro s1 s2 h; simp only [Set.le_eq_subset, Set.subset_def]; intro l hl
  induction hl with
  | mem l' hl' =>
    have := Set.mem_of_subset_of_mem h hl'
    simp [Membership.mem, Set.Mem] at this ⊢
    exact generateSet.mem l' this
  | tail m l' hl' ih =>
    simp [Membership.mem, Set.Mem]
    exact generateSet.tail m l' ih
  | less m l' hl' n hnm ih =>
    simp [Membership.mem, Set.Mem]
    exact generateSet.less m l' ih n hnm

lemma generateSet_subset (s : Set TreeNode) : s ⊆ generateSet s := by
  unfold Subset Set.instHasSubset LE.le Set.instLE Set.Subset; simp; intro l hl
  simp [Membership.mem, Set.Mem] at hl ⊢
  exact generateSet.mem l hl

lemma generateSet_proj (s : Set TreeNode) :
  generateSet (generateSet s) = generateSet s := by
  ext l; constructor
  · intro hl; induction hl with
      | mem => simp [Membership.mem, Set.Mem, *]
      | tail m l' hl' ih => exact generateSet.tail m l' ih
      | less m l' hl' n hnm ih => exact generateSet.less m l' ih n hnm
  · intro hl; exact generateSet.mem l hl

lemma generateSet_idempotent : @IsIdempotentElem _ ⟨Function.comp⟩ generateSet := by
  simp [IsIdempotentElem]; ext s l; constructor
  · intro hl; induction hl with
      | mem => simp [Membership.mem, Set.Mem, *]
      | tail m l' hl' ih => exact generateSet.tail m l' ih
      | less m l' hl' n hnm ih => exact generateSet.less m l' ih n hnm
  · intro hl; exact generateSet.mem l hl

lemma nonempty_of_nonempty (s : Set TreeNode) (hs : s ≠ ∅) : generateSet s ≠ ∅ := by
  obtain ⟨l, hl⟩ := not_not.1 <| not_imp_not.2 Set.not_nonempty_iff_eq_empty.1 hs
  apply not_imp_not.2 (@Set.not_nonempty_iff_eq_empty _ (generateSet s)).2
  simp only [not_not]; simp [Membership.mem, Set.Mem] at hl
  exact ⟨l, generateSet.mem l hl⟩

@[simp] lemma nil_mem {T : RootedLabeledTree} : [] ∈ T := by
  obtain ⟨h1, h2⟩ := T.property; obtain ⟨l, hl⟩ := Set.nonempty_iff_ne_empty.2 h2
  induction l with
  | nil => exact hl
  | cons m l' ih =>
    rw [←h1] at hl ih; simp [Membership.mem, Set.Mem] at hl ih ⊢
    have := h1 ▸ generateSet.tail m l' (h1 ▸ hl); exact ih this

@[simp] lemma tail_mem {T : RootedLabeledTree} {m : ℕ} {l : TreeNode} {h : m :: l ∈ T} : l ∈ T := by
  obtain ⟨h1, h2⟩ := T.property; simp [Membership.mem, Set.Mem] at ⊢ h; rw [←h1] at ⊢ h
  exact generateSet.tail m l h

@[simp] lemma tail_mem' {T : RootedLabeledTree} {l : TreeNode} {h : l ∈ T} : l.tail ∈ T := by
  cases l with
  | nil => simp
  | cons m l' => simp [@tail_mem T m l' h]

@[simp] lemma drop_mem {T : RootedLabeledTree} {l : TreeNode} {h : l ∈ T} {n : ℕ} :
  l.drop n ∈ T := by
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [←@List.drop_drop _ 1 n l, List.drop_one]; exact @tail_mem' T (l.drop n) ih

@[simp] lemma less_mem {T : RootedLabeledTree} {m n : ℕ} {l : TreeNode}
  {h : m :: l ∈ T} {hnm : n ≤ m} : n :: l ∈ T := by
  obtain ⟨h1, h2⟩ := T.property; simp [Membership.mem, Set.Mem] at ⊢ h; rw [←h1] at ⊢ h
  exact generateSet.less m l h n hnm

-- ## generateTree

def generateTree (s : Set TreeNode) (hs : s ≠ ∅) : RootedLabeledTree :=
  ⟨generateSet s, generateSet_proj s, nonempty_of_nonempty s hs⟩

@[simp] lemma generateTree_val (T : RootedLabeledTree) :
  generateTree T.val T.nonempty_of_val = T := by simp [generateTree]

def rootTree := generateTree {[]} (by simp)

@[simp] lemma rootTree_aux : generateSet {[]} = {[]} := by
  ext l; constructor
  · intro hl; simp [Membership.mem, Set.Mem] at hl
    induction hl with
    | mem l' hl'=>
      have : l' ∈ ({[]} : Set TreeNode) := by simp [Membership.mem, Set.Mem, *]
      simp [Set.mem_singleton_iff.1 this]
    | tail => contradiction
    | less => contradiction
  · intro hl; simp at hl; simp [Membership.mem, Set.Mem, hl]
    exact generateSet.mem [] (by
      have : ([] : TreeNode) ∈ ({[]} : Set TreeNode) := by simp
      simp [Membership.mem, Set.Mem] at this; exact this)

@[simp] lemma rootTree_eq : rootTree = ⟨({[]} : Set TreeNode),
  rootTree_aux, by simp⟩  := by simp [rootTree, generateTree]

-- ## countChildren

noncomputable def countChildren (T : RootedLabeledTree) (l : TreeNode) : ℕ∞ :=
  (⨆ (m : ℕ) (_ : (m :: l) ∈ T), m + 1 : WithTop ℕ)

@[simp] lemma countChildren_eq_zero {T : RootedLabeledTree} {l : TreeNode} (h : ∀ m, m :: l ∉ T) :
  T.countChildren l = 0 := by simp [countChildren, *]

@[simp] lemma countChildren_eq_top {T : RootedLabeledTree} {l : TreeNode} (h : ∀ m, m :: l ∈ T) :
  T.countChildren l = ⊤ := by
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

@[simp] lemma countChildren_eq_top_iff {T : RootedLabeledTree} {l : TreeNode} :
  (∀ m, m :: l ∈ T) ↔ T.countChildren l = ⊤ := by
  constructor
  · exact countChildren_eq_top
  · intro h; simp [countChildren] at h
    rw [iSup₂_eq_top (fun m => fun (_ : m :: l ∈ T) => (m + 1 : WithTop ℕ))] at h
    intro m; obtain ⟨n, hn, hmn⟩ := h (m + 1) (by simp)
    obtain ⟨m', hm', h'⟩ := WithTop.lt_iff_exists.1 hmn
    specialize h' (n + 1) (by simp)
    rw [show (m : WithTop ℕ) + 1 = ↑(m + 1) from by simp] at hm'
    rw [←(@WithTop.coe_inj ℕ (m + 1) m').1 hm'] at h'; simp at h'
    obtain ⟨h1, h2⟩ := T.property
    simp [Membership.mem, Set.Mem] at ⊢ hn; rw [←h1] at ⊢ hn
    exact generateSet.less n l hn m (by omega)

@[simp] lemma countChildren_ge {T : RootedLabeledTree} {l : TreeNode} {m : ℕ} (h : m :: l ∈ T) :
  m + 1 ≤ T.countChildren l := by simp [countChildren]; exact @le_iSup₂ (WithTop ℕ) ℕ _ _ _ _ h

lemma countChildren_mem {T : RootedLabeledTree} {l : TreeNode} {h : T.countChildren l ≠ ⊤}
  {h' : T.countChildren l ≠ 0} : ∃ m : ℕ, m :: l ∈ T ∧ T.countChildren l = m + 1 := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  have : n ≠ 0 := by by_contra h'; have := Eq.symm <| h' ▸ hn; simp at this; contradiction
  use (n - 1); constructor
  · have : ↑n - 1 < T.countChildren l := by
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

lemma countChildren_ge_iff {T : RootedLabeledTree} {l : TreeNode} {m : ℕ} :
  m :: l ∈ T ↔ m + 1 ≤ T.countChildren l := by
  constructor
  · exact countChildren_ge
  · intro h
    by_cases T.countChildren l = ⊤
    · exact countChildren_eq_top_iff.2 ‹_› m
    · set n := (T.countChildren l).untop ‹_› with hn
      have hn : ↑n = T.countChildren l := Eq.symm <| (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hn
      have : m + 1 ≤ n := by
        rw [←hn] at h
        obtain ⟨m', hm', h'⟩ := WithTop.le_coe_iff.1 h
        rw [show (m : WithTop ℕ) + 1 = ↑(m + 1) from by simp] at hm'
        have := (@WithTop.coe_inj ℕ (m + 1) m').1 hm'
        rw [←(@WithTop.coe_inj ℕ (m + 1) m').1 hm'] at h'; exact h'
      have : n ≠ 0 := by omega
      have : (n - 1) :: l ∈ T := by
        obtain ⟨k, hk, hk'⟩ := @T.countChildren_mem l ‹_›
          (by rw [←hn]; exact not_imp_not.2 WithTop.coe_inj.1 this)
        rw [←hn] at hk'
        have : k = n - 1 := by
          have := WithTop.coe_inj.1 hk'; simp at this; omega
        exact this ▸ hk
      obtain ⟨h1, h2⟩ := T.property; simp [Membership.mem, Set.Mem] at this ⊢; rw [←h1] at this ⊢
      exact generateSet.less (n - 1) l this m (by omega)

private def ext_of_countChildren_aux {T1 T2 : RootedLabeledTree}
  (h : ∀ l, T1.countChildren l = T2.countChildren l) (l : TreeNode) : l ∈ T1 → l ∈ T2 := by
  obtain ⟨h1, h1'⟩ := Subtype.property T1; obtain ⟨h2, h2'⟩ := Subtype.property T2
  simp [Membership.mem, Set.Mem]; intro hl
  cases l with
  | nil => exact T2.nil_mem
  | cons m l' =>
    have := countChildren_ge_iff.2 <| h l' ▸ T1.countChildren_ge hl
    simp [Membership.mem, Set.Mem] at this; exact this

@[ext] def ext_of_countChildren (T1 T2 : RootedLabeledTree)
  (h : ∀ l, T1.countChildren l = T2.countChildren l) : T1 = T2 := by
  apply Subtype.ext_iff.2; ext l
  constructor
  · exact ext_of_countChildren_aux h l
  · exact ext_of_countChildren_aux (fun l => Eq.symm <| h l) l

noncomputable instance : FunLike RootedLabeledTree TreeNode ℕ∞ where
  coe T := T.countChildren
  coe_injective' T1 T2 h := by
    ext l; simp at h; have := congrArg (fun f => f l) h; simpa using this

-- ## descendantTreeAt

def descendantTreeAt {T : RootedLabeledTree} (x : TreeNode) (hx : x ∈ T) : RootedLabeledTree := ⟨
  {x' | x' ++ x ∈ T}, by
    obtain ⟨h1, h2⟩ := T.property
    ext l; constructor
    · intro hl; simp
      induction hl with
      | mem => simp_all [Membership.mem, Set.Mem, setOf]
      | tail m l' hl' ih =>
        simp [Membership.mem, Set.Mem] at ⊢ ih; rw [←h1] at ⊢ ih
        exact generateSet.tail m (l' ++ x) ih
      | less m l' hl' n hnm ih =>
        simp [Membership.mem, Set.Mem] at ⊢ ih; rw [←h1] at ⊢ ih
        exact generateSet.less m (l' ++ x) ih n hnm
    · intro hl; exact generateSet.mem l hl
    , by
      apply not_imp_not.2 Set.not_nonempty_iff_eq_empty.2; simp only [not_not]
      exact ⟨[], by simp [*]⟩
  ⟩

-- ## height

noncomputable def height (T : RootedLabeledTree) : ℕ∞ :=
  (⨆ (x : TreeNode) (_ : x ∈ T), x.length : WithTop ℕ)

@[simp] lemma mem_length_at_most_height {T : RootedLabeledTree} : ∀ v ∈ T, v.length ≤ T.height := by
  simp [height]; exact @le_iSup₂ _ _ _ _ (fun v => fun (_ : v ∈ T) => (v.length : WithTop ℕ))

-- ## truncation

def truncation (T : RootedLabeledTree) (n : ℕ) : RootedLabeledTree := ⟨
  {x | x.length ≤ n ∧ x ∈ T},  by
    obtain ⟨h1, h2⟩ := T.property; ext l; constructor
    · intro hl; simp
      induction hl with
      | mem l' ih=> simp [setOf] at ih; exact ih
      | tail m l' hl' ih =>
        simp [Membership.mem, Set.Mem] at ⊢ ih; rw [←h1] at ⊢ ih
        exact ⟨by omega, generateSet.tail m l' ih.2⟩
      | less m l' hl' n hnm ih =>
        simp [Membership.mem, Set.Mem] at ⊢ ih; rw [←h1] at ⊢ ih
        exact ⟨by omega, generateSet.less m l' ih.2 n hnm⟩
    · intro hl; exact generateSet.mem l hl
    , by
      apply not_imp_not.2 Set.not_nonempty_iff_eq_empty.2; simp only [not_not]
      exact ⟨[], by simp [*]⟩
  ⟩

@[simp] lemma truncation_zero {T : RootedLabeledTree} : T.truncation 0 = rootTree := by
  rw [rootTree_eq, truncation]; apply Subtype.ext
  simp; ext; constructor <;> simp <;> aesop

lemma truncation_height_at_most {T : RootedLabeledTree} (n : ℕ) :
  (T.truncation n).height ≤ n := by
  simp [truncation, height, instMembershipTreeNode]
  apply @iSup₂_le (WithTop ℕ); intro l hl; exact ENat.coe_le_coe.2 hl.1

@[simp] lemma truncation_mem_length_at_most {T : RootedLabeledTree} (n : ℕ) :
  ∀ v ∈ T.truncation n, v.length ≤ n := by
  intro v hv; have := le_trans (mem_length_at_most_height v hv) (@truncation_height_at_most T n)
  simp at this; exact this

@[simp] lemma truncation_truncation {T : RootedLabeledTree} {n m : ℕ} :
  (T.truncation n).truncation m = T.truncation (min n m) := by
  simp [truncation, instMembershipTreeNode]; apply Subtype.val_inj.1; ext; simp; aesop

@[simp] lemma mem_of_mem_truncation {T : RootedLabeledTree} {n : ℕ} {l : TreeNode}
  (hl : l ∈ T.truncation n) : l ∈ T := by
  simp [truncation, setOf, Membership.mem, Set.Mem] at hl ⊢; exact hl.2

@[simp] lemma truncation_subset {T : RootedLabeledTree} {n : ℕ} : T.truncation n ⊆ T := by
  dsimp [instHasSubset]; simp [Set.subset_def]; exact @mem_of_mem_truncation T n

@[simp] lemma mem_higher_truncation_of_mem_truncation {T : RootedLabeledTree} {n m : ℕ}
  (hnm : n < m) {l : TreeNode} (hl : l ∈ T.truncation n) : l ∈ T.truncation m := by
  simp [truncation, setOf, Membership.mem, Set.Mem] at hl ⊢; exact ⟨by omega, hl.2⟩

@[simp] lemma mem_truncation_of_mem {T : RootedLabeledTree} {n : ℕ} {l : TreeNode}
  (hl : l.length ≤ n) (hl' : l ∈ T) : l ∈ T.truncation n := by
  simp [truncation, setOf, Membership.mem, Set.Mem] at hl' ⊢; exact ⟨by omega, hl'⟩

@[simp] lemma mem_truncation_of_mem_other_truncation {T : RootedLabeledTree} {n m : ℕ}
  {l : TreeNode} (hl : l.length ≤ n) (hl' : l ∈ T.truncation m) : l ∈ T.truncation n := by
  simp [truncation, setOf, Membership.mem, Set.Mem] at hl ⊢; exact ⟨by omega, hl'.2⟩

lemma ext_of_truncation {T1 T2 : RootedLabeledTree} (h : ∀ n, T1.truncation n = T2.truncation n) :
  T1 = T2 := by
  apply Subtype.ext_iff.2; ext l; constructor
  · obtain ⟨h1, h1'⟩ := Subtype.property T1; obtain ⟨h2, h2'⟩ := Subtype.property T2
    simp [Membership.mem, Set.Mem]; intro hl
    cases l with
    | nil => exact T2.nil_mem
    | cons m l' =>
      specialize h (l'.length + 1)
      simp [truncation, Membership.mem, Set.Mem] at h
      have h := Subtype.val_inj.2 h; simp [setOf] at h
      have h := congrArg (fun f ↦ f (m :: l')) h; simp at h
      exact h.1 ‹_›
  · obtain ⟨h1, h1'⟩ := Subtype.property T1; obtain ⟨h2, h2'⟩ := Subtype.property T2
    simp [Membership.mem, Set.Mem]; intro hl
    cases l with
    | nil => exact T1.nil_mem
    | cons m l' =>
      specialize h (l'.length + 1)
      simp [truncation, Membership.mem, Set.Mem] at h
      have h := Subtype.val_inj.2 h; simp [setOf] at h
      have h := congrArg (fun f ↦ f (m :: l')) h; simp at h
      exact h.2 ‹_›

-- ## heightCongr

noncomputable def heightCongr (T1 T2 : RootedLabeledTree) : ℕ∞ :=
  (⨆ (n : ℕ) (_ : T1.truncation n = T2.truncation n), n : WithTop ℕ)

@[simp] lemma heightCongr_comm {T1 T2 : RootedLabeledTree} :
  heightCongr T1 T2 = heightCongr T2 T1 := by simp [heightCongr, eq_comm]

lemma ext_of_top_heightCongr {T1 T2 : RootedLabeledTree} (h : heightCongr T1 T2 = ⊤) :
  T1 = T2 := by
  simp [heightCongr] at h
  have h' := (@iSup₂_eq_top (WithTop ℕ) ℕ _ _ (fun n => fun _ => n)).1 h
  apply ext_of_truncation; intro n; obtain ⟨m, hm, hnm⟩ := h' n (by simp)
  have := ENat.coe_lt_coe.1 hnm
  have := congrArg (fun T : RootedLabeledTree => T.truncation n) hm
  simp [(show min m n = n from by omega)] at this; exact this

@[simp] lemma heightCongr_self_eq_top {T : RootedLabeledTree} : heightCongr T T = ⊤ := by
  simp [heightCongr]; apply (@iSup_eq_top (WithTop ℕ) ℕ _ _).2; intro n hn
  set n' := n.untop (by aesop) with hn'; have := (WithTop.untop_eq_iff _).1 (Eq.symm hn')
  use n' + 1; rw [this]; exact WithTop.coe_lt_coe.2 (show n' < n' + 1 from by omega)

@[simp] lemma heightCongr_apply {T T' : RootedLabeledTree} (n : ℕ) (hn : n ≤ heightCongr T T') :
  T.truncation n = T'.truncation n := by
  by_cases h : heightCongr T T' = ⊤
  · exact congrArg (fun T => T.truncation n) <| ext_of_top_heightCongr h
  · by_cases n = 0
    · subst_vars; simp
    · have : n - 1 < heightCongr T T' := by
        obtain ⟨n', hn'⟩ := WithTop.ne_top_iff_exists.1 h
        rw [←hn'] at ⊢ hn; simp at ⊢ hn; apply ENat.coe_lt_coe.2; omega
      rw [heightCongr, iSup_subtype', iSup] at hn this
      obtain ⟨n', hn'1, hn'2⟩ := (@lt_sSup_iff (WithTop ℕ) _ _ _).1 this
      simp at hn'1; obtain ⟨n'', hn'3, hn'4⟩ := hn'1
      simp [←hn'4] at hn'2; have := ENat.coe_lt_coe.1 hn'2
      have := congrArg (fun T => T.truncation n) hn'3
      simp [show min n'' n = n from by omega] at this; exact this

@[simp] lemma heightCongr_apply_iff {T T' : RootedLabeledTree} (n : ℕ) :
  n ≤ heightCongr T T' ↔ T.truncation n = T'.truncation n := by
  constructor
  · exact heightCongr_apply n
  · intro hn; rw [heightCongr, iSup_subtype', iSup]
    apply (@le_sSup_iff (WithTop ℕ) _ _ _).2; simp [upperBounds]
    intro m hm; exact hm n hn

lemma heightCongr_ultra (T1 T2 T3 : RootedLabeledTree) :
  min (heightCongr T1 T2) (heightCongr T2 T3) ≤ heightCongr T1 T3 := by
  by_cases h' : heightCongr T1 T3 = ⊤
  · simp [*]
  · by_contra h; simp at h
    set m := heightCongr T1 T3 with hm
    set m' := m.untop ‹_› with hm'
    have hm'' := (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hm'
    have : T1.truncation (m' + 1) = T2.truncation (m' + 1) :=
      @heightCongr_apply T1 T2 (m' + 1) (by
        have := hm'' ▸ h.1
        by_cases heightCongr T1 T2 = ⊤
        · simp [*]
        · set n := heightCongr T1 T2 with hn
          set n' := n.untop ‹_› with hn'
          have hn'' := (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hn'
          have := ENat.coe_lt_coe.1 <| hn'' ▸ this
          rw [hn'']; apply ENat.coe_le_coe.2; omega
        )
    have : T2.truncation (m' + 1) = T3.truncation (m' + 1) :=
      @heightCongr_apply T2 T3 (m' + 1) (by
        have := hm'' ▸ h.2
        by_cases heightCongr T2 T3 = ⊤
        · simp [*]
        · set n := heightCongr T2 T3 with hn
          set n' := n.untop ‹_› with hn'
          have hn'' := (WithTop.untop_eq_iff ‹_›).1 <| Eq.symm hn'
          have := ENat.coe_lt_coe.1 <| hn'' ▸ this
          rw [hn'']; apply ENat.coe_le_coe.2; omega
        )
    have : T1.truncation (m' + 1) = T3.truncation (m' + 1) := Eq.trans ‹_› ‹_›
    have := @le_iSup₂_of_le (WithTop ℕ) ℕ (fun n => T1.truncation n = T3.truncation n) _
      (m' + 1) (fun n => fun _ => (n : WithTop ℕ)) (m' + 1) ‹_› (by simp); simp at this
    have heq := @rfl _ (heightCongr T1 T3); conv at heq => left; simp [heightCongr]
    conv at this => rhs; rw [heq, ←hm, hm'']
    have := ENat.coe_le_coe.1 this; simp at this

-- ## treeDist

noncomputable def treeDist (T1 T2 : RootedLabeledTree) : ℝ :=
  ((1 + (heightCongr T1 T2 : ENNReal))⁻¹).toReal

lemma ext_of_zero_treeDist {T1 T2 : RootedLabeledTree} (h12 : treeDist T1 T2 = 0) :
  T1 = T2 := by
  simp [treeDist, ENNReal.toReal, ENNReal.toNNReal] at h12
  rcases h12 with (h12|h12)
  · have h12 := ENNReal.inv_eq_zero.1 h12; simp at h12
    exact ext_of_top_heightCongr h12
  · have := ENNReal.inv_eq_top.1 h12; aesop

private lemma treeDist_eq_aux {T1 T2 : RootedLabeledTree} : (fun (x : ENat)
  => - ((1 + (x : ENNReal))⁻¹).toReal) (heightCongr T1 T2) = - treeDist T1 T2 := by simp [treeDist]

private lemma treeDist_mono' : StrictMono fun (x : ENat) => - ((1 + (x : ENNReal))⁻¹).toReal := by
  simp only [StrictMono]; intro a b hab
  have : a.toENNReal < b.toENNReal := by simp [*]
  have : 1 + a.toENNReal < 1 + b.toENNReal := by
    apply (ENNReal.add_lt_add_iff_left (show 1 ≠ ⊤ from by simp)).2; simp [*]
  have := ENNReal.inv_lt_inv.2 this
  have := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 this
  simp only [neg_lt_neg_iff, *]

private lemma treeDist_mono : Monotone fun (x : ENat) => - ((1 + (x : ENNReal))⁻¹).toReal := by
  apply StrictMono.monotone; exact treeDist_mono'

lemma treeDist_ultra (T1 T2 T3 : RootedLabeledTree) :
  treeDist T1 T3 ≤ max (treeDist T1 T2) (treeDist T2 T3) := by
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

noncomputable instance : MetricSpace RootedLabeledTree where
  dist := treeDist
  dist_self := by simp [treeDist]
  dist_comm := by simp [treeDist]
  dist_triangle T1 T2 T3 := le_trans (treeDist_ultra T1 T2 T3) <| max_le_add_of_nonneg (by
    simp [treeDist]) (by simp [treeDist])
  eq_of_dist_eq_zero := ext_of_zero_treeDist

instance : IsUltrametricDist RootedLabeledTree where
  dist_triangle_max := treeDist_ultra

--  ## CompleteSpace

private instance instUniformityBasis' : (uniformity RootedLabeledTree).HasBasis
  (fun _ => True) (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ENNReal))⁻¹}) :=
  EMetric.mk_uniformity_basis (by simp) (by
    simp; intro ε hε; obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε); use n
    simp [ENNReal.inv_lt_iff_inv_lt] at hn; simp [ENNReal.inv_le_iff_inv_le]
    exact le_of_lt <| lt_trans hn (by apply ENNReal.coe_lt_coe.2; simp))

def uniformityBasis := fun n =>
  {p : RootedLabeledTree × RootedLabeledTree | (p.1).truncation (n + 1) = (p.2).truncation (n + 1)}

private lemma uniformityBasis_eq_aux : (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ENNReal))⁻¹})
  = uniformityBasis := by
  ext n p; simp [uniformityBasis, edist, PseudoMetricSpace.edist, treeDist]; constructor
  · intro h; have h := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 h
    simp [-ENNReal.toReal_inv, ←ENNReal.toReal_inv] at h
    have h := (ENNReal.add_lt_add_iff_left (by simp)).1 h
    rw [show (n : ENNReal) = ((n : ENat) : ENNReal) from by simp] at h
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

instance instUniformityBasis : (uniformity RootedLabeledTree).HasBasis
  (fun _ => True) uniformityBasis := uniformityBasis_eq_aux ▸ instUniformityBasis'

instance : CompleteSpace RootedLabeledTree where
  complete := by
    intro f hf; have hf' := (by simpa [Cauchy] using hf)
    let E (n : ℕ) := {p : RootedLabeledTree × RootedLabeledTree |
      (p.1).truncation n = (p.2).truncation n}
    have memE (n : ℕ): E n ∈ uniformity RootedLabeledTree := by
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
    have hSsub' (n : ℕ) (T1 T2) : T1 ∈ S n → T2 ∈ S n → T1.truncation n = T2.truncation n := by
      intro h1 h2; have : (T1, T2) ∈ (S n) ×ˢ (S n) := by
        simp only [Set.mem_prod, and_self, h1, h2]
      have := Set.mem_of_subset_of_mem (hSsub n) this;
      simp only [Set.mem_setOf_eq, E] at this; exact this
    choose T' hT'mem using hSne
    have hT'tr (n m : ℕ) : (T' (n + m)).truncation n = (T' n).truncation n := by
      obtain ⟨U, hU⟩ : (S (n + m) ∩ S n).Nonempty := by
        by_contra h; exact (not_imp_not.2 Filter.empty_mem_iff_bot.1 <| Filter.neBot_iff.1 hf'.1)
          <| (Set.not_nonempty_iff_eq_empty.1 h) ▸ f.inter_mem (hSmem (n + m)) (hSmem n)
      have h1 := hSsub' (n + m) U (T' (n + m)) ((Set.mem_inter_iff _ _ _).1 hU).1 (hT'mem (n + m))
      have h2 := hSsub' n U (T' n) ((Set.mem_inter_iff _ _ _).1 hU).2 (hT'mem n)
      have h1 := congrArg (fun T => T.truncation n) h1; simp at h1
      exact h1 ▸ h2
    let Tval : Set TreeNode := fun l => l ∈ ((T' l.length).truncation l.length)
    set T : RootedLabeledTree := ⟨Tval, by
      ext l; constructor
      · intro hl; induction hl with
        | mem l' hl' => simp only [Membership.mem, Set.Mem, hl']
        | tail m l' hl' ih =>
          have ih := @tail_mem ((T' (l'.length + 1)).truncation (l'.length + 1)) m l' ih
          simp only [Membership.mem, Set.Mem, ne_eq, Tval] at ⊢ ih; rw [←hT'tr l'.length 1]
          exact @mem_truncation_of_mem_other_truncation _
            l'.length (l'.length + 1) l' (by omega) ih
        | less m l' hl' n hnm ih =>
          exact @less_mem ((T' (l'.length + 1)).truncation (l'.length + 1)) m n l' ih hnm
      · exact generateSet.mem l
      , Set.nonempty_iff_ne_empty.1 ⟨[], by
        have : ([] : TreeNode) ∈ ({[]} : Set TreeNode) := by simp only [Set.mem_singleton_iff]
        simp [Tval, Membership.mem, Set.Mem] at ⊢ this; exact this⟩⟩
    use T; have := @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T
    simp only [uniformityBasis, Set.mem_setOf_eq] at this
    refine (this.ge_iff.mpr ?_); simp only [forall_const]
    have hTtr (n : ℕ) : T.truncation n = (T' n).truncation n := by
      simp only [truncation, ne_eq, T, Tval]; apply Subtype.coe_inj.1; ext l;
      simp [Membership.mem, Set.Mem, setOf]; intro hl
      have := (show l.length + (n - l.length) = n from by omega) ▸ hT'tr l.length (n - l.length)
      constructor
      · intro hl'; exact @mem_of_mem_truncation _ l.length _
          (this ▸ mem_truncation_of_mem (by omega) hl')
      · intro hl'; exact @mem_of_mem_truncation _ l.length _
          (Eq.symm this ▸ mem_truncation_of_mem (by omega) hl')
    intro n; exact f.sets_of_superset (hSmem (n + 1)) (by
      simp only [Set.subset_def, Set.mem_setOf_eq]; intro U hU; rw [hTtr (n + 1)]
      exact hSsub' (n + 1) U (T' (n + 1)) hU (hT'mem (n + 1)))

instance : MeasurableSpace RootedLabeledTree := borel RootedLabeledTree

-- ## generateSet

private def generate_tail_of_single (l : TreeNode) : Set TreeNode :=
  ⋃ (n : Fin (l.length + 1)), {l.drop n}

@[simp] private lemma finite_generate_tail_of_single (l : TreeNode) :
  (generate_tail_of_single l).Finite := by
  simp only [generate_tail_of_single]; apply Set.finite_iUnion; simp

@[simp] private lemma mem_self_generate_tail_of_single (l : TreeNode) :
  l ∈ generate_tail_of_single l := by simp [generate_tail_of_single]; use 0; simp

@[simp] private lemma treeNode_eq_of_mem_generate_tail_of_single_of_same_length (v u : TreeNode)
  (hvu : v.length = u.length) (hu : u ∈ generate_tail_of_single v) : u = v := by
  simp [generate_tail_of_single] at hu; obtain ⟨n, hn⟩ := hu
  have := n.is_lt; set n' : ℕ := ↑n with hn'
  have := Eq.symm hvu ▸ congrArg List.length hn; simp at this
  have := (show n' = 0 from by omega) ▸ hn; simp at this; exact Eq.symm this

private def generate_tail (s : Set TreeNode) : Set TreeNode := ⋃ l : ↑s, generate_tail_of_single l

@[simp] private lemma finite_generate_tail_of_finite (s : Set TreeNode) (hs : s.Finite) :
  (generate_tail s).Finite := by
  simp only [generate_tail]
  apply fun h => @Set.finite_iUnion _ _ (Set.finite_coe_iff.2 hs) _ h; simp

@[simp] private lemma mem_self_generate_tail (l : TreeNode) (s : Set TreeNode) (h : l ∈ ↑s) :
  l ∈ generate_tail s := by simp [generate_tail]; use l; simp [*]

@[simp] private lemma tail_mem_of_mem_generate_tail (m : ℕ) (l : TreeNode) (s : Set TreeNode)
  (h : m :: l ∈ generate_tail s) : l ∈ generate_tail s := by
  simp [generate_tail] at h ⊢; obtain ⟨l', hl'1, hl'2⟩ := h
  simp [generate_tail_of_single] at hl'2 ⊢; obtain ⟨⟨n, hn⟩, hl'2⟩ := hl'2; simp at hl'2
  by_cases hl'3 : n = l'.length
  · simp [hl'3] at hl'2
  · use l'; simp [*]; use ⟨n + 1, by omega⟩; simp only [←@List.drop_drop _ 1 n l', hl'2,
    List.drop_succ_cons, List.drop_zero]

private def generate_less_of_single (l : TreeNode) (hl : l ≠ []) : Set TreeNode :=
  ⋃ (n : Fin (l.head hl + 1)), {(n : ℕ) :: l.tail}

@[simp] private lemma finite_generate_less_of_single (l : TreeNode) (hl : l ≠ []) :
  (generate_less_of_single l hl).Finite := by
  simp only [generate_less_of_single]; apply Set.finite_iUnion; simp

@[simp] private lemma mem_self_generate_less_of_single (l : TreeNode) (hl : l ≠ []) :
  l ∈ generate_less_of_single l hl := by
  simp [generate_less_of_single]; use ⟨l.head hl, by omega⟩; simp

@[simp] private lemma same_length_of_mem_generate_less_of_single (v u : TreeNode) (hv : v ≠ [])
  (hu : u ∈ generate_less_of_single v hv) : v.length = u.length := by
  simp [generate_less_of_single] at hu; obtain ⟨m, hu'⟩ := hu
  have : v.length ≠ 0 := (by simp [hv]); have := congrArg List.length hu'; simp at this
  rw [(show v.length - 1 + 1 = v.length from by omega)] at this; exact this

private def generate_less (s : Set TreeNode) (hs : [] ∉ s) :=
  ⋃ l : ↑s, generate_less_of_single l (by aesop)

@[simp] private lemma finite_generate_less (s : Set TreeNode) (hs : [] ∉ s) (hs' : s.Finite) :
  (generate_less s hs).Finite := by
  simp only [generate_less]
  apply fun h => @Set.finite_iUnion _ _ (Set.finite_coe_iff.2 hs') _ h; simp

@[simp] private lemma mem_self_generate_less (l : TreeNode) (s : Set TreeNode) (hs : [] ∉ s)
  (hl' : l ∈ ↑s) : l ∈ generate_less s hs := by simp [generate_less]; use l, hl'; simp

@[simp] private lemma cons_mem_of_mem_generate_less (s : Set TreeNode) (hs : [] ∉ s) (m : ℕ)
  (l : TreeNode) (hl : m :: l ∈ generate_less s hs) : ∃ n, m ≤ n ∧ n :: l ∈ s := by
  simp [generate_less] at hl; obtain ⟨l', hl'1, hl'2⟩ := hl
  simp [generate_less_of_single] at hl'2; obtain ⟨⟨⟨m', hm'⟩, hl'2⟩, hl'3⟩ := hl'2
  cases l' with
  | nil => exact False.elim <| hs hl'1
  | cons n l' =>
    use n; simp_all only [List.tail_cons]; simp only [List.head_cons] at hm'; subst_vars
    exact ⟨by omega, hl'1⟩

@[simp] private lemma less_mem_of_mem_generate_less (s : Set TreeNode) (hs : [] ∉ s) (n m : ℕ)
  (hmn : n ≤ m) (l : TreeNode) (hl : m :: l ∈ generate_less s hs) : n :: l ∈ generate_less s hs
  := by
  obtain ⟨n', hmn', hl'⟩ := cons_mem_of_mem_generate_less s hs m l hl
  simp [generate_less]; use n' :: l, hl'; simp [generate_less_of_single]; use ⟨n, by omega⟩

private lemma generateSet_eq_generate_tail_then_less (s : Set TreeNode) (hs : s ≠ ∅) :
  generateSet s = {[]} ∪ generate_less (generate_tail s \ {[]}) (by simp) := by
  ext l; simp only [Set.singleton_union, Set.mem_insert_iff]; constructor
  · intro hl; by_cases hl'1 : l = []
    · left; exact hl'1
    · right; induction hl with
      | mem l' hl'2 =>
        exact mem_self_generate_less l' _ _ (by simp [*]; exact mem_self_generate_tail l' s hl'2)
      | tail m l' hl'2 ih =>
        simp only [reduceCtorEq, not_false_eq_true, forall_const] at ih
        obtain ⟨n, hmn, ih⟩ := cons_mem_of_mem_generate_less _ _ m l' ih
        simp only [generate_less, Set.iUnion_coe_set, Set.mem_diff, Set.mem_singleton_iff,
          Set.mem_iUnion]; use l'
        simp only [Set.mem_diff, Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true,
          and_true] at ih; use ⟨tail_mem_of_mem_generate_tail n l' s ih, hl'1⟩
        exact mem_self_generate_less_of_single l' hl'1
      | less m l' hl'2 n hnm ih =>
        simp only [reduceCtorEq, not_false_eq_true, forall_const] at ih
        exact less_mem_of_mem_generate_less _ _ n m hnm l' ih
  · intro hl; by_cases hl'1 : l = []
    · have := hl'1 ▸ @nil_mem (generateTree s hs)
      simp only [generateTree, instMembershipTreeNode] at this
      exact this
    · simp [hl'1, generate_less] at hl; obtain ⟨l', ⟨hl'2, hl'3⟩, hl'4⟩ := hl
      simp [generate_tail] at hl'2; obtain ⟨l'', hl'2, hl'5⟩ := hl'2
      simp [generate_tail_of_single] at hl'5; obtain ⟨⟨n, hn⟩, hl'5⟩ := hl'5; simp only at hl'5
      simp [generate_less_of_single] at hl'4; obtain ⟨⟨m, hm⟩, hl'4⟩ := hl'4; simp only at hl'4
      simp only [Membership.mem, Set.Mem] at hl'2
      have := List.cons_head_tail hl'3 ▸ hl'5 ▸
        @drop_mem (generateTree s hs) l'' (generateSet.mem l'' hl'2) n
      exact hl'4 ▸ @less_mem (generateTree s hs) (l'.head hl'3) m l'.tail this (by omega)

@[simp] lemma finite_of_generateSet_finite {s : Set TreeNode} (hs : s.Finite) :
  Set.Finite (generateSet s) := by
  by_cases s = ∅
  · simp [nil_generate, *]
  · simp only [generateSet_eq_generate_tail_then_less s ‹_›, Set.singleton_union, Set.finite_insert]
    exact finite_generate_less _ (by aesop)
      <| @Finite.Set.finite_diff _ _ {[]} <| finite_generate_tail_of_finite s hs

@[simp] lemma finite_of_generate_finite {s : Set TreeNode} (hs : s ≠ ∅) (hs' : s.Finite) :
  Set.Finite (generateTree s hs).val := by
  simp [generateTree, finite_of_generateSet_finite hs']

@[simp] lemma finite_truncation_of_finite {T : RootedLabeledTree} (hT : Set.Finite T.val) (n : ℕ) :
  Set.Finite (T.truncation n).val := by
  have := @truncation_subset T n; simp only [instHasSubset] at this
  have : (T.val \ (T.val \ (T.truncation n).val)) = (T.truncation n).val := by simp [*]
  exact this ▸ @Finite.Set.finite_diff _ T.val (T.val \ (T.truncation n).val) hT

open TreeNode

variable (T : RootedLabeledTree)

-- ## setOfLevelAtMost

@[simp] def setOfLevelAtMost (n : ℕ) : Set TreeNode := (T.truncation n).val

instance instMonotoneSetOfLevelAtMost : Monotone T.setOfLevelAtMost := by
  intro m n hmn; by_cases h : m = n
  · subst m; simp
  · exact @mem_higher_truncation_of_mem_truncation T m n (by omega)

-- ## setOfLevel

def setOfLevel (n : ℕ) : Set TreeNode :=
  (T.truncation n).val \ if n = 0 then ∅ else (T.truncation (n - 1)).val

lemma setOfLevel_def (T : RootedLabeledTree) :
  T.setOfLevel = Set.seqDiff T.setOfLevelAtMost := by
  ext n v; by_cases h : n = 0
  · simp [setOfLevel, Set.seqDiff, h]
  · simp only [Set.seqDiff, setOfLevel, h, setOfLevelAtMost,
      Set.accumulate_of_mono T.setOfLevelAtMost T.instMonotoneSetOfLevelAtMost]

variable {T : RootedLabeledTree}

@[simp] lemma setOfLevel_zero : T.setOfLevel 0 = {[]} := by
  simp [setOfLevel]

@[simp] lemma setOfLevel_same_length {n : ℕ} :
  ∀ ν ∈ T.setOfLevel n, ν.length = n := by
  intro v hv; simp [setOfLevel, truncation] at hv; by_cases h : n = 0
  · have := h ▸ hv.1.1; omega
  · have := (not_imp_not.2 <| hv.2 h) (not_not.2 hv.1.2); omega

@[simp] lemma finite_setOfLevel_of_finite (hT : Set.Finite T.val)
  (n : ℕ) : Set.Finite (T.setOfLevel n) := by
  simp [setOfLevel]; by_cases h : n = 0
  · simp [h]
  · simp [h]; exact @Finite.Set.finite_diff _ _ _ (finite_truncation_of_finite hT n)

@[simp] lemma setOfLevel_subset_setOfLevel {n : ℕ} : T.setOfLevel n ⊆ TreeNode.setOfLevel n := by
  simp [TreeNode.setOfLevel, Set.subset_def]; exact RootedLabeledTree.setOfLevel_same_length

-- ## generationSizeAtLevel

noncomputable def generationSizeAtLevel' (T : RootedLabeledTree) :=
  tsumOfLevel (ENat.toENNReal ∘ T.countChildren)

lemma generationSizeAtLevel'_eq_tsum_sum (T : RootedLabeledTree) (n : ℕ) :
  T.generationSizeAtLevel' n
  = ∑' m, ∑ ν : Set.seqDiff (setOfLevelOfValAtMost n) m, ↑(T.countChildren ↑ν)
  := tsumOfLevel_eq_tsum_sum' _ n (by simp) (by simp)

-- instance _root_.ENat.instTopologicalSpace : TopologicalSpace ENat :=
--   TopologicalSpace.induced ENat.toENNReal inferInstance

-- noncomputable def generationSizeAtLevel' (T : RootedLabeledTree) :=
--   tsumOfLevel T.countChildren

-- #check ENNReal.aemeasurable_of_tendsto'
-- #check ENNReal.aemeasurable_of_tendsto

-- private lemma partial_sums_tendsto_tsum {f : ℕ → ENNReal} :
--   Filter.Tendsto (fun m => ∑ i ∈ Finset.range m, f i) Filter.atTop (nhds (∑' i, f i)) := by
--   apply Summable.tendsto_sum_tsum_nat; simp

-- ## LocallyFinite

def IsLocallyFinite (T : RootedLabeledTree) := ∀ n, Set.Finite (T.truncation n).val

def LocallyFinite := {T : RootedLabeledTree // T.IsLocallyFinite}

lemma isLocallyFinite_of_truncation (hT : T.IsLocallyFinite) (n : ℕ) :
  IsLocallyFinite (T.truncation n) := by simp [IsLocallyFinite] at ⊢ hT; intro m; exact hT (min n m)

def LocallyFinite.generateFinite (s : Set TreeNode) (hs : s ≠ ∅) (hs' : s.Finite) : LocallyFinite :=
  ⟨generateTree s hs, by
    simp [IsLocallyFinite]; exact finite_truncation_of_finite <| finite_of_generate_finite hs hs'⟩

namespace LocallyFinite

noncomputable instance : MetricSpace LocallyFinite := Subtype.metricSpace

instance : IsUltrametricDist LocallyFinite where
  dist_triangle_max T1 T2 T3 := treeDist_ultra T1.val T2.val T3.val

instance : Coe LocallyFinite (Set TreeNode) where
  coe T := T.val

instance : Membership TreeNode LocallyFinite where
  mem T l := l ∈ T.val

instance : HasSubset LocallyFinite where
  Subset T1 T2 := T1.val ⊆ T2.val

-- ## LocallyFinite.truncation

@[simp] def truncation (T : LocallyFinite) (n : ℕ) : LocallyFinite :=
  ⟨T.val.truncation n, isLocallyFinite_of_truncation T.property n⟩

private instance instUniformityBasis' : (uniformity LocallyFinite).HasBasis
  (fun _ => True) (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ENNReal))⁻¹}) :=
  EMetric.mk_uniformity_basis (by simp) (by
    simp; intro ε hε; obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε); use n
    simp [ENNReal.inv_lt_iff_inv_lt] at hn; simp [ENNReal.inv_le_iff_inv_le]
    exact le_of_lt <| lt_trans hn (by apply ENNReal.coe_lt_coe.2; simp))

def uniformityBasis := fun n =>
  {p : LocallyFinite × LocallyFinite | p.1.truncation (n + 1) = p.2.truncation (n + 1)}

private lemma uniformityBasis_eq_aux : (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ENNReal))⁻¹})
  = uniformityBasis := by
  ext n p; simp [uniformityBasis, edist, PseudoMetricSpace.edist, treeDist]; constructor
  · intro h; have h := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 h
    simp [-ENNReal.toReal_inv, ←ENNReal.toReal_inv] at h
    have h := (ENNReal.add_lt_add_iff_left (by simp)).1 h
    rw [show (n : ENNReal) = ((n : ENat) : ENNReal) from by simp] at h
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

instance instUniformityBasis : (uniformity LocallyFinite).HasBasis
  (fun _ => True) uniformityBasis := uniformityBasis_eq_aux ▸ instUniformityBasis'

instance : CompleteSpace LocallyFinite where
  complete := by
    intro f hf; have hf' := (by simpa [Cauchy] using hf)
    let E (n : ℕ) := {p : LocallyFinite × LocallyFinite |
      (p.1.val).truncation n = (p.2.val).truncation n}
    have memE (n : ℕ): E n ∈ uniformity LocallyFinite := by
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
    have hSsub' (n : ℕ) (T1 T2) : T1 ∈ S n → T2 ∈ S n → T1.truncation n = T2.truncation n := by
      intro h1 h2; have : (T1, T2) ∈ (S n) ×ˢ (S n) := by
        simp only [Set.mem_prod, and_self, h1, h2]
      have := Set.mem_of_subset_of_mem (hSsub n) this; simp only [Set.mem_setOf_eq, E] at this
      apply Subtype.coe_inj.1; exact this
    choose T' hT'mem using hSne
    have hT'tr (n m : ℕ) : (T' (n + m)).truncation n = (T' n).truncation n := by
      obtain ⟨U, hU⟩ : (S (n + m) ∩ S n).Nonempty := by
        by_contra h; exact (not_imp_not.2 Filter.empty_mem_iff_bot.1 <| Filter.neBot_iff.1 hf'.1)
          <| (Set.not_nonempty_iff_eq_empty.1 h) ▸ f.inter_mem (hSmem (n + m)) (hSmem n)
      have h1 := hSsub' (n + m) U (T' (n + m)) ((Set.mem_inter_iff _ _ _).1 hU).1 (hT'mem (n + m))
      have h2 := hSsub' n U (T' n) ((Set.mem_inter_iff _ _ _).1 hU).2 (hT'mem n)
      have h1 := congrArg (fun T => T.truncation n) h1; simp at h1 h2; have := h1 ▸ h2; exact this
    let Tval : Set TreeNode := fun l => l ∈ ((T' l.length).truncation l.length)
    set _T : RootedLabeledTree := ⟨Tval, by
      ext l; constructor
      · intro hl; induction hl with
        | mem l' hl' => simp only [Membership.mem, Set.Mem, hl']
        | tail m l' hl' ih =>
          have ih := @tail_mem ((T' (l'.length + 1)).truncation (l'.length + 1)).val m l' ih
          simp only [Membership.mem, Set.Mem, ne_eq, truncation, Tval] at ⊢ ih
          have := hT'tr l'.length 1; simp only [truncation] at this
          rw [←Subtype.coe_inj, ←Subtype.coe_inj] at this; simp only [ne_eq] at this; rw [←this]
          exact @mem_truncation_of_mem_other_truncation _
            l'.length (l'.length + 1) l' (by omega) ih
        | less m l' hl' n hnm ih =>
          exact @less_mem ((T' (l'.length + 1)).truncation (l'.length + 1)).val m n l' ih hnm
      · exact generateSet.mem l
      , Set.nonempty_iff_ne_empty.1 ⟨[], by
        have : ([] : TreeNode) ∈ ({[]} : Set TreeNode) := by simp only [Set.mem_singleton_iff]
        simp [Tval, Membership.mem, Set.Mem] at ⊢ this; exact this⟩⟩
    have hTtr (n : ℕ) : _T.truncation n = (T' n).val.truncation n := by
      simp only [RootedLabeledTree.truncation, ne_eq, truncation, _T, Tval]
      apply Subtype.coe_inj.1; ext l;
      simp [Membership.mem, Set.Mem, setOf]; intro hl
      have := (show l.length + (n - l.length) = n from by omega) ▸ hT'tr l.length (n - l.length)
      simp only [truncation] at this; rw [←Subtype.coe_inj] at this; simp only at this
      constructor
      · intro hl'; exact @mem_of_mem_truncation _ l.length _
          (this ▸ mem_truncation_of_mem (by omega) hl')
      · intro hl'; exact @mem_of_mem_truncation _ l.length _
          (Eq.symm this ▸ mem_truncation_of_mem (by omega) hl')
    set T : LocallyFinite := ⟨_T, by
      simp only [IsLocallyFinite, ne_eq]; intro n; rw [hTtr n]
      have := ((T' n).truncation n).property; simp [IsLocallyFinite] at this
      have := (show min n n = n from by omega) ▸ this n; exact this⟩
    use T; have := @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T
    simp only [uniformityBasis, Set.mem_setOf_eq] at this
    refine (this.ge_iff.mpr ?_); simp only [forall_const]
    have hTtr (n : ℕ) : T.truncation n = (T' n).truncation n := by
      simp only [T, truncation]; apply Subtype.coe_inj.1; simp only; exact hTtr n
    intro n; exact f.sets_of_superset (hSmem (n + 1)) (by
      simp only [Set.subset_def]; intro U hU; rw [hTtr (n + 1)]
      exact hSsub' (n + 1) U (T' (n + 1)) hU (hT'mem (n + 1)))

instance instNhdsBasis (T : LocallyFinite) : (nhds T).HasBasis (fun _ => True)
  fun n => {T' | T'.truncation (n + 1) = T.truncation (n + 1)} :=
  @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T

noncomputable instance instFintypeTruncate (T : LocallyFinite) (n : ℕ) :
  Fintype (T.val.truncation n).val := by
  exact @Fintype.ofFinite _ <| Set.finite_coe_iff.2 <| T.property n

instance : TopologicalSpace.SeparableSpace LocallyFinite where
  exists_countable_dense := by
    let F := { s : Finset TreeNode // s.Nonempty }
    let embed : F → LocallyFinite := fun s => generateFinite s
      (by simp [Finset.nonempty_iff_ne_empty.1 s.property]) (by simp only [Finset.finite_toSet])
    -- `Countable` is inferred in `use` from `Set.countable_range` and `Countable F`, which in turn
    -- is inferred from `Subtype.countable`, `Finset.countable`, and `Countable TreeNode`
    use Set.range embed; constructor
    · exact Set.countable_range embed
    · simp [Dense]; intro T; simp [mem_closure_iff_nhds_basis (instNhdsBasis T)]; intro n
      -- In `Set.toFinset`, `Fintype ↑(T.val.truncation n).val` is required for element in `F`
      -- this means `LocallyFinite` is required here, because otherwise it is not `Fintype`
      use ⟨Set.toFinset (T.val.truncation (n + 1)).val, by
        use []; have := @nil_mem (T.val.truncation (n + 1)); simp [Membership.mem, Set.Mem] at this
        -- In `Set.mem_toFinset`, `Fintype (T.val.truncation n).val` is required likewise
        simp only [ne_eq, Set.mem_toFinset]; simp only [Membership.mem, Set.Mem, *]⟩
      simp only [generateFinite, ne_eq, Set.coe_toFinset, generateTree_val,
        truncation_truncation, min_self, embed]

instance : MeasurableSpace LocallyFinite := borel LocallyFinite

instance : Coe LocallyFinite RootedLabeledTree where
  coe T := T.val

variable (T : LocallyFinite) (ν : TreeNode) (n : ℕ)

@[simp] lemma countChildren_ne_top : countChildren ↑T ν ≠ ⊤ := by
  simp [←countChildren_eq_top_iff]
  set S := T.val.truncation (ν.length + 1) with hS
  have hT := (@Nat.card_eq_fintype_card _
    <| hS ▸ (@Fintype.ofFinite _ <| T.property (ν.length + 1)))
    ▸ hS ▸ (@Finite.equivFin _ <| T.property (ν.length + 1))
  set n := @Fintype.card _ <| hS ▸ (@Fintype.ofFinite _ <| T.property (ν.length + 1)) with hn
  use n; by_contra h; have h := hS ▸ @mem_truncation_of_mem _ (ν.length + 1) _ (by simp) h
  let F (m : Fin (n + 1)) : S.val.Elem := ⟨m :: ν, @less_mem S n _ ν h (by omega)⟩
  have := Fintype.card_le_of_injective F (by simp [Function.Injective, F]; omega); simp [hn] at this

@[simp] lemma countChildren_lt_top : countChildren ↑T ν < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top]; exact countChildren_ne_top T ν

noncomputable def countChildren : ℕ := (T.val.countChildren ν).lift (by simp)

lemma countChildren_eq_toNat : T.countChildren ν = (T.val.countChildren ν).toNat
  := ENat.lift_eq_toNat_of_lt_top (by simp)

@[ext] def ext_of_countChildren (T1 T2 : LocallyFinite)
  (h : ∀ l, T1.countChildren l = T2.countChildren l) : T1 = T2 :=
  Subtype.coe_inj.1 <| RootedLabeledTree.ext_of_countChildren _ _ (by
    intro l; specialize h l; simp [countChildren] at h
    exact @ENat.coe_lift (T1.val.countChildren l) (by simp)
      ▸ h ▸ @ENat.coe_lift (T2.val.countChildren l) (by simp))

@[simp] lemma countChildren_eq_zero_of_not_mem (hv : ν ∉ T) :
  T.countChildren ν = 0 := by
  simp [countChildren, RootedLabeledTree.countChildren, ENat.lift, WithTop.untop_eq_iff]
  have {m : ENat} (hm : m ≤ 0) : m = 0 := by simp only [nonpos_iff_eq_zero] at hm; exact hm
  apply this; apply (@iSup₂_le_iff (WithTop ℕ) ℕ (fun m => m :: ν ∈ T) _).2; intro m hm
  simp; exact hv <| @tail_mem _ _ _ hm

noncomputable instance : FunLike LocallyFinite TreeNode ℕ where
  coe T := T.countChildren
  coe_injective' T1 T2 h := by
    ext l; simp at h; have := congrArg (fun f => f l) h; simpa using this

@[simp] lemma setOfLevel_finite :
  Set.Finite (T.val.setOfLevel n) := by
  simp [setOfLevel]; by_cases n = 0
  · simp [*]
  · simp [*]; apply Set.Finite.diff; exact T.property n

noncomputable instance : Fintype ↑(T.val.setOfLevel n) :=
  @Fintype.ofFinite _ <| Set.finite_coe_iff.2 <| setOfLevel_finite T n

section

noncomputable def _root_.NNReal.toNat := FloorSemiring.floor (α := NNReal)

noncomputable def _root_.ENNReal.toNat := fun x : ENNReal => x.toNNReal.toNat

noncomputable def _root_.ENNReal.toENat := fun x : ENNReal => match x with
  | ⊤ => (⊤ : ENat)
  | some x => x.toNat

end

noncomputable def generationSizeAtLevel' := (T.val.generationSizeAtLevel' n).toNat

noncomputable def generationSizeAtLevel (T : LocallyFinite) :=
  tsumOfLevel T.countChildren

lemma generationSizeAtLevel_eq_tsum_sum :
  T.generationSizeAtLevel n
  = ∑' m, ∑ ν : Set.seqDiff (setOfLevelOfValAtMost n) m, ↑(T.countChildren ↑ν)
  := tsumOfLevel_eq_tsum_sum' _ n (by sorry) (by
    by_cases h : n = 0
    · subst n; simp only [Summable, HasSum, SummationFilter.unconditional_filter, nhds_discrete,
      Filter.tendsto_pure, Filter.eventually_atTop, ge_iff_le, Finset.le_eq_subset]
      rw [setOfLevelOfValAtMost_zero_seqDiff]
      use T.countChildren [], {⟨0, [], by simp⟩}; intro s' hs
      set S := @Sigma ℕ fun m ↦ ↑((fun m ↦ if m = 0 then {[]} else (∅ : Set (List ℕ))) m) with hS
      simp at hS
      sorry
    · sorry
      -- simp [Summable, HasSum]
      -- use ∑ v : T.val.setOfLevel n, T.countChildren v
      -- set S := @Sigma ℕ fun m ↦ ↑(Set.seqDiff (setOfLevelOfValAtMost n) m)
      -- set s : Set S := ⋃ v : T.val.setOfLevel n, {⟨n, v.val, by sorry⟩}
      -- use
    )

#check aemeasurable_coe_nnreal_ennreal_iff

end LocallyFinite

section RootedForest

instance : Coe (WithBot TreeNode) TreeNode where
  coe v := match v with
    | ⊥ => []
    | some v => v

axiom bot_eq_some_nil : (⊥ : WithBot TreeNode) = some ([] : TreeNode)

lemma exists_some (v : WithBot TreeNode) : ∃ l, v = some l := by
  match v with
  | ⊥ => use []; rw [bot_eq_some_nil]
  | some l => use l

def toRootedForest (T : RootedLabeledTree) : RootedForest TreeNode
  (fun v => { i : ℕ // match T v with | ⊤ => True | some k => i < k }) where
  branch v i := (i : ℕ) :: v
  parent_child u v := ↑v ∈ T ∧ ∃ m : ℕ, v = m :: u
  parent_child_def u v := by
    obtain ⟨u, hu⟩ := exists_some u; obtain ⟨v, hv⟩ := exists_some v; simp [*]; constructor
    · intro h; obtain ⟨hvT, m, hmuv⟩ := h; use m; match h : T u with
      | ⊤ => simp [*]
      | some k =>
        have := h ▸ (show T.countChildren u = T u from by simp [instFunLikeTreeNodeENat])
          ▸ countChildren_ge_iff.1 <| (WithBot.coe_inj.1 hmuv) ▸ hvT
        conv at this => left; rw [(show (m : WithTop ℕ) + 1 = ↑(m + 1) from by simp)]
        have := ENat.coe_le_coe.1 this; simp [*]; omega
    · intro h; obtain ⟨m, hmT, h'⟩ := h; match h : T u with
      | ⊤ => use WithBot.coe_inj.1 h' ▸ countChildren_eq_top_iff.2 h m, m; simp [*]
      | some k =>
        simp [*] at hmT; have := ENat.coe_le_coe.2 (show m + 1 ≤ k from by omega)
        conv at this => left; simp
        conv at this => right; rw [←ENat.some_eq_coe, ←WithTop.some_eq_coe k, ←h,
          ←(show T.countChildren u = T u from by simp [instFunLikeTreeNodeENat])]
        use (WithBot.coe_inj.1 h') ▸ countChildren_ge_iff.2 this, m; simp [*]
  root_no_parent := by simp
  acyclic := by
    simp; intro u v w; cases u <;> cases v <;> simp_all [bot_eq_some_nil]
    · sorry
    · sorry
  loopless := by simp; intro u m; cases u <;> simp
  wellfounded := sorry
  IsOrigin v := match v with
    | ⊥ => False
    | some v => v.length = 1
  isOrigin_def := by simp; sorry
  root_bij := sorry
  node_bij := sorry

end RootedForest

end RootedLabeledTree
