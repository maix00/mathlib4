import Mathlib.Probability.RandomGraph.Tree.TreeNode

open TreeNode ENNReal NNReal ENat Cardinal

-- ## generateSet
namespace RLTree

inductive generateSet (s : Set 𝕍) : Set 𝕍
  | mem : (v : 𝕍) → s v → generateSet s v
  | tail : (m : ℕ) → (v : 𝕍) → generateSet s (m :: v) → generateSet s v
  | less : (m : ℕ) → (v : _) → generateSet s (m :: v) → (n : ℕ) → n ≤ m → generateSet s (n :: v)

structure _root_.RLTree where -- Rooted Labeled Tree
  set : Set 𝕍
  generate_refl : generateSet set = set
  non_empty : set ≠ ∅

attribute [simp] generate_refl non_empty

scoped[RLTree] notation "𝕋₀" => RLTree

variable {T T1 T2 : 𝕋₀} {v : 𝕍}

@[ext] lemma ext_of_set (h : T1.set = T2.set) : T1 = T2 := by
  cases T1; cases T2; simp only at h; cases h; rfl

instance : FunLike 𝕋₀ 𝕍 Prop where
  coe T := T.set
  coe_injective' T1 T2 h12 := by ext; simp [h12]

instance : Membership 𝕍 𝕋₀ where
  mem T v := v ∈ T.set

lemma mem_iff : v ∈ T ↔ v ∈ T.set := by constructor <;> intro h <;> exact h

lemma set_eq_of_eq {T1 T2 : 𝕋₀} (h : T1 = T2) : T1.set = T2.set := congrArg @RLTree.set h

instance : HasSubset 𝕋₀ where
  Subset T1 T2 := T1.set ⊆ T2.set

instance : LE 𝕋₀ where
  le := (· ⊆ ·)

variable (s : Set 𝕍) {T : 𝕋₀}

@[simp] lemma nil_generate : generateSet ∅ = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false]; by_contra hv; induction hv <;> assumption

lemma generateSet_mono : Monotone generateSet := by
  intro _ _ _; simp only [Set.le_eq_subset, Set.subset_def]; intro _ h; induction h with
  | mem => exact generateSet.mem _ <| Set.mem_of_subset_of_mem ‹_› ‹_›
  | tail => exact generateSet.tail _ _ ‹_›
  | less => exact generateSet.less _ _ ‹_› _ ‹_›

lemma generateSet_subset : s ⊆ generateSet s := by intro _ _; exact generateSet.mem _ ‹_›

lemma generateSet_proj : generateSet (generateSet s) = generateSet s := by
  ext; constructor
  · intro h; induction h with
      | mem => assumption
      | tail => exact generateSet.tail _ _ ‹_›
      | less => exact generateSet.less _ _ ‹_› _ ‹_›
  · intro; exact generateSet.mem _ ‹_›

lemma generateSet_idempotent : @IsIdempotentElem _ ⟨Function.comp⟩ generateSet := by
  simp only [IsIdempotentElem]; ext; constructor
  · intro h; induction h with
      | mem => assumption
      | tail => exact generateSet.tail _ _ ‹_›
      | less => exact generateSet.less _ _ ‹_› _ ‹_›
  · intro; exact generateSet.mem _ ‹_›

lemma nonempty_of_nonempty (hs : s ≠ ∅) : generateSet s ≠ ∅ := by
  obtain ⟨v, hv⟩ := not_not.1 <| not_imp_not.2 Set.not_nonempty_iff_eq_empty.1 hs
  apply not_imp_not.2 (@Set.not_nonempty_iff_eq_empty _ (generateSet s)).2; apply not_not.2
  exact ⟨v, generateSet.mem v hv⟩

@[simp] lemma nil_mem : [] ∈ T := by
  obtain ⟨v, h⟩ := Set.nonempty_iff_ne_empty.2 T.non_empty; induction v with
  | nil => exact h
  | cons m v' ih => exact ih <| T.generate_refl ▸ generateSet.tail m v' <| T.generate_refl ▸ h

@[simp] lemma tail_mem {m : ℕ} {v : 𝕍} (h : m :: v ∈ T) : v ∈ T :=
  T.generate_refl ▸ generateSet.tail m v <| T.generate_refl ▸ mem_iff.1 h

@[simp] lemma tail_mem' {v : 𝕍} {h : v ∈ T} : v.tail ∈ T := by cases v <;> grind [tail_mem]

@[simp] lemma drop_mem {v : 𝕍} {h : v ∈ T} {n : ℕ} : v.drop n ∈ T := by
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [←@List.drop_drop _ 1 n v, List.drop_one]; exact @tail_mem' T (v.drop n) ih

@[simp] lemma less_mem {m n : ℕ} {v : 𝕍} (h : m :: v ∈ T)
  (hnm : n ≤ m) : n :: v ∈ T :=  mem_iff.2 <| T.generate_refl ▸ generateSet.less m v
  (Eq.symm T.generate_refl ▸ mem_iff.1 h) n hnm

-- ## generateTree

def generateTree (hs : s ≠ ∅) : 𝕋₀ := ⟨generateSet s, generateSet_proj s, nonempty_of_nonempty s hs⟩

@[simp] lemma generateTree_set (T : 𝕋₀) : generateTree T.set T.non_empty = T := by
  simp [generateTree]

def rootTree := generateTree {[]} (by simp)

@[simp] lemma rootTree_aux : generateSet {[]} = {[]} := by
  ext; constructor
  · intro h; induction h <;> first | assumption | contradiction
  · exact generateSet.mem _

@[simp] lemma rootTree_eq : rootTree = ⟨{[]}, rootTree_aux, by simp⟩  := by
  simp [rootTree, generateTree]

instance : Bot 𝕋₀ where
  bot := rootTree

@[simp] lemma rootTree_bot : ⊥ = rootTree := rfl

def univTree := generateTree Set.univ (by simp)

instance : Top 𝕋₀ where
  top := univTree

@[simp] lemma univTree_top : ⊤ = univTree := rfl


-- ## generateSet_eq_generate_tail_then_less

def generate_tail_of_single (v : 𝕍) : Set 𝕍 :=
  ⋃ (n : Fin (‖v‖ₕ + 1)), {v.drop n}

@[simp] lemma finite_generate_tail_of_single (v : 𝕍) :
  (generate_tail_of_single v).Finite := by
  simp only [generate_tail_of_single]; apply Set.finite_iUnion; simp

@[simp] lemma mem_self_generate_tail_of_single (v : 𝕍) :
  v ∈ generate_tail_of_single v := by simp only [generate_tail_of_single,
    Set.iUnion_singleton_eq_range, Set.mem_range]; use 0; simp

@[simp] lemma treeNode_eq_of_mem_generate_tail_of_single_of_same_length (v u : 𝕍)
  (hvu : ‖v‖ₕ = ‖u‖ₕ) (hu : u ∈ generate_tail_of_single v) : u = v := by
  simp only [generate_tail_of_single, Set.iUnion_singleton_eq_range, Set.mem_range] at hu
  obtain ⟨n, hn⟩ := hu
  have := n.is_lt; set n' : ℕ := ↑n with hn'
  have := Eq.symm hvu ▸ congrArg List.length hn; simp at this
  have := (show n' = 0 from by omega) ▸ hn; simp only [List.drop_zero] at this; exact Eq.symm this

def generate_tail (s : Set 𝕍) : Set 𝕍 := ⋃ v : s, generate_tail_of_single v

@[simp] lemma finite_generate_tail_of_finite (s : Set 𝕍) (hs : s.Finite) :
  (generate_tail s).Finite := by
  simp only [generate_tail]
  apply fun h => @Set.finite_iUnion _ _ (Set.finite_coe_iff.2 hs) _ h; simp

@[simp] lemma mem_self_generate_tail (v : 𝕍) (s : Set 𝕍) (h : v ∈ ↑s) :
  v ∈ generate_tail s := by
    simp only [generate_tail, Set.iUnion_coe_set, Set.mem_iUnion, exists_prop]; use v; simp [*]

@[simp] lemma tail_mem_of_mem_generate_tail (m : ℕ) (v : 𝕍) (s : Set 𝕍)
  (h : m :: v ∈ generate_tail s) : v ∈ generate_tail s := by
  simp only [generate_tail, Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at h ⊢
  obtain ⟨v', hv'1, hv'2⟩ := h; simp only [generate_tail_of_single,
    Set.iUnion_singleton_eq_range, Set.mem_range] at hv'2 ⊢
  obtain ⟨⟨n, hn⟩, hv'2⟩ := hv'2; simp only at hv'2
  by_cases hv'3 : n = ‖v'‖ₕ
  · simp [hv'3] at hv'2
  · use v'; simp only [true_and, hv'1]; use ⟨n + 1, by omega⟩
    simp only [←@List.drop_drop _ 1 n v', hv'2, List.drop_succ_cons, List.drop_zero]

def generate_less_of_single (v : 𝕍) (hv : v ≠ []) : Set 𝕍 :=
  ⋃ (n : Fin (v.head hv + 1)), {(n : ℕ) :: v.tail}

@[simp] lemma finite_generate_less_of_single (v : 𝕍) (hv : v ≠ []) :
  (generate_less_of_single v hv).Finite := by
  simp only [generate_less_of_single]; apply Set.finite_iUnion; simp

@[simp] lemma mem_self_generate_less_of_single (v : 𝕍) (hv : v ≠ []) :
  v ∈ generate_less_of_single v hv := by
  simp only [generate_less_of_single, Set.iUnion_singleton_eq_range, Set.mem_range]
  use ⟨v.head hv, by omega⟩; simp

@[simp] lemma same_length_of_mem_generate_less_of_single (v u : 𝕍) (hv : v ≠ [])
  (hu : u ∈ generate_less_of_single v hv) : ‖v‖ₕ = ‖u‖ₕ := by
  simp only [generate_less_of_single, Set.iUnion_singleton_eq_range, Set.mem_range] at hu
  obtain ⟨m, hu'⟩ := hu
  have : ‖v‖ₕ ≠ 0 := (by simp [hv]); have := congrArg List.length hu'; simp only [List.length_cons,
    List.length_tail] at this
  rw [(show ‖v‖ₕ - 1 + 1 = ‖v‖ₕ from by omega)] at this; exact this

def generate_less (s : Set 𝕍) (hs : [] ∉ s) :=
  ⋃ v : ↑s, generate_less_of_single v (by aesop)

@[simp] lemma finite_generate_less (s : Set 𝕍) (hs : [] ∉ s) (hs' : s.Finite) :
  (generate_less s hs).Finite := by
  simp only [generate_less]
  apply fun h => @Set.finite_iUnion _ _ (Set.finite_coe_iff.2 hs') _ h; simp

@[simp] lemma mem_self_generate_less (v : 𝕍) (s : Set 𝕍) (hs : [] ∉ s)
  (hv' : v ∈ ↑s) : v ∈ generate_less s hs := by
  simp only [generate_less, Set.iUnion_coe_set, Set.mem_iUnion]; use v, hv'; simp

@[simp] lemma cons_mem_of_mem_generate_less (s : Set 𝕍) (hs : [] ∉ s) (m : ℕ)
  (v : 𝕍) (hv : m :: v ∈ generate_less s hs) : ∃ n, m ≤ n ∧ n :: v ∈ s := by
  simp only [generate_less, Set.iUnion_coe_set, Set.mem_iUnion] at hv; obtain ⟨v', hv'1, hv'2⟩ := hv
  simp only [generate_less_of_single, Set.iUnion_singleton_eq_range, Set.mem_range, List.cons.injEq,
    exists_and_right] at hv'2; obtain ⟨⟨⟨m', hm'⟩, hv'2⟩, hv'3⟩ := hv'2
  cases v' with
  | nil => exact False.elim <| hs hv'1
  | cons n v' =>
    use n; simp_all only [List.tail_cons]; simp only [List.head_cons] at hm'; subst_vars
    exact ⟨by omega, hv'1⟩

@[simp] lemma less_mem_of_mem_generate_less (s : Set 𝕍) (hs : [] ∉ s) (n m : ℕ)
  (hmn : n ≤ m) (v : 𝕍) (hv : m :: v ∈ generate_less s hs) : n :: v ∈ generate_less s hs
  := by
  obtain ⟨n', hmn', hv'⟩ := cons_mem_of_mem_generate_less s hs m v hv
  simp only [generate_less, Set.iUnion_coe_set, Set.mem_iUnion]; use n' :: v, hv'
  simp only [generate_less_of_single, List.head_cons, List.tail_cons, Set.iUnion_singleton_eq_range,
    Set.mem_range, List.cons.injEq, and_true]; use ⟨n, by omega⟩

lemma generateSet_eq_generate_tail_then_less (s : Set 𝕍) (hs : s ≠ ∅) :
  generateSet s = {[]} ∪ generate_less (generate_tail s \ {[]}) (by simp) := by
  ext v; simp only [Set.singleton_union, Set.mem_insert_iff]; constructor
  · intro hv; by_cases hv'1 : v = []
    · left; exact hv'1
    · right; induction hv with
      | mem v' hv'2 =>
        exact mem_self_generate_less v' _ _ (by
          simp only [Set.mem_diff, Set.mem_singleton_iff, not_false_eq_true, and_true, hv'1]
          exact mem_self_generate_tail v' s hv'2)
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
  · intro hv; by_cases hv'1 : v = []
    · exact hv'1 ▸ @nil_mem (generateTree s hs)
    · simp only [hv'1, generate_less, Set.iUnion_coe_set, Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_iUnion, false_or] at hv; obtain ⟨v', ⟨hv'2, hv'3⟩, hv'4⟩ := hv
      simp only [generate_tail, Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at hv'2
      obtain ⟨v'', hv'2, hv'5⟩ := hv'2
      simp only [generate_tail_of_single, Set.iUnion_singleton_eq_range, Set.mem_range] at hv'5
      obtain ⟨⟨n, hn⟩, hv'5⟩ := hv'5; simp only at hv'5
      simp only [generate_less_of_single, Set.iUnion_singleton_eq_range, Set.mem_range] at hv'4
      obtain ⟨⟨m, hm⟩, hv'4⟩ := hv'4; simp only at hv'4
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
  Set.Finite (generateTree s hs).set := by
  simp [generateTree, finite_of_generateSet_finite hs']

-- ## descendantTreeAt

def descendantTreeAt {T : 𝕋₀} (x : 𝕍) (hx : x ∈ T) : 𝕋₀ := ⟨
  {x' | x' ++ x ∈ T}, by
    ext v; constructor
    · intro hv
      induction hv with
      | mem => assumption
      | tail m v' hv' ih =>
        exact mem_iff.2 <| T.generate_refl ▸ generateSet.tail m (v' ++ x)
          <| Eq.symm T.generate_refl ▸ mem_iff.1 ih
      | less m v' hv' n hnm ih =>
        exact mem_iff.2 <| T.generate_refl ▸ generateSet.less m (v' ++ x)
          (Eq.symm T.generate_refl ▸ mem_iff.1 ih) n hnm
    · intro hv; exact generateSet.mem v hv
    , by
      apply not_imp_not.2 Set.not_nonempty_iff_eq_empty.2; simp only [not_not]
      exact ⟨[], by simp [*]⟩
  ⟩

-- ## height

noncomputable def height (T : 𝕋₀) : ℕ∞ := (⨆ (v : 𝕍) (_ : v ∈ T), ‖v‖ₕ : WithTop ℕ)

scoped[RLTree] notation "‖" T "‖ₕ" => height T

@[simp] lemma mem_length_at_most_height {T : 𝕋₀} : ∀ v ∈ T, ‖v‖ₕ ≤ ‖T‖ₕ := by
  simp only [height]; exact @le_iSup₂ _ _ _ _ (fun v => fun (_ : v ∈ T) => (‖v‖ₕ : WithTop ℕ))

end RLTree
