import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

variable (V : Type*) (κ : WithBot V → Type*)

class RootedForest where
  branch : (v : WithBot V) → (κ v → WithBot V)
  parent_child : (WithBot V) → (WithBot V) → Prop
  parent_child_def : ∀ u v, parent_child u v ↔ ∃ j, branch u j = v
  root_no_parent : ∀ v, ¬ parent_child v ⊥
  acyclic : ∀ {u v w}, parent_child u w → parent_child v w → u = v
  loopless : ∀ u, ¬ parent_child u u
  wellfounded : WellFounded parent_child
  IsOrigin (v : WithBot V) : Prop
  isOrigin_def : ∀ v, IsOrigin v ↔ (∃ u, parent_child v u) ∧ (∀ u, parent_child u v → u = ⊥)
  root_bij : Set.BijOn (branch ⊥) Set.univ { v | IsOrigin v }
  node_bij {v : V} : Set.BijOn (branch v) Set.univ { u | ∃ j, branch v j = u }

namespace RootedForest

attribute [simp] root_no_parent

section LE
variable {V : Type*} {κ : WithBot V → Type*} {F : RootedForest V κ}

scoped infix:50 " ≺ " => @parent_child _ _ _
scoped notation:50 a " ≺[" F:50 "] " b => @parent_child _ _ (F : RootedForest _ ‹_›) a b

@[simp] lemma false_of_not_acyclic {u v v'} (huv : v ≺[F] u) (huv' : v' ≺[F] u) (hvv' : v ≠ v') :
  False := by exact hvv' <| F.acyclic huv huv'

@[simp] lemma root_branch_nonempty_of_has_isOrigin {u} (hu : F.IsOrigin u) : Nonempty (κ ⊥) := by
  have := Set.mem_of_subset_of_mem F.root_bij.surjOn <| Set.mem_setOf.2 hu
  simp at this; obtain ⟨j, hj⟩ := this; exact ⟨j⟩

@[simp] lemma has_root_parent_of_isOrigin {u} (hu : F.IsOrigin u) : F.parent_child ⊥ u := by
  have := Set.mem_of_subset_of_mem F.root_bij.surjOn <| Set.mem_setOf.2 hu
  simp at this; simp [parent_child_def, *]

lemma only_has_root_parent_of_isOrigin {u} (hu : F.IsOrigin u) :
  ∀ v, F.parent_child v u → v = ⊥ := by
  intro v huv; have := F.has_root_parent_of_isOrigin hu; simp [isOrigin_def] at hu
  cases v <;> aesop

noncomputable def root_inv [Nonempty (κ ⊥)] := Function.invFunOn (F.branch ⊥) Set.univ

lemma root_inv_on [Nonempty (κ ⊥)] :
  Set.InvOn F.root_inv (F.branch ⊥) Set.univ { v | F.IsOrigin v } := ⟨by
    simp [Set.LeftInvOn]; intro x; simp [root_inv]
    exact F.root_bij.injOn (Set.mem_univ _) (Set.mem_univ x)
      <| @Function.invFunOn_apply_eq _ _ _ (F.branch ⊥) x _ (Set.mem_univ x), by
    simp [Set.RightInvOn]; intro v hv; simp [root_inv]
    exact @Function.invFunOn_eq _ _ _ (F.branch ⊥) v _ <| (by
      have := F.root_bij.surjOn; simp [Set.SurjOn] at this; simp
      exact Set.mem_range.1 <| Set.mem_of_subset_of_mem this hv)⟩

def root_inv_bij [Nonempty (κ ⊥)]
  := (@Set.bijOn_comm _ _ _ _ F.root_inv _ F.root_inv_on).mpr root_bij

@[simp] lemma root_left_inv {j : κ ⊥} : @F.root_inv _ _ ⟨j⟩ (F.branch ⊥ j) = j :=
  (@F.root_inv_on _ _ ⟨j⟩).left (Set.mem_univ j)

@[simp] lemma root_right_inv {v} {hv : F.IsOrigin v} :
  F.branch ⊥ (@F.root_inv _ _ (F.root_branch_nonempty_of_has_isOrigin hv) v) = v :=
  (@F.root_inv_on _ _ (F.root_branch_nonempty_of_has_isOrigin hv)).right <| Set.mem_setOf.mpr hv

lemma isOrigin_of_has_root_parent {u} (hu : F.parent_child ⊥ u) : F.IsOrigin u := by
  simp [parent_child_def] at hu; obtain ⟨j, hj⟩ := hu; have : Nonempty (κ ⊥) := ⟨j⟩
  let hj' := hj; apply congrArg (@F.root_inv _ _ ⟨j⟩) at hj; simp at hj
  have := Set.mem_of_subset_of_mem F.root_inv_bij.surjOn (hj ▸ Set.mem_univ j)
  simp only [Set.mem_image] at this; rcases this with ⟨v, ⟨hv, hvu⟩⟩
  simp only [Set.mem_setOf_eq] at hv; rw [←hj] at hvu; apply congrArg (F.branch ⊥) at hvu
  simp [*, -hj] at hvu; exact hvu ▸ hv

instance instLT : LT V where
  lt u v := @parent_child _ _ F (u : WithBot V) (v : WithBot V)

scoped notation:50 a " ᵖ≺ " b => @LT.lt _ (instLT _) a b
scoped notation:50 a " ᵖ≺[" F:50 "] " b => @LT.lt _ (instLT (F : RootedForest _ ‹_›)) a b

def toSimpleGraph : SimpleGraph (WithBot V) where
  Adj u v := (u ≺[F] v) ∨ (v ≺[F] u)
  loopless u := by simp [loopless]

def support := F.toSimpleGraph.support

lemma root_or_has_parent_of_mem_support {u} : u ∈ F.support → u = ⊥ ∨ ∃ v, v ≺[F] u := by
  intro ⟨v, huv⟩; simp [toSimpleGraph] at huv; by_cases u = ⊥
  · left; assumption
  · right; by_cases hu : F.IsOrigin u
    · use ⊥; simp [*]
    · simp only [isOrigin_def, not_and_or] at hu; cases hu <;> aesop

lemma mem_support_of_parent {u v} (_ : u ≺[F] v) : u ∈ F.support := by
  simp_all [support, toSimpleGraph, SimpleGraph.support]; use v; left; assumption

lemma mem_support_of_child {u v} (_ : u ≺[F] v) : v ∈ F.support := by
  simp_all [support, toSimpleGraph, SimpleGraph.support]; use u; right; assumption

open SimpleGraph Walk in
private lemma mem_support_of_walk_start_not_nil {u v : WithBot V} (puv : F.toSimpleGraph.Walk u v)
  (hpuv : ¬puv.Nil) : u ∈ F.support := by
  have : 0 < puv.length := by simp [not_nil_iff_lt_length.1, *]
  have := puv.getVert_zero ▸ puv.adj_getVert_succ this
  simp [toSimpleGraph] at this; cases this
  · exact mem_support_of_parent ‹_›
  · exact mem_support_of_child ‹_›

def Descend {u v} (p : F.toSimpleGraph.Walk u v) := p.support.IsChain F.parent_child

def ancester_descendant : (WithBot V) → (WithBot V) → Prop :=
  fun u v ↦ ∃ p : F.toSimpleGraph.Walk u v, Descend p

open SimpleGraph Walk in
@[simp] lemma descend_nil {u v : WithBot V} {p : F.toSimpleGraph.Walk u v} (hp : p.Nil) :
  Descend p := by simp [Descend, List.isChain_iff_getElem, p.nil_iff_length_eq.1 hp]

open SimpleGraph Walk List in
@[simp] lemma descend_append {u v w : WithBot V} (p : F.toSimpleGraph.Walk u v)
  (q : F.toSimpleGraph.Walk v w) : Descend p → Descend q → Descend (p.append q) := by
    intro hp hq; simp [Descend] at hp hq;
    rw [←List.cons_head_tail (show q.support ≠ [] from by simp)] at hq
    simp [List.isChain_cons] at hq
    have : p.support.getLast (show p.support ≠ [] from by simp) = v := by simp
    simp [Descend, support_append, List.isChain_append, List.getLast?_eq_getLast, *]; exact hq.left

@[simp] lemma descend_copy {u v u' v' : WithBot V} {p : F.toSimpleGraph.Walk u v}
  {hu : u = u'} {hv : v = v'} : Descend (p.copy hu hv) → Descend p := by simp [Descend]

lemma descend_copy_iff {u v u' v' : WithBot V} (p : F.toSimpleGraph.Walk u v)
  (hu : u = u') (hv : v = v') : Descend p ↔ Descend (p.copy hu hv) := by simp [Descend]

@[simp] lemma descend_from_root {u} : u ∈ F.support →
  ∃ p : F.toSimpleGraph.Walk ⊥ u, Descend p := by
  have : ∀ u, (∀ v, F.parent_child v u → v ∈ F.support → ∃ p : F.toSimpleGraph.Walk ⊥ v, Descend p)
    → (u ∈ F.support → ∃ p : F.toSimpleGraph.Walk ⊥ u, Descend p) := by
    intro u h hu; by_cases hur : u = ⊥
    · use SimpleGraph.Walk.nil.copy hur rfl; simp [Descend]
    · obtain ⟨v, hvu⟩ := Or.resolve_left (root_or_has_parent_of_mem_support hu) hur
      specialize h v hvu (mem_support_of_parent hvu); obtain ⟨p, hp⟩ := h
      set q := (show F.toSimpleGraph.Adj v u from by simp [toSimpleGraph, *]).toWalk
      have : Descend q := (by simp [Descend, q, *]); use p.append q; simp [*]
  exact F.wellfounded.recursion u this

variable {F : RootedForest V κ} {u v : WithBot V} {p : F.toSimpleGraph.Walk u v} in
@[simp] lemma not_bot_of_descend (hp : Descend p) : ⊥ ∉ p.support.tail := by
  by_contra; obtain ⟨i, hi, hib⟩ := p.support.tail.mem_iff_getElem.1 ‹_›
  simp at hi hib; simp [Descend, List.isChain_iff_getElem] at hp; have := hib ▸ hp i hi; aesop

open SimpleGraph Walk List in
instance instPartialOrderWithBot : PartialOrder (WithBot V) where
  le := F.ancester_descendant
  le_refl _ := by simp [ancester_descendant]; use Walk.nil; simp [Descend]
  le_trans u v w huv hvw := by
    simp [ancester_descendant] at ⊢ huv hvw; obtain ⟨puv, hpuv⟩ := huv; obtain ⟨pvw, hpvw⟩ := hvw
    use puv.append pvw; exact F.descend_append puv pvw hpuv hpvw
  le_antisymm u v huv hvu := by
    simp [ancester_descendant] at huv hvu; obtain ⟨puv, hpuv⟩ := huv; obtain ⟨pvu, hpvu⟩ := hvu
    by_cases puv.Nil ∨ pvu.Nil
    · by_cases puv.Nil
      · exact eq_of_length_eq_zero <| nil_iff_length_eq.1 ‹_›
      · exact Eq.symm <| eq_of_length_eq_zero <| nil_iff_length_eq.1 <| Or.resolve_left ‹_› ‹_›
    · have := F.descend_append puv pvu hpuv hpvu
      have : ¬(puv.append pvu).Nil := by aesop
      set puu := puv.append pvu
      have : ¬ u = ⊥ := by
        have : puu.support.tail ≠ [] := by
          simp [ne_nil_iff_length_pos, Nat.pos_iff_ne_zero]
          exact not_imp_not.2 nil_iff_eq_nil.2 ‹_›
        exact Ne.symm <| not_imp_not.2 (fun h => @Set.mem_of_eq_of_mem _ (⊥ : WithBot V) _ _ h
          puu.getLast_support ▸ getLast_tail ‹_› ▸ getLast_mem ‹_›)
          (show ⊥ ∉ puu.support.tail from by simp [*])
      have : ∀ u, (∀ v, F.parent_child v u → v ≠ ⊥ → v ∈ F.support →
        (∃ p : F.toSimpleGraph.Walk v v, ¬p.Nil ∧ Descend p) → False) → (u ≠ ⊥ → u ∈ F.support →
        (∃ p : F.toSimpleGraph.Walk u u, ¬p.Nil ∧ Descend p) → False) := by
        intro u h hu hu' ⟨puu, hpuu', hpuu⟩; obtain ⟨pru', hpru'⟩ := descend_from_root hu'
        set pru : F.toSimpleGraph.Walk ⊥ u := pru'.copy rfl (by simp)
        have hpru : Descend pru := by simp [*, pru]
        have := not_bot_of_descend hpuu
        simp [Descend, *, List.isChain_iff_get] at hpru hpuu
        -- puu
        have := puu.not_nil_iff_lt_length.1 ‹_›
        have hv'u := hpuu (puu.length - 1) (by omega)
        conv at hv'u => arg 3; simp [(by omega : puu.length - 1 + 1 = puu.length),
          ←puu.getVert_eq_support_getElem (by omega : puu.length ≤ puu.length)]
        set v' := puu.support[puu.length - 1] with hv'
        have : v' ≠ u := by by_contra h; exact F.loopless u <| h ▸ hv'u
        have : v' ≠ ⊥ := by
          have : 1 < puu.length := by
            by_contra; have : 1 = puu.length := by omega
            simp [(by omega: puu.length - 1 = 0),
              ←puu.getVert_eq_support_getElem (by omega : 0 ≤ puu.length)] at hv'
            contradiction
          have := puu.support.getElem_tail
            (show puu.length - 2 < puu.support.tail.length from by simp [*])
          conv at this => arg 2; simp [(by omega : puu.length - 2 + 1 = puu.length - 1), ←hv']
          have := puu.support.tail.mem_of_getElem this
          by_contra h; have := h ▸ this; contradiction
        -- pru
        have := pru.not_nil_iff_lt_length.1 <| pru.not_nil_of_ne <| Ne.symm ‹_›
        have hvu := hpru (pru.length - 1) (by omega)
        conv at hvu => arg 3; simp [(by omega : pru.length - 1 + 1 = pru.length),
          ←pru.getVert_eq_support_getElem (by omega : pru.length ≤ pru.length)]
        set v := pru.support[pru.length - 1]; specialize h v hvu
        by_cases hvr : v = ⊥
        · have := isOrigin_of_has_root_parent (hvr ▸ hvu)
          simp [isOrigin_def] at this; have := this.2 v' ‹_›; contradiction
        · specialize h hvr (mem_support_of_parent hvu); by_cases v = v'
          · set pvv := ((show F.toSimpleGraph.Adj v u from by
              simp_all [toSimpleGraph]).toWalk.append (puu.take (puu.length - 1))).copy rfl
              (show puu.getVert (puu.length - 1) = v from by
                simp_all [puu.getVert_eq_support_getElem])
            have : ¬pvv.Nil := by simp_all [not_nil_iff_lt_length, pvv]
            have : Descend pvv := by
              simp [pvv, Descend, List.isChain_iff_getElem]; intro i hi
              set puv' := puu.take (puu.length - 1); match i with
              | 0 =>
                simp; rw[←puv'.getVert_eq_support_getElem
                  (show 0 ≤ puv'.length from by simp [puv'])]; simp; assumption
              | i' + 1 =>
                have h1 := puv'.getVert_eq_support_getElem
                  (show i' ≤ puv'.length from by simp [puv']; omega)
                simp [puv'] at h1
                conv at h1 => left; arg 2; rw[(by omega : min (puu.length - 1) i' = i')]
                have h2 := puv'.getVert_eq_support_getElem
                  (show i' + 1 ≤ puv'.length from by simp [puv']; omega)
                simp [puv'] at h2
                conv at h2 => left; arg 2; rw[(by omega : min (puu.length - 1) (i' + 1) = i' + 1)]
                have h3 := puu.getVert_eq_support_getElem (by omega : i' ≤ puu.length)
                have h4 := puu.getVert_eq_support_getElem (by omega : i' + 1 ≤ puu.length)
                simp; rw [←h1, ←h2, h3, h4]; exact hpuu i' (by omega)
            exact h ⟨pvv, ‹_›, ‹_›⟩
          · exact F.false_of_not_acyclic hvu hv'u ‹_›
      exact False.elim <| F.wellfounded.recursion u this ‹_›
        (mem_support_of_walk_start_not_nil puu ‹_›) ⟨puu, ‹_›, ‹_›⟩

scoped infix:50 " ≼ " => @ancester_descendant _ _ _
scoped infix:50 " ≽ " => fun u v => @ancester_descendant _ _ _ v u
scoped notation:50 a " ≼[" F:50 "] " b => @ancester_descendant _ _ (F : RootedForest _ ‹_›) a b
scoped notation:50 a " ≽[" F:50 "] " b => @ancester_descendant _ _ (F : RootedForest _ ‹_›) b a

@[simp] lemma toAncesterDescendant : Subrelation F.parent_child F.ancester_descendant := by
  simp [Subrelation, ancester_descendant]; intro u v _
  use (show F.toSimpleGraph.Adj u v from by simp [toSimpleGraph, *]).toWalk; simp [Descend, *]

@[simp] lemma parent_child_not_commu {u v} (huv : u ≺[F] v) : ¬v ≺[F] u := by
  by_contra hvu; have := F.instPartialOrderWithBot.le_antisymm u v (F.toAncesterDescendant huv)
    (F.toAncesterDescendant hvu); subst_vars; exact F.loopless v huv

end LE

section Acyclic
variable {V : Type*} {κ : WithBot V → Type*} (F : RootedForest V κ)

open SimpleGraph Walk in
@[simp] lemma _root_.SimpleGraph.Walk.take_of_length {G : SimpleGraph V} {u v} {p : G.Walk u v} :
  p.take p.length = p.copy rfl (by simp) := by induction p <;> simp [take, *]

open SimpleGraph Walk in
lemma isAcyclic : F.toSimpleGraph.IsAcyclic := by
  dsimp [IsAcyclic]; intros u c; by_contra hc; have h0 := hc.three_le_length
  have h₁ {u v} (p : F.toSimpleGraph.Walk u v) (hp : 0 < p.length) :
    (p.take 1).support = [p.support[0], p.support[1]'(by simp; omega)] := by
    apply List.ext_getElem
    · simp [*]; omega
    · intro i hi hi'; simp at hi'; by_cases i = 0
      · subst_vars; simp [take_support_eq_support_take_succ]
      · have : i = 1 := (by omega); subst_vars; simp [take_support_eq_support_take_succ]
  have h₀ {u} (c : F.toSimpleGraph.Walk u u) (hc : c.IsCycle)
    (hc' : u ≺[F] c.getVert 1) : False := by
    have h0 := hc.three_le_length
    have : ∃ i < c.length, Descend (c.take i) ∧ ¬ Descend (c.take (i + 1)) := by
      by_contra h; simp only [not_exists, not_and_or, not_not] at h
      have : ∀ i ≤ c.length, Descend (c.take i) := by
        intro i hi; induction i with
        | zero => simp [Descend, List.isChain_iff_getElem,
          (show (c.take 0).length = 0 from by simp)]
        | succ i' ih =>
          exact Or.resolve_left (Or.resolve_left (h i') (by omega)) (not_not.2 <| ih (by omega))
      have := this c.length (by omega); simp at this; have h1 := descend_copy this
      have : c.getVert 1 ≠ u := by
        obtain ⟨_, hc⟩ := hc; simp [List.Nodup, List.pairwise_iff_getElem] at hc
        have h2 := @c.getVert_eq_support_getElem _ _ _ _ 1 (by omega)
        have h3 := @c.getVert_eq_support_getElem _ _ _ _ (c.length) (by omega)
        have := hc 0 (c.length - 1) (by omega) (by omega) (by omega)
        conv at this => right; right; arg 2; rw [(by omega : c.length - 1 + 1 = c.length)]
        simp [←h2, ←h3] at this; exact this
      have : c.getVert 1 = u := by
        have : Descend (c.take 1) := by
          have : (c.take 1).support.length = 2 := by simp; omega
          have := h₁ c (by omega)
          simp [Descend, List.isChain_iff_getElem, this] at ⊢ h1
          intro i _; conv => arg 2; arg 2; rw[(by omega : i = 0)]
          specialize h1 0 (by omega); simpa
        have : u ≼[F] c.getVert 1 := by simp [ancester_descendant]; use (c.take 1)
        have : Descend (c.drop 1) := by
          simp [Descend, List.isChain_iff_getElem, drop_support_eq_support_drop_min] at ⊢ h1
          intro i hi; conv => arg 2; arg 2; simp [(by omega : min 1 c.length + i = i + 1)]
          conv => arg 3; arg 2; simp [(by omega : min 1 c.length + (i + 1) = i + 2)]
          exact h1 (i + 1) (by omega)
        have : c.getVert 1 ≼[F] u := by simp [ancester_descendant]; use (c.drop 1)
        exact F.instPartialOrderWithBot.le_antisymm (c.getVert 1) u ‹_› ‹_›
      contradiction
    obtain ⟨i, hi1, hi2, hi3⟩ := this
    have : i > 0 := by
      by_contra; have := (by omega : i = 0); subst_vars
      simp [Descend, List.isChain_iff_getElem, h₁ c (by omega)] at hi3
      obtain ⟨j, hj, hj'⟩ := hi3; have := (by omega : j = 0); subst_vars; simp at hj'
      simp [←@c.getVert_eq_support_getElem _ _ _ _ 0 (by omega),
        ←@c.getVert_eq_support_getElem _ _ _ _ 1 (by omega)] at hj'; contradiction
    simp [Descend, List.isChain_iff_getElem] at hi2 hi3
    obtain ⟨j, hj, hj', hj''⟩ := hi3
    simp [←@getVert_eq_support_getElem _ _ _ _ j (c.take (i + 1)) (by simp; omega),
      ←@getVert_eq_support_getElem _ _ _ _ (j + 1) (c.take (i + 1)) (by simp; omega),
      (by omega : min (i + 1) j = j), (by omega : min i j + 1 = j + 1)] at hj''
    have : j = i := by
      by_contra; have := (by omega : j < i); specialize hi2 j ‹_› ‹_›
      simp [←@getVert_eq_support_getElem _ _ _ _ j (c.take i) (by simp; omega),
        ←@getVert_eq_support_getElem _ _ _ _ (j + 1) (c.take i) (by simp; omega),
        (by omega : min i j = j), (by omega : min i (j + 1) = j + 1)] at hi2; contradiction
    subst j; specialize hi2 (i - 1) (by omega) (by omega)
    simp [←@getVert_eq_support_getElem _ _ _ _ (i - 1) (c.take i) (by simp; omega), (by omega :
      i - 1 + 1 = i), ←@getVert_eq_support_getElem _ _ _ _ i (c.take i) (by simp; omega)] at hi2
    have := @c.adj_getVert_succ _ _ _ _ i (by omega); simp [toSimpleGraph] at this
    have := F.acyclic hi2 <| Or.resolve_left this hj''
    obtain ⟨_, hc⟩ :=  hc; simp [List.Nodup, List.pairwise_iff_getElem] at hc
    by_cases h : i - 1 = 0
    · specialize hc i (c.length - 1) (by omega) (by omega) (by omega)
      simp only [(by omega : c.length - 1 + 1 = c.length), ←@getVert_eq_support_getElem _ _ _ _
        c.length c (by omega), getVert_length, ←c.getVert_zero, ←h, ←@getVert_eq_support_getElem
        _ _ _ _ (i + 1) c (by omega)] at hc; exact hc <| Eq.symm this
    · specialize hc (i - 2) i (by omega) (by omega) (by omega)
      simp [(by omega : i - 2 + 1 = i - 1), ←@getVert_eq_support_getElem _ _ _ _ (i - 1) c
        (by omega), ←@getVert_eq_support_getElem _ _ _ _ (i + 1) c (by omega), this] at hc
  by_cases hc' : u ≺[F] c.getVert 1
  · exact h₀ c hc hc'
  · set c' := ((c.drop 1).append (c.take 1)).reverse
    have : c'.length = c.length := by simp [c']; omega
    have : c'.getVert 0 = c.getVert 1 := by simp [c']
    have h9 : c'.getVert 1 = u := by simp [c', getVert_append, (by omega : 1 - min 1 c.length = 0)];
    have h₂ : ∀ i ≤ c'.length, i > 0 → c'.getVert i = c.getVert (c.length - i + 1) := by
      simp [c', getVert_append, (by omega : min 1 c.length + (c.length - 1) = c.length)]
      intro i hi hi'; split_ifs
      · omega
      · simp [getVert_reverse, (by omega : 1 + (c.length - 1 - (i - min 1 c.length))
          = c.length - i + 1)]
    have : c'.IsCycle := by
      simp [isCycle_def]
      constructor
      · simp [isCycle_def] at hc; obtain ⟨hc, _⟩ := hc
        simp only [c']; apply ((c.drop 1).append (c.take 1)).reverse_isTrail_iff.2
        simp [isTrail_def, List.Nodup, ] at ⊢ hc
        have h6 : (c.drop 1).edges = List.drop 1 c.edges := by
          match c with
          | nil => simp [drop]
          | cons h q => simp [drop, drop_zero]
        have h7 : (c.take 1).edges = List.take 1 c.edges := by
          match c with
          | nil => simp [take]
          | cons h q => simp [take]; cases q <;> simp [take]
        have h8 : (List.drop 1 c.edges) ++ (List.take 1 c.edges) = List.rotate c.edges 1 := by
          have : c.edges.length = c.length := by simp
          have := c.edges.rotate_eq_drop_append_take (by omega : 1 ≤ c.edges.length)
          exact Eq.symm this
        simp only [h6, h7, h8]; simp [List.pairwise_iff_getElem] at ⊢ hc; intro i j hi hj hij
        have : (c.edges.rotate 1).length = c.length := by simp
        simp [List.getElem_rotate c.edges 1 i (by omega),
          List.getElem_rotate c.edges 1 j (by omega)]
        by_cases hj' : j + 1 = c.length
        · specialize hc ((j + 1) % c.length) ((i + 1) % c.length)
            (by simp [@Nat.mod_lt (j + 1) c.length (by omega)])
            (by simp [@Nat.mod_lt (i + 1) c.length (by omega)])
            (by simp [hj', Nat.mod_eq_of_lt (by omega : i + 1 < c.length)])
          exact Ne.symm hc
        · specialize hc ((i + 1) % c.length) ((j + 1) % c.length)
            (by simp [@Nat.mod_lt (i + 1) c.length (by omega)])
            (by simp [@Nat.mod_lt (j + 1) c.length (by omega)])
            (by simpa [Nat.mod_eq_of_lt (by omega : i + 1 < c.length),
              Nat.mod_eq_of_lt (by omega : j + 1 < c.length)])
          exact hc
      · constructor
        · exact not_imp_not.2 c'.nil_iff_eq_nil.2 <| c'.not_nil_iff_lt_length.2 (by omega)
        · simp [isCycle_def] at hc; obtain ⟨_, _, hc⟩ := hc
          simp [List.Nodup, List.pairwise_iff_getElem] at ⊢ hc; intro i j hi hj hij
          simp [←@getVert_eq_support_getElem _ _ _ _ (i + 1) c' (by omega), h₂ (i + 1) (by omega),
            ←@getVert_eq_support_getElem _ _ _ _ (j + 1) c' (by omega), h₂ (j + 1) (by omega)]
          specialize hc (c.length - (j + 1)) (c.length - (i + 1)) (by omega) (by omega) (by omega)
          simp [←@getVert_eq_support_getElem _ _ _ _ (c.length - (i + 1) + 1) c (by omega),
            ←@getVert_eq_support_getElem _ _ _ _ (c.length - (j + 1) + 1) c (by omega)] at hc
          exact Ne.symm hc
    have : c.getVert 1 ≺[F] c'.getVert 1 := by
      have : c.getVert 1 ≺[F] u := by
        have := c.adj_getVert_succ (by omega : 0 < c.length); simp [toSimpleGraph] at this; aesop
      exact Eq.symm h9 ▸ this
    exact h₀ c' ‹_› ‹_›

end Acyclic

class Standard (β : List ℕ → ℕ)
  extends RootedForest (List ℕ) (fun v => Fin (β <| match v with | ⊥ => [] | some v => v)) where
  nil_eq_root : (⊥ : WithBot (List ℕ)) = some []
  branch_def : ∀ v i, branch v i = match v with
    | ⊥ => [(i : ℕ)]
    | some v => (i : ℕ) :: v

variable (β : List ℕ → ℕ) in
instance : FunLike (Standard β) (List ℕ) ℕ where
  coe _ := β
  coe_injective' β1 β2 h := by cases β1; cases β2; congr; aesop

end RootedForest

section GW
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

structure ListNProcess (Ω : Type*) [mΩ : MeasurableSpace Ω] (E : Type*) where
  toFun : List ℕ → Ω → E

namespace ListNProcess
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {E : Type*}

instance instFunLike : FunLike (ListNProcess Ω E) (List ℕ) (Ω → E) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

@[simp] def sizeAfterLayer (L : ListNProcess Ω ℕ) (x : List ℕ) (ω : Ω) (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 =>
    let M := sizeAfterLayer L x ω n
    ∑ (f : Fin n → Fin (M + 1)),
      let seq := List.ofFn fun i => (f i).val;
      if seq.sum < M then L (seq ++ x) ω else 0

variable (L : ListNProcess Ω ℕ) (x : List ℕ) (ω : Ω) (n : ℕ)

@[simp] lemma sizeAfterLayer_zero : sizeAfterLayer L x ω 0 = 1 := by simp

@[simp] lemma sizeAfterLayer_one : sizeAfterLayer L x ω 1 = L x ω := by simp

@[simp] def sizeBefore (L : ListNProcess Ω ℕ) (x : List ℕ) (ω : Ω) : ℕ :=
  match x with
  | [] => 0
  | m :: x' => m + ∑ n : Fin x'.length, ∑ n' : Fin (x'.get n),
      sizeAfterLayer L (n' :: (x'.drop (x'.length - n))) ω (x'.length - n + 1)

end ListNProcess

variable (ℙ : MeasureTheory.Measure Ω) (p : PMF ℕ) -- by volume_tac?

class GaltonWatsonListN where
  toProcess : ListNProcess Ω ℕ
  toField (ω : Ω) := RootedForest.Standard (fun x ↦ toProcess x ω)
  indep : ProbabilityTheory.iIndepFun (fun v ↦ toProcess v) ℙ
  sameLaw : ∀ v, ℙ.map (toProcess v) = p.toMeasure ∨ ℙ.map (toProcess v) = 0

class GaltonWatson (V : Type*) extends GaltonWatsonListN ℙ p where
  labelling : Ω → List ℕ → WithBot V
  labelling_inj : ∀ ω, Function.Injective <| labelling ω

class GaltonWatsonNN extends GaltonWatson ℙ p (ℕ × ℕ) where
  labelling_def : labelling = fun ω x => match x with
    | [] => ⊥
    | m :: x' => (x'.length, ListNProcess.sizeBefore toProcess (m :: x') ω)

namespace GaltonWatson

variable {p : PMF ℕ} {ℙ : MeasureTheory.Measure Ω} (GW : GaltonWatson ℙ p V)

def generationSize : ℕ → Ω → ℕ := fun n ω => GW.toProcess.sizeAfterLayer [] ω n

end GaltonWatson
end GW

section ProbabilityGeneratingFunction

end ProbabilityGeneratingFunction
