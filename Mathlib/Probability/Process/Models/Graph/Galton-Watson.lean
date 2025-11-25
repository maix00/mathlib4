import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
-- import Mathlib.Topology.Instances.ENat

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

@[simp] instance : Membership (WithBot V) (RootedForest V κ) where
  mem RF v := v ∈ RF.support

lemma root_or_has_parent_of_mem_support {u} : u ∈ F → u = ⊥ ∨ ∃ v, v ≺[F] u := by
  intro ⟨v, huv⟩; simp [toSimpleGraph] at huv; by_cases u = ⊥
  · left; assumption
  · right; by_cases hu : F.IsOrigin u
    · use ⊥; simp [*]
    · simp only [isOrigin_def, not_and_or] at hu; cases hu <;> aesop

lemma mem_support_of_parent {u v} (_ : u ≺[F] v) : u ∈ F := by
  simp_all [support, toSimpleGraph, SimpleGraph.support]; use v; left; assumption

lemma mem_support_of_child {u v} (_ : u ≺[F] v) : v ∈ F := by
  simp_all [support, toSimpleGraph, SimpleGraph.support]; use u; right; assumption

open SimpleGraph Walk in
private lemma mem_support_of_walk_start_not_nil {u v : WithBot V} (puv : F.toSimpleGraph.Walk u v)
  (hpuv : ¬puv.Nil) : u ∈ F := by
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

@[simp] lemma descend_from_root {u} : u ∈ F →
  ∃ p : F.toSimpleGraph.Walk ⊥ u, Descend p := by
  have : ∀ u, (∀ v, F.parent_child v u → v ∈ F → ∃ p : F.toSimpleGraph.Walk ⊥ v, Descend p)
    → (u ∈ F → ∃ p : F.toSimpleGraph.Walk ⊥ u, Descend p) := by
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
      have : ∀ u, (∀ v, F.parent_child v u → v ≠ ⊥ → v ∈ F →
        (∃ p : F.toSimpleGraph.Walk v v, ¬p.Nil ∧ Descend p) → False) → (u ≠ ⊥ → u ∈ F →
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

end RootedForest

@[reducible] def TreeNode := List ℕ

inductive generateRootedLabeledTree (s : Set TreeNode) : Set TreeNode
  | mem : (l : TreeNode) → s l → generateRootedLabeledTree s l
  | tail : (m : ℕ) → (l : TreeNode) → generateRootedLabeledTree s (m :: l)
    → generateRootedLabeledTree s l
  | less : (m : ℕ) → (l : TreeNode) → generateRootedLabeledTree s (m :: l) → (n : ℕ) → n ≤ m
    → generateRootedLabeledTree s (n :: l)

def RootedLabeledTree := {s // generateRootedLabeledTree s = s ∧ s ≠ ∅}

namespace RootedLabeledTree

instance : Coe TreeNode (List ℕ) where
  coe l := l

instance : Coe RootedLabeledTree (Set TreeNode) where
  coe T := T.val

instance instMembershipTreeNode : Membership TreeNode RootedLabeledTree where
  mem T l := l ∈ T.val

instance : HasSubset RootedLabeledTree where
  Subset T1 T2 := T1.val ⊆ T2.val

@[simp] lemma nil_generate : generateRootedLabeledTree ∅ = ∅ := by
  ext l; simp only [Set.mem_empty_iff_false, iff_false]; by_contra hl
  induction hl with
  | mem _ ih => exact ih
  | tail _ _ _ ih => exact ih
  | less _ _ _ _ _ ih => exact ih

@[simp] lemma generateRootedLabeledTree_eq_self_of_val (T : RootedLabeledTree) :
  generateRootedLabeledTree T.val = T.val := T.property.1

@[simp] lemma nonempty_of_val (T : RootedLabeledTree) : T.val ≠ ∅ := T.property.2

lemma generate_subset_generate_of_subset (s1 s2 : Set TreeNode) (h : s1 ⊆ s2) :
  generateRootedLabeledTree s1 ⊆ generateRootedLabeledTree s2 := by
  unfold Subset Set.instHasSubset LE.le Set.instLE Set.Subset; simp; intro l hl; induction hl with
  | mem l' hl' =>
    have := Set.mem_of_subset_of_mem h hl'
    simp [Membership.mem, Set.Mem] at this ⊢
    exact generateRootedLabeledTree.mem l' this
  | tail m l' hl' ih =>
    simp [Membership.mem, Set.Mem]
    exact generateRootedLabeledTree.tail m l' ih
  | less m l' hl' n hnm ih =>
    simp [Membership.mem, Set.Mem]
    exact generateRootedLabeledTree.less m l' ih n hnm

lemma subset_generate (s : Set TreeNode) : s ⊆ generateRootedLabeledTree s := by
  unfold Subset Set.instHasSubset LE.le Set.instLE Set.Subset; simp; intro l hl
  simp [Membership.mem, Set.Mem] at hl ⊢
  exact generateRootedLabeledTree.mem l hl

lemma generate_generate (s : Set TreeNode) :
  generateRootedLabeledTree (generateRootedLabeledTree s) = generateRootedLabeledTree s := by
  ext l; constructor
  · intro hl; induction hl with
      | mem => simp [Membership.mem, Set.Mem, *]
      | tail m l' hl' ih => exact generateRootedLabeledTree.tail m l' ih
      | less m l' hl' n hnm ih => exact generateRootedLabeledTree.less m l' ih n hnm
  · intro hl; exact generateRootedLabeledTree.mem l hl

lemma nonempty_of_nonempty (s : Set TreeNode) (hs : s ≠ ∅) : generateRootedLabeledTree s ≠ ∅ := by
  obtain ⟨l, hl⟩ := not_not.1 <| not_imp_not.2 Set.not_nonempty_iff_eq_empty.1 hs
  apply not_imp_not.2 (@Set.not_nonempty_iff_eq_empty _ (generateRootedLabeledTree s)).2
  simp only [not_not]; simp [Membership.mem, Set.Mem] at hl
  exact ⟨l, generateRootedLabeledTree.mem l hl⟩

def generate (s : Set TreeNode) (hs : s ≠ ∅) : RootedLabeledTree :=
  ⟨generateRootedLabeledTree s, generate_generate s, nonempty_of_nonempty s hs⟩

@[simp] lemma self_eq_generate_val (T : RootedLabeledTree) :
  generate T.val T.nonempty_of_val = T := by simp [generate]

@[simp] lemma nil_mem {T : RootedLabeledTree} : [] ∈ T := by
  obtain ⟨h1, h2⟩ := T.property; obtain ⟨l, hl⟩ := Set.nonempty_iff_ne_empty.2 h2
  induction l with
  | nil => exact hl
  | cons m l' ih =>
    rw [←h1] at hl ih; simp [Membership.mem, Set.Mem] at hl ih ⊢
    have := h1 ▸ generateRootedLabeledTree.tail m l' (h1 ▸ hl); exact ih this

@[simp] lemma tail_mem {T : RootedLabeledTree} {m : ℕ} {l : TreeNode} {h : m :: l ∈ T} : l ∈ T := by
  obtain ⟨h1, h2⟩ := T.property; simp [Membership.mem, Set.Mem] at ⊢ h; rw [←h1] at ⊢ h
  exact generateRootedLabeledTree.tail m l h

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
  exact generateRootedLabeledTree.less m l h n hnm

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
    exact generateRootedLabeledTree.less n l hn m (by omega)

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
      exact generateRootedLabeledTree.less (n - 1) l this m (by omega)

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

def descendantTreeAt {T : RootedLabeledTree} (x : TreeNode) (hx : x ∈ T) : RootedLabeledTree := ⟨
  {x' | x' ++ x ∈ T}, by
    obtain ⟨h1, h2⟩ := T.property
    ext l; constructor
    · intro hl; simp
      induction hl with
      | mem => simp_all [Membership.mem, Set.Mem, setOf]
      | tail m l' hl' ih =>
        simp [Membership.mem, Set.Mem] at ⊢ ih; rw [←h1] at ⊢ ih
        exact generateRootedLabeledTree.tail m (l' ++ x) ih
      | less m l' hl' n hnm ih =>
        simp [Membership.mem, Set.Mem] at ⊢ ih; rw [←h1] at ⊢ ih
        exact generateRootedLabeledTree.less m (l' ++ x) ih n hnm
    · intro hl; exact generateRootedLabeledTree.mem l hl
    , by
      apply not_imp_not.2 Set.not_nonempty_iff_eq_empty.2; simp only [not_not]
      exact ⟨[], by simp [*]⟩
  ⟩

noncomputable def height (T : RootedLabeledTree) : ℕ∞ :=
  (⨆ (x : TreeNode) (_ : x ∈ T), x.length : WithTop ℕ)

@[simp] lemma mem_length_at_most_height {T : RootedLabeledTree} : ∀ v ∈ T, v.length ≤ T.height := by
  simp [height]; exact @le_iSup₂ _ _ _ _ (fun v => fun (_ : v ∈ T) => (v.length : WithTop ℕ))

def truncation (T : RootedLabeledTree) (n : ℕ) : RootedLabeledTree := ⟨
  {x | x.length ≤ n ∧ x ∈ T},  by
    obtain ⟨h1, h2⟩ := T.property; ext l; constructor
    · intro hl; simp
      induction hl with
      | mem l' ih=> simp [setOf] at ih; exact ih
      | tail m l' hl' ih =>
        simp [Membership.mem, Set.Mem] at ⊢ ih; rw [←h1] at ⊢ ih
        exact ⟨by omega, generateRootedLabeledTree.tail m l' ih.2⟩
      | less m l' hl' n hnm ih =>
        simp [Membership.mem, Set.Mem] at ⊢ ih; rw [←h1] at ⊢ ih
        exact ⟨by omega, generateRootedLabeledTree.less m l' ih.2 n hnm⟩
    · intro hl; exact generateRootedLabeledTree.mem l hl
    , by
      apply not_imp_not.2 Set.not_nonempty_iff_eq_empty.2; simp only [not_not]
      exact ⟨[], by simp [*]⟩
  ⟩

def nilRootedLabeledTree := generate {[]} (by simp)

@[simp] lemma nilRootedLabeledTree_aux : generateRootedLabeledTree {[]} = {[]} := by
  ext l; constructor
  · intro hl; simp [Membership.mem, Set.Mem] at hl
    induction hl with
    | mem l' hl'=>
      have : l' ∈ ({[]} : Set TreeNode) := by simp [Membership.mem, Set.Mem, *]
      simp [Set.mem_singleton_iff.1 this]
    | tail => contradiction
    | less => contradiction
  · intro hl; simp at hl; simp [Membership.mem, Set.Mem, hl]
    exact generateRootedLabeledTree.mem [] (by
      have : ([] : TreeNode) ∈ ({[]} : Set TreeNode) := by simp
      simp [Membership.mem, Set.Mem] at this; exact this)

@[simp] lemma nilRootedLabeledTree_eq : nilRootedLabeledTree = ⟨({[]} : Set TreeNode),
  nilRootedLabeledTree_aux, by simp⟩  := by simp [nilRootedLabeledTree, generate]

@[simp] lemma truncation_zero {T : RootedLabeledTree} : T.truncation 0 = nilRootedLabeledTree := by
  rw [nilRootedLabeledTree_eq, truncation]; apply Subtype.eq
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

noncomputable instance : MetricSpace RootedLabeledTree where
  dist := treeDist
  dist_self := by simp [treeDist]
  dist_comm := by simp [treeDist]
  dist_triangle T1 T2 T3 := le_trans (treeDist_ultra T1 T2 T3) <| max_le_add_of_nonneg (by
    simp [treeDist]) (by simp [treeDist])
  eq_of_dist_eq_zero := ext_of_zero_treeDist

instance : IsUltrametricDist RootedLabeledTree where
  dist_triangle_max := treeDist_ultra

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
      · exact generateRootedLabeledTree.mem l
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

private lemma generate_eq_generate_tail_then_less (s : Set TreeNode) (hs : s ≠ ∅) :
  generateRootedLabeledTree s = {[]} ∪ generate_less (generate_tail s \ {[]}) (by simp) := by
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
    · have := hl'1 ▸ @nil_mem (generate s hs); simp only [generate, instMembershipTreeNode] at this
      exact this
    · simp [hl'1, generate_less] at hl; obtain ⟨l', ⟨hl'2, hl'3⟩, hl'4⟩ := hl
      simp [generate_tail] at hl'2; obtain ⟨l'', hl'2, hl'5⟩ := hl'2
      simp [generate_tail_of_single] at hl'5; obtain ⟨⟨n, hn⟩, hl'5⟩ := hl'5; simp only at hl'5
      simp [generate_less_of_single] at hl'4; obtain ⟨⟨m, hm⟩, hl'4⟩ := hl'4; simp only at hl'4
      simp only [Membership.mem, Set.Mem] at hl'2
      have := List.cons_head_tail hl'3 ▸ hl'5 ▸
        @drop_mem (generate s hs) l'' (generateRootedLabeledTree.mem l'' hl'2) n
      exact hl'4 ▸ @less_mem (generate s hs) (l'.head hl'3) m l'.tail this (by omega)

@[simp] lemma finite_of_generateRootedLabeledTree_finite {s : Set TreeNode} (hs : s.Finite) :
  Set.Finite (generateRootedLabeledTree s) := by
  by_cases s = ∅
  · simp [nil_generate, *]
  · simp only [generate_eq_generate_tail_then_less s ‹_›, Set.singleton_union, Set.finite_insert]
    exact finite_generate_less _ (by aesop)
      <| @Finite.Set.finite_diff _ _ {[]} <| finite_generate_tail_of_finite s hs

@[simp] lemma finite_of_generate_finite {s : Set TreeNode} (hs : s ≠ ∅) (hs' : s.Finite) :
  Set.Finite (generate s hs).val := by
  simp [generate, finite_of_generateRootedLabeledTree_finite hs']

@[simp] lemma finite_truncation_of_finite {T : RootedLabeledTree} (hT : Set.Finite T.val) (n : ℕ) :
  Set.Finite (T.truncation n).val := by
  have := @truncation_subset T n; simp only [instHasSubset] at this
  have : (T.val \ (T.val \ (T.truncation n).val)) = (T.truncation n).val := by simp [*]
  exact this ▸ @Finite.Set.finite_diff _ T.val (T.val \ (T.truncation n).val) hT

end RootedLabeledTree

namespace Set

variable {T : Type*} (seq : ℕ → Set T)

def seqDiff : ℕ → Set T := fun m =>
  Set.Accumulate seq m \ (if m = 0 then ∅ else Set.Accumulate seq (m - 1))

lemma iUnion₂_le_succ (m : ℕ) :
  ⋃ n ≤ m + 1, seq n = (⋃ n ≤ m, seq n) ∪ seq (m + 1) := by
      ext x; simp only [Set.mem_iUnion, exists_prop, Set.mem_union]; constructor
      · intro ⟨n, hn, hn'⟩; by_cases h' : n = m + 1
        · right; exact h' ▸ hn'
        · left; use n; exact ⟨by omega, hn'⟩
      · intro h; rcases h with (⟨n, hn, hn'⟩|_)
        · use n; exact ⟨by omega, hn'⟩
        · use m + 1

@[simp] lemma accumulate_eq_seqDiff_acculumate :
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

lemma eq_accumulate_self_of_mono (hseq : Monotone seq) : Set.Accumulate seq = seq := by
  ext m x; simp [Set.Accumulate]; constructor
  · intro ⟨n, hn, hn'⟩; exact Set.mem_of_subset_of_mem (hseq hn) hn'
  · intro; use m

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
  rw [←congr (Set.eq_accumulate_self_of_mono seq hseq) (@rfl _ i),
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

def setOfLength (n : ℕ) : Set TreeNode := {ν | ν.length = n}

def setOfLengthAtMost (n : ℕ) : Set TreeNode := {ν | ν.length ≤ n}

instance instCountableSetTreeNodeOfLength (n : ℕ) :
  Countable (setOfLength n) := by
  simp [setOfLength]; exact Subtype.countable

instance instCountableSetTreeNodeOfLengthAtMost (n : ℕ) :
  Countable (setOfLengthAtMost n) := by
  simp [setOfLengthAtMost]; exact Subtype.countable

lemma setOfLengthAtMost_eq_iUnion_finset_setOfLength (n : ℕ) :
  setOfLengthAtMost n = ⋃ k : Finset.range (n + 1), setOfLength k := by
  simp [setOfLengthAtMost, setOfLength]; ext v; simp; omega

def setOfLengthOfValAtMost (n m : ℕ) : Set TreeNode :=
  ⋃ f : Fin n → Fin (m + 1), {(List.ofFn f).map Fin.val}

@[simp] lemma setOfLengthOfValAtMost_zero : setOfLengthOfValAtMost 0 = fun _ => {[]} := by
  ext; simp [setOfLengthOfValAtMost]

@[simp] lemma setOfLengthOfValAtMost_zero_seqDiff :
  Set.seqDiff (setOfLengthOfValAtMost 0) = fun m => if m = 0 then {[]} else ∅ := by
  simp; unfold Set.seqDiff; simp [Set.Accumulate]; ext m v; by_cases h : m = 0
  · simp [h]
  · conv => left; congr; arg 2; simp [h]
    conv => right; congr; simp [h]
    have (m : ℕ) : ⋃ y, ⋃ (_ : y ≤ m), {([] : List ℕ)} = {[]} := by ext; simp; intro; use 0; omega
    rw [this m, this (m - 1)]; simp

instance instFiniteSetTreeNodeOfLengthTruncated (n m : ℕ) :
  Set.Finite (setOfLengthOfValAtMost n m) := by
  simp only [setOfLengthOfValAtMost]; apply Finite.Set.finite_iUnion

noncomputable instance instFintypeSetTreeNodeOfLengthTruncated (n m : ℕ) :
  Fintype (setOfLengthOfValAtMost n m) :=
  Set.Finite.fintype <| instFiniteSetTreeNodeOfLengthTruncated n m

@[simp] lemma setOfLengthOfValAtMost_subset_setOfLength (n m : ℕ) :
  setOfLengthOfValAtMost n m ⊆ setOfLength n := by
  simp [Set.subset_def, setOfLengthOfValAtMost, setOfLength]

@[simp] lemma setOfLengthOfValAtMost_mono (n : ℕ) :
  Monotone (setOfLengthOfValAtMost n) := by
  intro m1 m2 h12; simp [Set.subset_def, setOfLengthOfValAtMost]; intro f
  use Fin.castLE (show m1 + 1 ≤ m2 + 1 from by omega) ∘ f; ext; simp

@[simp] lemma setOfLengthOfValAtMost_union_eq_setOfLength (n : ℕ) :
  ⋃ m : ℕ, setOfLengthOfValAtMost n m = setOfLength n := by
  ext v; simp only [Set.mem_iUnion]; constructor
  · intro ⟨m, h⟩; exact Set.mem_of_subset_of_mem (by simp) h
  · intro h; by_cases h' : n = 0
    · simp [setOfLength] at h
      have : v = [] := List.eq_nil_iff_length_eq_zero.2 <| h' ▸ h
      use 0; simp [setOfLengthOfValAtMost, *]
    · simp only [setOfLength, Set.mem_setOf_eq] at h
      set m := v.max? with hm
      have : ∃ m', m = some m' := by
        match v with
        | [] => absurd h; simp; exact Ne.symm h'
        | n' :: v' => simp only [List.max?_cons] at hm; simp only [hm, Option.some.injEq,
          exists_eq']
      obtain ⟨m', hm'⟩ := this; use m'; simp [setOfLengthOfValAtMost]
      use fun ⟨i, hi⟩ => ⟨v[i], by
        have := List.le_max?_get_of_mem (show v[i] ∈ v from by simp)
        conv at this => right; congr; simp [←(hm' ▸ hm)]
        simp at this; omega⟩; simp only; conv => congr; congr; ext i; simp
      ext; aesop

instance instFiniteSetTreeNodeOfLengthTruncatedSeqDiff (n m : ℕ) :
  Set.Finite (Set.seqDiff (setOfLengthOfValAtMost n) m) := by
  apply Set.seqDiff_finite_of_finite; exact TreeNode.instFiniteSetTreeNodeOfLengthTruncated n

noncomputable instance instFintypeSetTreeNodeOfLengthTruncatedSeqDiff (n m : ℕ) :
  Fintype (Set.seqDiff (setOfLengthOfValAtMost n) m) :=
  Set.Finite.fintype <| instFiniteSetTreeNodeOfLengthTruncatedSeqDiff n m

variable {α : Type*}

noncomputable def tsumOfLevel [AddCommMonoid α] [TopologicalSpace α] (f : TreeNode → α) (n : ℕ) : α
  := ∑' (ν : setOfLength n), f ν

lemma tsumOfLevel_eq_tsum_sum' [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α] [T3Space α]
  (f : TreeNode → α) (n : ℕ)
  (hf1 : ∀ m, Summable fun c =>
    (fun v : @Sigma ℕ (fun m => Set.seqDiff (setOfLengthOfValAtMost n) m) => f v.snd) ⟨m, c⟩)
  (hf2 : Summable fun v : @Sigma ℕ (fun m => Set.seqDiff (setOfLengthOfValAtMost n) m) => f v.snd) :
  tsumOfLevel f n = ∑' m : ℕ, ∑ ν : Set.seqDiff (setOfLengthOfValAtMost n) m, f ν := by
  set seqDiff := Set.seqDiff <| setOfLengthOfValAtMost n with hseqDiff
  have h0 (m : ℕ) : ∑' v : seqDiff m, f v = ∑ v : seqDiff m, f v := by rw [tsum_eq_sum]; simp
  have h1 := @Summable.tsum_sigma' α ℕ _ _ _ _ (fun m => Set.Elem <| seqDiff m) (fun x => f x.2)
    hf1 hf2; simp at h1
  have h2 := TreeNode.setOfLengthOfValAtMost_union_eq_setOfLength n
  rw [←Set.iUnion_accumulate, Set.accumulate_eq_seqDiff_acculumate, ←hseqDiff,
    Set.iUnion_accumulate, Set.iUnion_eq_range_sigma] at h2
  have h3 := @tsum_range α TreeNode (@Sigma ℕ fun b ↦ ↑(seqDiff b))
    _ _ (fun a => ↑a.snd) (fun v => f v) (by simp [seqDiff]); simp at h3
  have := h1 ▸ h2 ▸ h3; conv at this => right; congr; ext m; rw [h0 m]
  exact this

lemma tsumOfLevel_eq_tsum_sum [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
  [CompleteSpace α] [T0Space α] (f : TreeNode → α) (n : ℕ)
  (hf : Summable fun v : @Sigma ℕ (fun m => Set.seqDiff (setOfLengthOfValAtMost n) m) => f v.snd) :
  tsumOfLevel f n = ∑' m : ℕ, ∑ ν : Set.seqDiff (setOfLengthOfValAtMost n) m, f ν := by
  set seqDiff := Set.seqDiff <| setOfLengthOfValAtMost n with hseqDiff
  have h0 (m : ℕ) : ∑' v : seqDiff m, f v = ∑ v : seqDiff m, f v := by rw [tsum_eq_sum]; simp
  have h1 := @Summable.tsum_sigma α ℕ _ _ _ _ _ (fun m => Set.Elem <| seqDiff m) (fun x => f x.2)
    hf; simp at h1
  have h2 := TreeNode.setOfLengthOfValAtMost_union_eq_setOfLength n
  rw [←Set.iUnion_accumulate, Set.accumulate_eq_seqDiff_acculumate, ←hseqDiff,
    Set.iUnion_accumulate, Set.iUnion_eq_range_sigma] at h2
  have h3 := @tsum_range α TreeNode (@Sigma ℕ fun b ↦ ↑(seqDiff b))
    _ _ (fun a => ↑a.snd) (fun v => f v) (by simp [seqDiff]); simp at h3
  have := h1 ▸ h2 ▸ h3; conv at this => right; congr; ext m; rw [h0 m]
  exact this

end TreeNode

namespace RootedLabeledTree

open TreeNode

variable (T : RootedLabeledTree)

@[simp] def setOfLevelAtMost (n : ℕ) : Set TreeNode := (T.truncation n).val

instance instMonotoneSetOfLevelAtMost : Monotone T.setOfLevelAtMost := by
  intro m n hmn; by_cases h : m = n
  · subst m; simp
  · exact @mem_higher_truncation_of_mem_truncation T m n (by omega)

def setOfLevel (n : ℕ) : Set TreeNode :=
  (T.truncation n).val \ if n = 0 then ∅ else (T.truncation (n - 1)).val

lemma setOfLevel_def (T : RootedLabeledTree) :
  T.setOfLevel = Set.seqDiff T.setOfLevelAtMost := by
  ext n v; by_cases h : n = 0
  · simp [setOfLevel, Set.seqDiff, h]
  · simp only [Set.seqDiff, setOfLevel, h, setOfLevelAtMost,
      Set.eq_accumulate_self_of_mono T.setOfLevelAtMost T.instMonotoneSetOfLevelAtMost]

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

@[simp] lemma setOfLevel_subset_setOfLength {n : ℕ} : T.setOfLevel n ⊆ setOfLength n := by
  simp [setOfLength, Set.subset_def]; exact RootedLabeledTree.setOfLevel_same_length

noncomputable def generationSizeAtLevel' (T : RootedLabeledTree) :=
  tsumOfLevel (ENat.toENNReal ∘ T.countChildren)

lemma generationSizeAtLevel'_eq_tsum_sum (T : RootedLabeledTree) (n : ℕ) :
  T.generationSizeAtLevel' n
  = ∑' m, ∑ ν : Set.seqDiff (setOfLengthOfValAtMost n) m, ↑(T.countChildren ↑ν)
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

def IsLocallyFinite (T : RootedLabeledTree) := ∀ n, Set.Finite (T.truncation n).val

def LocallyFinite := {T : RootedLabeledTree // T.IsLocallyFinite}

lemma isLocallyFinite_of_truncation (hT : T.IsLocallyFinite) (n : ℕ) :
  IsLocallyFinite (T.truncation n) := by simp [IsLocallyFinite] at ⊢ hT; intro m; exact hT (min n m)

def LocallyFinite.generateFinite (s : Set TreeNode) (hs : s ≠ ∅) (hs' : s.Finite) : LocallyFinite :=
  ⟨generate s hs, by
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
      · exact generateRootedLabeledTree.mem l
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
      simp only [generateFinite, ne_eq, Set.coe_toFinset, self_eq_generate_val,
        truncation_truncation, min_self, embed]

instance : MeasurableSpace LocallyFinite := borel LocallyFinite

instance : Coe LocallyFinite RootedLabeledTree where
  coe T := T.val

@[simp] lemma countChildren_finite (T : LocallyFinite) (ν : TreeNode) :
  countChildren ↑T ν ≠ ⊤ := by
  simp [←countChildren_eq_top_iff]
  set S := T.val.truncation (ν.length + 1) with hS
  have hT := (@Nat.card_eq_fintype_card _
    <| hS ▸ (@Fintype.ofFinite _ <| T.property (ν.length + 1)))
    ▸ hS ▸ (@Finite.equivFin _ <| T.property (ν.length + 1))
  set n := @Fintype.card _ <| hS ▸ (@Fintype.ofFinite _ <| T.property (ν.length + 1)) with hn
  use n; by_contra h; have h := hS ▸ @mem_truncation_of_mem _ (ν.length + 1) _ (by simp) h
  let F (m : Fin (n + 1)) : S.val.Elem := ⟨m :: ν, @less_mem S n _ ν h (by omega)⟩
  have := Fintype.card_le_of_injective F (by simp [Function.Injective, F]; omega); simp [hn] at this

noncomputable def countChildren (T : LocallyFinite) (ν : TreeNode) : ℕ :=
  (RootedLabeledTree.countChildren ↑T ν).toNat

@[ext] def ext_of_countChildren (T1 T2 : LocallyFinite)
  (h : ∀ l, T1.countChildren l = T2.countChildren l) : T1 = T2 :=
  Subtype.coe_inj.1 <| RootedLabeledTree.ext_of_countChildren _ _ (by
    intro l; specialize h l; simp [countChildren] at h
    exact @ENat.coe_toNat (T1.val.countChildren l) (by simp)
      ▸ h ▸ @ENat.coe_toNat (T2.val.countChildren l) (by simp))

@[simp] lemma countChildren_eq_zero_of_not_mem (T : LocallyFinite) (v : TreeNode) (hv : v ∉ T) :
  T.countChildren v = 0 := by
  simp [countChildren, RootedLabeledTree.countChildren]; left
  have {m : ENat} (hm : m ≤ 0) : m = 0 := by simp only [nonpos_iff_eq_zero] at hm; exact hm
  apply this; apply (@iSup₂_le_iff (WithTop ℕ) ℕ (fun m => m :: v ∈ T) _).2; intro m hm
  simp; exact hv <| @tail_mem _ _ _ hm

noncomputable instance : FunLike LocallyFinite TreeNode ℕ where
  coe T := T.countChildren
  coe_injective' T1 T2 h := by
    ext l; simp at h; have := congrArg (fun f => f l) h; simpa using this

@[simp] lemma setOfLevel_finite (T : LocallyFinite) (n : ℕ) :
  Set.Finite (T.val.setOfLevel n) := by
  simp [setOfLevel]; by_cases n = 0
  · simp [*]
  · simp [*]; apply Set.Finite.diff; exact T.property n

noncomputable instance (T : LocallyFinite) (n : ℕ) : Fintype ↑(T.val.setOfLevel n) :=
  @Fintype.ofFinite _ <| Set.finite_coe_iff.2 <| setOfLevel_finite T n

noncomputable def generationSizeAtLevel (T : LocallyFinite) :=
  tsumOfLevel T.countChildren

lemma generationSizeAtLevel_eq_tsum_sum (T : LocallyFinite) (n : ℕ) :
  T.generationSizeAtLevel n
  = ∑' m, ∑ ν : Set.seqDiff (setOfLengthOfValAtMost n) m, ↑(T.countChildren ↑ν)
  := tsumOfLevel_eq_tsum_sum' _ n (by sorry) (by
    by_cases h : n = 0
    · subst n; simp only [Summable, HasSum, SummationFilter.unconditional_filter, nhds_discrete,
      Filter.tendsto_pure, Filter.eventually_atTop, ge_iff_le, Finset.le_eq_subset]
      rw [setOfLengthOfValAtMost_zero_seqDiff]
      use T.countChildren [], {⟨0, [], by simp⟩}; intro s' hs
      set S := @Sigma ℕ fun m ↦ ↑((fun m ↦ if m = 0 then {[]} else (∅ : Set (List ℕ))) m) with hS
      simp at hS
      sorry
    · sorry
      -- simp [Summable, HasSum]
      -- use ∑ v : T.val.setOfLevel n, T.countChildren v
      -- set S := @Sigma ℕ fun m ↦ ↑(Set.seqDiff (setOfLengthOfValAtMost n) m)
      -- set s : Set S := ⋃ v : T.val.setOfLevel n, {⟨n, v.val, by sorry⟩}
      -- use
    )

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

section GW
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

variable (ℙ : MeasureTheory.Measure Ω) (L : PMF ℕ) in
class GaltonWatson where
  toField (ω : Ω) : RootedLabeledTree.LocallyFinite
  toProcess : TreeNode → Ω → ℕ
  toProcess_def : toProcess = fun ν ω => toField ω ν
  indep : ProbabilityTheory.iIndepFun (fun ν ↦ toProcess ν) ℙ
  -- `sameLaw` requires `toProcess ν` to be AEMeasurable
  sameLaw : ∀ ν, ℙ.map (toProcess ν) = L.toMeasure

variable {ℙ : MeasureTheory.Measure Ω} {L : PMF ℕ} (GW : GaltonWatson ℙ L)

noncomputable def measureGaltonWatson := ℙ.map GW.toField

namespace GaltonWatson

variable (ν : TreeNode)

open MeasureTheory Measure RootedLabeledTree LocallyFinite

@[simp] instance toProcess_aemeasurable : AEMeasurable (GW.toProcess ν) ℙ := by
  have := GW.sameLaw ν; simp [map] at this; split_ifs at this
  · assumption
  · exact False.elim <| Ne.symm (IsProbabilityMeasure.ne_zero L.toMeasure) this

@[simp] lemma toProcess_eq_countChildren :
  (fun ω => (GW.toField ω).countChildren ν) = GW.toProcess ν := by
  ext ω; simp [toProcess_def, RootedLabeledTree.LocallyFinite.instFunLikeTreeNodeNat]

noncomputable def processGenerationSize : ℕ → Ω → ℕ :=
  fun n ω => (GW.toField ω).generationSizeAtLevel n

lemma processGenerationSize_eq₁ : GW.processGenerationSize = fun n ω =>
  ∑' (ν : {ν : TreeNode // ν.length = n}), GW.toProcess ν ω := by
  unfold processGenerationSize; ext n ω
  -- have := tsum_fintype
  -- have := tsum_eq_finsum
  -- have := Finset.sum
  -- have := sum_eq_tsum_indicator
  -- have := Set.Finite.subtypeEquivToFinset
  -- have := Equiv.sum_comp
  -- have := summable_of_finite_support
  -- have := aemeasurable_of_tendsto_metrizable_ae
  -- have := aemeasurable_of_tendsto_metrizable_ae'

  sorry

@[simp] lemma processGenerationSize_zero : GW.processGenerationSize 0 = 1 := by
  unfold processGenerationSize; simp [generationSizeAtLevel]; rfl

@[simp] lemma processGenerationSize_one : GW.processGenerationSize 1 = GW.toProcess [] := by
  unfold processGenerationSize; simp [generationSizeAtLevel, setOfLevel]

#check List.aemeasurable_sum
#check List.aemeasurable_fun_sum
#check aemeasurable_of_tendsto_metrizable_ae
#check aemeasurable_of_tendsto_metrizable_ae'
#check ENNReal.aemeasurable_of_tendsto
#check ENNReal.aemeasurable_of_tendsto'

@[simp] instance processGenerationSize_aemeasurable (n : ℕ) : AEMeasurable (GW.processGenerationSize n) ℙ := by
  match n with
  | 0 => simp; exact aemeasurable_const
  | 1 => simp
  | n + 2 =>
    unfold processGenerationSize; simp [generationSizeAtLevel]
    exact @Finset.aemeasurable_fun_sum ℕ _ _ _ _ _ _ _ _ (by
      exact ((↑(GW.toField ℙ L ω)).setOfLevel (n + 1)).toFinset) (fun ν _ =>
      toProcess_eq_countChildren GW ν ▸ toProcess_aemeasurable GW ν)

end GaltonWatson

section ProbabilityGeneratingFunction

noncomputable def pgf (L : PMF ℕ) (s : ENNReal) : ENNReal := ∑' k, (L k) * s ^ k

lemma pgf_zero (L : PMF ℕ) : pgf L 0 = L 0 := by
  rw [pgf, ←@Summable.sum_add_tsum_nat_add' _ _ _ _ _ _ 1 ENNReal.summable]; simp

end ProbabilityGeneratingFunction

namespace GaltonWatson

def eventExtinction := { ω | ∃ n, GW.processGenerationSize n ω = 0 }

-- lemma eventExtinction_ofAEIsTree :
--   GW.eventExtinction = { ω | ∃ n, GW.toProcess.forestSize_atMostK_atLevel 0 n ω = 0 } := sorry

def eventExtinction_measurable : MeasurableSet (GW.eventExtinction) := by

  sorry

end GaltonWatson
end GW
