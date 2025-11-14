import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

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

scoped infix:50 " < " => @parent_child _ _ _
scoped notation:50 a " <[" F:50 "] " b => @parent_child _ _ (F : RootedForest _ ‹_›) a b

@[simp] lemma false_of_not_acyclic {u v v'} (huv : v <[F] u) (huv' : v' <[F] u) (hvv' : v ≠ v') :
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

scoped notation:50 a " ᵖ< " b => @LT.lt _ (instLT _) a b
scoped notation:50 a " ᵖ<[" F:50 "] " b => @LT.lt _ (instLT (F : RootedForest _ ‹_›)) a b

def toSimpleGraph : SimpleGraph (WithBot V) where
  Adj u v := (u <[F] v) ∨ (v <[F] u)
  loopless u := by simp [loopless]

def support := F.toSimpleGraph.support

lemma root_or_has_parent_of_mem_support {u} : u ∈ F.support → u = ⊥ ∨ ∃ v, v <[F] u := by
  intro ⟨v, huv⟩; simp [toSimpleGraph] at huv; by_cases u = ⊥
  · left; assumption
  · right; by_cases hu : F.IsOrigin u
    · use ⊥; simp [*]
    · simp only [isOrigin_def, not_and_or] at hu; cases hu <;> aesop

lemma mem_support_of_parent {u v} (_ : u <[F] v) : u ∈ F.support := by
  simp_all [support, toSimpleGraph, SimpleGraph.support]; use v; left; assumption

lemma mem_support_of_child {u v} (_ : u <[F] v) : v ∈ F.support := by
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

scoped infix:50 " ≤ " => @ancester_descendant _ _ _
scoped infix:50 " ≥ " => fun u v => @ancester_descendant _ _ _ v u
scoped notation:50 a " ≤[" F:50 "] " b => @ancester_descendant _ _ (F : RootedForest _ ‹_›) a b
scoped notation:50 a " ≥[" F:50 "] " b => @ancester_descendant _ _ (F : RootedForest _ ‹_›) b a

@[simp] lemma toAncesterDescendant : Subrelation F.parent_child F.ancester_descendant := by
  simp [Subrelation, ancester_descendant]; intro u v _
  use (show F.toSimpleGraph.Adj u v from by simp [toSimpleGraph, *]).toWalk; simp [Descend, *]

@[simp] lemma parent_child_not_commu {u v} (huv : u <[F] v) : ¬v <[F] u := by
  by_contra hvu; have := F.instPartialOrderWithBot.le_antisymm u v (F.toAncesterDescendant huv)
    (F.toAncesterDescendant hvu); subst_vars; exact F.loopless v huv

end LE

section Subgraph
variable {V : Type*} {κ : WithBot V → Type*} (F : RootedForest V κ)

@[simp] def _root_.SimpleGraph.subgraph_of_support (G : SimpleGraph V) :
  SimpleGraph.Subgraph G where
  verts := G.support
  Adj := G.Adj
  symm u v huv := G.adj_symm huv
  adj_sub := by intro v w a; simp_all only
  edge_vert := by simp [SimpleGraph.support]; intro v w a; apply Exists.intro; exact a

@[simp] def _root_.SimpleGraph.graph_of_support (G : SimpleGraph V) := G.subgraph_of_support.coe

@[simp] def toSimpleGraph' := (⊤ : F.toSimpleGraph.Subgraph)

@[simp] def toTree' := F.toSimpleGraph.subgraph_of_support

@[simp] def toTree := F.toSimpleGraph.graph_of_support

@[simp] def toForest' : F.toSimpleGraph.Subgraph where
  verts := F.toSimpleGraph.support \ {⊥}
  Adj := F.toSimpleGraph.Adj
  symm u v huv := F.toSimpleGraph.adj_symm huv
  adj_sub := by intro v w a; simp_all only
  edge_vert := by
    simp [SimpleGraph.support]; intro v w a;
    -- apply Exists.intro; exact a
    sorry

@[simp] def toForest := F.toForest'.coe

end Subgraph

section Acyclic
variable {V : Type*} {κ : WithBot V → Type*} (F : RootedForest V κ)

lemma isTree_of_toTree : F.toTree.IsTree := sorry

lemma isAcyclic_of_toForest : F.toForest.IsAcyclic := sorry

end Acyclic

class Standard extends RootedForest V κ where
  branch_bij v : Set.BijOn (branch v) Set.univ { u | ∃ j, branch v j = u }
  branch_inv' (v : V) [Nonempty (κ v)] : V → κ v
  branch_inv (v : V) [Nonempty (κ v)] :
    branch_inv' v = @Function.invFunOn _ _ _ (branch v) Set.univ
  branch_inv_on (v : V) [Nonempty (κ v)] :
    Set.InvOn (branch_inv' v) (branch v) Set.univ { u | ∃ j, branch v j = u } := ⟨by
      simp [Set.LeftInvOn]; intro x; simp [branch_inv v]
      exact (branch_bij v).injOn (Set.mem_univ _) (Set.mem_univ x)
        <| @Function.invFunOn_apply_eq _ _ _ (branch v) x _ (Set.mem_univ x), by
      simp [Set.RightInvOn]; intro u hu; simp [branch_inv v]
      exact @Function.invFunOn_eq _ _ _ (branch v) u _ <| (by
        have := (branch_bij v).surjOn; simp [Set.SurjOn] at this; simp
        exact Set.mem_range.1 <| Set.mem_of_subset_of_mem this hu)⟩
  branch_inv_bij (v : V) [Nonempty (κ v)]
    := (@Set.bijOn_comm _ _ _ _ (branch_inv' v) _ (branch_inv_on v)).mpr (branch_bij v)

end RootedForest





/-

variable (V : Type*) (β : V → Type*) (ρ : Unit → Type*)

class Branching where
  branch : (v : V) → (β v → V)
  branch_bij v : Set.BijOn (branch v) Set.univ { u | ∃ j, branch v j = u }
  branch_inj v := (branch_bij v).injOn
  branch_surj v := (branch_bij v).surjOn
  branch_inv (v : V) [Nonempty (β v)] : V → β v
  branch_inv_def (v : V) [Nonempty (β v)] :
    branch_inv v = @Function.invFunOn _ _ _ (branch v) Set.univ
  branch_inv_on (v : V) [Nonempty (β v)] :
    Set.InvOn (branch_inv v) (branch v) Set.univ { u | ∃ j, branch v j = u } := ⟨by
      simp [Set.LeftInvOn]; intro x; simp [branch_inv_def v]
      exact branch_inj v (Set.mem_univ _) (Set.mem_univ x)
        <| @Function.invFunOn_apply_eq _ _ _ (branch v) x _ (Set.mem_univ x), by
      simp [Set.RightInvOn]; intro u hu; simp [branch_inv_def v]
      exact @Function.invFunOn_eq _ _ _ (branch v) u _ <| (by
        have := branch_surj v; simp [Set.SurjOn] at this; simp
        exact Set.mem_range.1 <| Set.mem_of_subset_of_mem this hu)⟩
  branch_inv_bij (v : V) [Nonempty (β v)]
    := (@Set.bijOn_comm _ _ _ _ (branch_inv v) _ (branch_inv_on v)).mpr (branch_bij v)
  branch_inv_inj (v : V) [Nonempty (β v)] := (branch_inv_bij v).injOn
  branch_inv_surj (v : V) [Nonempty (β v)] := (branch_inv_bij v).surjOn
  parent_child : V → V → Prop
  parent_child_def : ∀ u v, parent_child u v ↔ ∃ j, branch u j = v
  acyclic_wedge : ∀ u v, u ≠ v → Set.range (branch u) ∩ Set.range (branch v) = ∅
  acyclic_oriented : ¬ ∃ p : ℕ → V, ∃ n, (∀ i < n, parent_child (p i) (p (i + 1))) ∧ p 0 = p n
  loopless : ∀ v, ¬ parent_child v v

-- attribute [simp] Branching.parent_child_def

namespace Branching

scoped infix:50 " ᵖ< " => @parent_child _ _ _
scoped infix:50 " ≻ᵖ " => fun a b => @parent_child _ _ _ b a
scoped notation:50 a " ᵖ<[" B:50 "] " b => @parent_child _ _ (B : Branching _ ‹_›) a b
scoped notation:50 b " ≻ᵖ[" B:50 "] " a => @parent_child _ _ (B : Branching _ ‹_›) b a

class Forest extends Branching V β where
  is_origin (v : V) : Prop
  is_origin_def : ∀ v, is_origin v
    ↔ (∃ u, parent_child v u) ∧ ¬∃ u, parent_child u v
  origin_wellfounded : WellFounded parent_child

namespace Forest

instance {V : Type*} {β : V → Type*} : Coe (Forest V β) (Branching V β) where
  coe F := F.toBranching

lemma parent_child_wellfounded {F : Forest V β} : WellFounded F.parent_child :=
  F.origin_wellfounded

instance (F : Forest V β) : WellFoundedRelation V := ⟨F.parent_child, F.parent_child_wellfounded⟩

lemma is_origin_def_parent_child {F : Forest V β} (v : V) :
  F.is_origin v ↔ (∃ u, v ᵖ<[F] u) ∧ ¬∃ u, u ᵖ<[F] v := by simp [is_origin_def]

noncomputable instance (F : Forest V β) (v : V) : Decidable (F.is_origin v) :=
  Classical.dec _

class Rooted extends Forest V β where
  root : ρ () → V
  root_bij : Set.BijOn root Set.univ { v | is_origin v }
  root_inj := root_bij.injOn
  root_surj := root_bij.surjOn
  root_inv [Nonempty (ρ ())] : V → ρ ()
  root_inv_def [Nonempty (ρ ())] : root_inv = Function.invFunOn root Set.univ
  root_inv_on [Nonempty (ρ ())] :
    Set.InvOn root_inv root Set.univ { v | is_origin v } := ⟨by
      simp [Set.LeftInvOn]; intro x; simp [root_inv_def]
      exact root_inj (Set.mem_univ _) (Set.mem_univ x)
        <| @Function.invFunOn_apply_eq _ _ _ root x _ (Set.mem_univ x), by
      simp [Set.RightInvOn]; intro v hv; simp [root_inv_def]
      exact @Function.invFunOn_eq _ _ _ root v _ <| (by
        have := root_surj; simp [Set.SurjOn] at this; simp
        exact Set.mem_range.1 <| Set.mem_of_subset_of_mem this hv)⟩
  root_inv_bij [Nonempty (ρ ())]
    := (@Set.bijOn_comm _ _ _ _ root_inv _ root_inv_on).mpr root_bij
  root_inv_inj [Nonempty (ρ ())] := root_inv_bij.injOn
  root_inv_surj [Nonempty (ρ ())] := root_inv_bij.surjOn

noncomputable instance instCoeDepForestRooted {V : Type*} {β : V → Type*} (F : Forest V β) :
  CoeDep (Forest V β) F (Rooted V β (fun _ => { v // F.is_origin v })) where
  coe := {
    branch := F.branch
    branch_bij := F.branch_bij
    branch_inv := F.branch_inv
    branch_inv_def := F.branch_inv_def
    parent_child := F.parent_child
    parent_child_def := F.parent_child_def
    acyclic_wedge := F.acyclic_wedge
    acyclic_oriented := F.acyclic_oriented
    loopless := F.loopless
    is_origin := F.is_origin
    is_origin_def := F.is_origin_def
    origin_wellfounded := F.origin_wellfounded
    root v := ↑v
    root_bij := by
      apply Set.BijOn.mk
      · simp [Set.MapsTo]
      · simp [Set.InjOn];
      · simp [Set.SurjOn]
    root_inv {hr : Nonempty { v // F.is_origin v }}
      := @Function.invFunOn _ _ hr (↑) Set.univ
    root_inv_def := by simp
  }

noncomputable def toRooted (F : Forest V β) := (instCoeDepForestRooted F).coe

inductive WithRoot where
  | root : Unit → WithRoot
  | node : V → WithRoot

namespace Rooted

variable {V : Type*} {β : V → Type*} {ρ : Unit → Type*} in
instance : CoeOut (Rooted V β ρ) (Forest V β) where
  coe FR := FR.toForest

@[simp] def parent_childᵣ {FR : Rooted V β ρ} : WithBot V → WithBot V → Prop
  | ⊥, ⊥ => False
  | ⊥, some v => ∃ i, FR.root i = v
  | some _, ⊥ => False
  | some u, some v => u ᵖ<[FR] v

@[simp] def root_parent_child {FR : Rooted V β ρ} : WithRoot V → WithRoot V → Prop
  | .root _, .root _ => False
  | .root _, .node v => ∃ i, FR.root i = v
  | .node _, .root _ => False
  | .node u, .node v => u ᵖ<[FR] v

scoped infix:50 " ᵖʳ< " => root_parent_child
scoped infix:50 " ≻ᵖʳ " => fun a b => root_parent_child b a
scoped notation:50 a " ᵖʳ<[" F:50 "] " b => @root_parent_child _ _ _ (F : Rooted _ ‹_› ‹_›) a b
scoped notation:50 b " ≻ᵖʳ[" F:50 "] " a => @root_parent_child _ _ _ (F : Rooted _ ‹_› ‹_›) a b

def toSimpleGraph_rooted (FR : Rooted V β ρ) : SimpleGraph (WithRoot V) where
  Adj u v := (u ᵖʳ<[FR] v) ∨ (v ᵖʳ<[FR] u)
  loopless u := by match u with
    | .root _ => simp
    | .node u => simp; have := FR.loopless; simp at this; exact this u

def toSimpleGraph_unrooted_sub (FR : Rooted V β ρ) :
  SimpleGraph.Subgraph (FR.toSimpleGraph_rooted) where
  verts := { v | ∃ a, v = .node a }
  Adj u v := match u, v with
    | .node _, .node _ => FR.toSimpleGraph_rooted.Adj u v
    | .node _, .root _ => False
    | .root _, .root _ => False
    | .root _, .node _ => False
  symm u v huv := by
    match u, v with
    | .node u, .node v => simp at ⊢ huv; exact FR.toSimpleGraph_rooted.symm huv
    | .node _, .root _ => simp at ⊢ huv
    | .root _, .root _ => simp at ⊢ huv
    | .root _, .node _ => simp at ⊢ huv
  adj_sub := by
    intros u v huv; match u, v with
    | .node _, .node _ => simp at ⊢ huv; exact huv
    | .node _, .root _ => simp at ⊢ huv
    | .root _, .root _ => simp at ⊢ huv
    | .root _, .node _ => simp at ⊢ huv
  edge_vert := by
    intros u v huv; match u, v with
    | .node _, .node _ => simp at ⊢ huv
    | .node _, .root _ => simp at ⊢ huv
    | .root _, .root _ => simp at ⊢ huv
    | .root _, .node _ => simp at ⊢ huv

def toSimpleGraph_unrooted (FR : Rooted V β ρ) := FR.toSimpleGraph_unrooted_sub.coe

end Rooted


-- ## WithRoot
section WithRoot

instance {n : ℕ} [OfNat V n] : OfNat (WithRoot V) n where
  ofNat := .node (OfNat.ofNat n)

instance (V : Type*) : Coe V (WithRoot V) where
  coe v := .node v

instance (V : Type*) : Coe Unit (WithRoot V) where
  coe _ := .root ()

instance (V : Type*) : Coe (Option V) (WithRoot V) where
  coe v := match v with
  | none => .root ()
  | some v => .node v


#check WithBot

@[simp] lemma root_ne_node {v : V} : WithRoot.node v ≠ () := by simp

variable {V : Type*}

def unroot (v : WithRoot V) (hv : v ≠ ()) : V := by
  match hv' : v with
  | () => contradiction
  | .node v0 => exact v0

@[simp] lemma node_unroot {v : WithRoot V} {hv : v ≠ ()} : unroot v hv = v := by
  match hv' : v with
  | () => contradiction
  | .node v0 =>  simp [unroot]

@[simp] lemma unroot_node {v : V} : unroot v (by simp) = v := by simp [unroot]

@[simp] lemma unroot_ext {v v' : WithRoot V} {hv : v ≠ ()} {hv' : v' ≠ ()}
  {hvv' : unroot v hv = unroot v' hv'} : v = v' := by
  match v, v' with
  | (), _ => contradiction
  | _, () => contradiction
  | .node v0, .node v0' => simp only [unroot_node] at hvv'; simpa only [WithRoot.node.injEq]

variable {V : Type*} {β : V → Type*} {ρ : Unit → Type*} {FR : Rooted V β ρ} {v : V} in
private lemma ne_root_of_is_origin : FR.is_origin v → WithRoot.node v ≠ () := by
  intro hv; by_contra hv'; contradiction

end WithRoot

-- ## Standard

class Standard [DecidableEq V] (β : V → ℕ) (ρ : Unit → ℕ) extends
  Rooted V (fun v => Fin (β v)) (fun r => Fin (ρ r)) where
  index : V → List ℕ
  index_origin : (hr : Nonempty (Fin (ρ ()))) → ∀ v, is_origin v → index v =
    [Fin.toNat <| @Function.invFunOn _ _ hr root Set.univ v]
  index_branch : ∀ u, (hu : Nonempty (Fin (β u))) → ∀ v j, (branch u j = v) →
    index v = index u ++ [Fin.toNat <| @Function.invFunOn _ _ hu (branch u) Set.univ v]
  index_rooted : (u : WithRoot V) → List ℕ := by
    induction u with
    | root _ => exact []
    | node v => exact index v
  layer' v := (index v).length

-- variable [Fintype V] [DecidableEq V] {β : V → ℕ} {ρ : Unit → ℕ} in
-- instance (FS : Standard V β ρ) (v : V) : Decidable (FS.is_origin v) := by
--   simp [is_origin_def, parent_child_def]; exact inferInstance

end Forest

variable {V : Type*} {β : V → Type*} {ρ : Unit → Type*}

def toSimpleGraph (B : Branching V β) : SimpleGraph V where
  Adj u v := (u ᵖ<[B] v) ∨ (v ᵖ<[B] u)
  loopless u := by simp; have := B.loopless u; simp at this; exact this

lemma adj_of_parent_child {B : Branching V β} (u v : V) (huv : u ᵖ<[B] v) :
  B.toSimpleGraph.Adj u v := by simp only [toSimpleGraph]; simp_all only [true_or]

open SimpleGraph in
lemma _root_.SimpleGraph.Walk.darts_getElem.{u} {V : Type u} {G : SimpleGraph V}
  {u v : V} (p : G.Walk u v) (i : ℕ) (hi : i < p.length) : p.darts[i]'(p.length_darts ▸ hi)
  = ⟨⟨p.getVert i, p.getVert (i + 1)⟩, p.adj_getVert_succ hi⟩ := by
  induction p generalizing i with
  | nil => simp; contradiction
  | cons h q ih =>
    simp [List.getElem_cons]; split_ifs
    · subst_vars; simp
    · simp at hi; specialize ih (i - 1) (by omega)
      have := Walk.getVert_cons q h (by omega : i ≠ 0)
      conv => rhs; congr; arg 1; rw [this]
      conv => rhs; congr; arg 2; rw [(by omega : i = i - 1 + 1)]
      assumption

open SimpleGraph in
lemma isAcyclic {F : Branching V β} : IsAcyclic F.toSimpleGraph := by
  dsimp [IsAcyclic]; intros v c; by_contra hc
  have h0 := hc.three_le_length
  by_cases h1 : ∃ i < c.length, ∃ j < c.length, ∃ k < c.length, (i ≠ k) ∧
    (c.getVert j ∈ Set.range (F.branch (c.getVert i))) ∧
    (c.getVert j ∈ Set.range (F.branch (c.getVert k)))
  · rcases h1 with ⟨i, hi, j, hj, k, hk, hne, hij, hjk⟩
    have h2 := F.acyclic_wedge (c.getVert i) (c.getVert k); contrapose h2
    simp at ⊢ hij hjk; rcases hij with ⟨m, hm⟩; rcases hjk with ⟨n, hn⟩; constructor
    · have h3 : i ∈ { i | i ≤ c.length - 1} := by simp only [Set.mem_setOf_eq]; omega
      have h4 : k ∈ { i | i ≤ c.length - 1} := by simp only [Set.mem_setOf_eq]; omega
      have h5 := hc.getVert_injOn' h3 h4;
      simp_all only [ne_eq, not_false_eq_true, Set.mem_setOf_eq, imp_false]
    · by_contra h_empty; have := h_empty ▸ Set.mem_inter (Set.mem_range.mpr ⟨m, hm⟩)
        (Set.mem_range.mpr ⟨n, hn⟩); contradiction
  · simp [-forall_exists_index] at h1
    have h6 := F.acyclic_oriented; contrapose h6; simp only [not_not]; clear h6
    by_cases h7 : ∃ j, F.branch (c.getVert 0) j = c.getVert 1
    · use c.getVert, c.length
      simp only [Walk.getVert_zero, Walk.getVert_length, and_true, parent_child_def]
      intro i hi; induction i with
      | zero => exact h7
      | succ i' ih =>
        by_cases h8 : i' = c.length - 2
        · subst_vars; specialize ih (by omega)
          rw [(by omega : c.length - 2 + 1 = c.length - 1)] at ih
          specialize h1 (c.length - 2) (by omega) (c.length - 1) (by omega) 0 (by omega)
            (by omega) ih
          have h9 := c.adj_getVert_succ (by omega : c.length - 1 < c.length)
          simp [toSimpleGraph, parent_child_def] at h9
          conv at h9 => rw [(by omega : c.length - 1 + 1 = c.length)]
          conv => rw [(by omega : c.length - 2 + 1 = c.length - 1)]
          conv => rw [(by omega : c.length - 1 + 1 = c.length)]
          rw [c.getVert_length] at ⊢ h9; rw [c.getVert_zero] at h1
          simp_all only [exists_false, or_false]
        · specialize ih (by omega)
          specialize h1 i' (by omega) (i' + 1) (by omega) (i' + 2) (by omega) (by omega) ih
          have h9 := c.adj_getVert_succ (by omega : i' + 1 < c.length)
          simp [toSimpleGraph, parent_child_def] at h9
          conv at h1 => rw [(by omega : i' + 2 = i' + 1 + 1)]
          simp_all only [exists_false, or_false]
    · use fun n => c.getVert (c.length - n), c.length
      simp only [tsub_zero, Walk.getVert_length, tsub_self, Walk.getVert_zero, and_true,
        Branching.parent_child_def]
      have h9 := c.adj_getVert_succ (by omega : 0 < c.length)
      simp [toSimpleGraph, parent_child_def, -Walk.getVert_zero] at h9
      have h7 : ∃ j, F.branch (c.getVert 1) j = c.getVert 0 := by
        simp_all only [forall_exists_index, not_exists,
        exists_false, Walk.getVert_zero, false_or]
      intro i hi; induction i with
      | zero =>
        specialize h1 1 (by omega) 0 (by omega) (c.length - 1) (by omega) (by omega) h7
        have h9 := c.adj_getVert_succ (by omega : c.length - 1 < c.length)
        simp [toSimpleGraph, parent_child_def] at h9; simp; rw [c.getVert_zero] at h1
        conv at h9 => rw [(by omega : c.length - 1 + 1 = c.length)]
        conv at h1 => ext; congr; rhs; rw [←c.getVert_length]
        simp_all only [not_exists, exists_false, Walk.getVert_zero, false_or, Walk.getVert_length]
      | succ i' ih =>
        induction i' with
        | zero =>
          specialize ih (by omega)
          rw [(by omega : c.length - 0 = c.length)] at ih
          rw [(by omega : c.length - (0 + 1) = c.length - 1)] at ih
          have : c.getVert (c.length) = c.getVert 0 := by rw[c.getVert_length, c.getVert_zero]
          rw [this] at ih
          specialize h1 0 (by omega) (c.length - 1) (by omega) (c.length - 2)
            (by omega) (by omega) ih
          have h9 := c.adj_getVert_succ (by omega : c.length - 2 < c.length)
          simp [toSimpleGraph, parent_child_def] at h9; simp at ⊢
          conv at h9 => rw [(by omega : c.length - 2 + 1 = c.length - 1)]
          simp_all only [not_exists, exists_false, Walk.getVert_zero, false_or,
            zero_add, Walk.getVert_length]
        | succ i'' ih' =>
          specialize ih (by omega)
          specialize h1 (c.length - (i'' + 1)) (by omega) (c.length - (i'' + 1 + 1)) (by omega)
            (c.length - (i'' + 1 + 1 + 1)) (by omega) (by omega) ih
          have h9 := c.adj_getVert_succ (by omega : c.length - (i'' + 1 + 1 + 1) < c.length)
          simp [toSimpleGraph, parent_child_def] at h9
          conv at h9 =>
            rw [(by omega : c.length - (i'' + 1 + 1 + 1) + 1 = c.length - (i'' + 1 + 1))]
          simp_all only [not_exists, exists_false, Walk.getVert_zero, false_or, implies_true]

def component {F : Branching V β} (v : V) := F.toSimpleGraph.connectedComponentMk v
def tree {F : Branching V β} (v : V) := (F.component v).toSimpleGraph
def tree_hom {F : Branching V β} {v : V} := (F.component v).toSimpleGraph_hom
open SimpleGraph in
@[simp] def tree_isTree {F : Branching V β} {v : V} : IsTree (F.tree v) := ⟨
    (F.component v).connected_toSimpleGraph, by
    simp [IsAcyclic]; intro x hx c
    set c' := Walk.map F.tree_hom c
    simp [tree_hom, ConnectedComponent.toSimpleGraph_hom_apply] at c'
    have := F.isAcyclic c'; contrapose this; simp only [not_not] at this ⊢
    have hinj : Function.Injective (@F.tree_hom _ _ v) := by
      simp [Function.Injective, tree_hom, component, ConnectedComponent.toSimpleGraph_hom]
    exact Walk.IsCycle.map hinj this
  ⟩

@[simp] def _root_.SimpleGraph.subgraph_of_support (G : SimpleGraph V) :
  SimpleGraph.Subgraph G where
  verts := G.support
  Adj := G.Adj
  symm u v huv := G.adj_symm huv
  adj_sub := by intro v w a; simp_all only
  edge_vert := by simp [SimpleGraph.support]; intro v w a; apply Exists.intro; exact a
def _root_.SimpleGraph.graph_of_support (G : SimpleGraph V) := G.subgraph_of_support.coe

instance {V : Type*} {G : SimpleGraph V} : CoeOut (↑G.subgraph_of_support.verts) V where
  coe v := by obtain ⟨v, hv⟩ := v; exact v

section Upload_Downlad_And_Other_Private_Similar_Functions

section Walk
open SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V} {u v : V} {p q : G.Walk u v}

lemma _root_.SimpleGraph.Walk.length_eq_of_eq (_ : p = q) :
  p.length = q.length := by simp [*]

lemma _root_.SimpleGraph.Walk.ext_getVert_iff : (∀ i, p.getVert i = q.getVert i)
  ↔ p = q := ⟨ext_getVert, by intro _ i; revert u; cases i <;> simp [*]⟩

lemma _root_.SimpleGraph.Walk.ext_support_iff : p.support = q.support
  ↔ p = q := ⟨ext_support, by intro; simp [*]⟩

end Walk

-- ## Upload
open SimpleGraph SimpleGraph.Subgraph in
@[simp] def _root_.SimpleGraph.Walk.upload {G : SimpleGraph V} {SG1 SG2 : Subgraph G}
  {u v : ↑SG1.verts} (w : SG1.coe.Walk u v) (hSG : SG1 ≤ SG2) :
  SG2.coe.Walk ((inclusion hSG) u) ((inclusion hSG) v) := w.map (inclusion hSG)

-- ## IsDownloadable
open SimpleGraph SimpleGraph.Subgraph in
def _root_.SimpleGraph.IsDownloadable {G : SimpleGraph V}
  (SG2 : Subgraph G) {u v : ↑SG2.verts} (w : SG2.coe.Walk u v) (SG1 : Subgraph G) : Prop :=
  (Subtype.val '' w.toSubgraph.verts ⊆ SG1.verts) ∧
  (Sym2.map Subtype.val '' w.toSubgraph.edgeSet ⊆ SG1.edgeSet)

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.isDownloadable_iff' {G : SimpleGraph V}
  {SG2 : Subgraph G} {u v : ↑SG2.verts} {w : SG2.coe.Walk u v} {SG1 : Subgraph G} :
  IsDownloadable SG2 w SG1 ↔ (w.map SG2.hom).toSubgraph ≤ SG1 := sorry

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.isDownloadable_iff {G : SimpleGraph V}
  {SG2 : Subgraph G} {u v : ↑SG2.verts} {w : SG2.coe.Walk u v} {SG1 : Subgraph G} :
  IsDownloadable SG2 w SG1 ↔ (∀ x ∈ w.support, x.1 ∈ SG1.verts) ∧
  ∀ x ∈ w.edgeSet, x.map Subtype.val ∈ SG1.edgeSet := by
  constructor
  · intro h; constructor
    · have h := h.1; simp only [Set.instHasSubset, Set.instLE, Set.Subset] at h; simp
      intro a ha haw; specialize @h a
      have : a ∈ Subtype.val '' w.toSubgraph.verts := by simp; use ha
      exact h this
    · sorry
  · intro h; constructor
    · sorry
    · sorry

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.lattice_le_iff_forall_isDownloadable {G : SimpleGraph V}
  {SG1 SG2 : Subgraph G} : SG1 ≤ SG2 ↔
  ∀ u v : ↑SG2.verts, ∀ w : SG2.coe.Walk u v, IsDownloadable SG2 w SG1 := sorry

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.isDownloadable_cons {G : SimpleGraph V}
  {SG2 : Subgraph G} {u u' v : ↑SG2.verts} {w : SG2.coe.Walk u' v}
  {huu' : SG2.coe.Adj u u'} {SG1 : Subgraph G}
  (h : IsDownloadable SG2 (Walk.cons huu' w) SG1) : IsDownloadable SG2 w SG1 := by
  simp [isDownloadable_iff] at *; simp at *; aesop

-- ## Download

open SimpleGraph SimpleGraph.Subgraph in
def _root_.SimpleGraph.Walk.download {G : SimpleGraph V}
  {SG1 SG2 : Subgraph G} {u v : ↑SG2.verts} (w : SG2.coe.Walk u v)
  (hwSG : IsDownloadable SG2 w SG1) : SG1.coe.Walk
    ⟨u.1, (isDownloadable_iff.1 hwSG).1 u w.start_mem_support⟩
    ⟨v.1, (isDownloadable_iff.1 hwSG).1 v w.end_mem_support⟩ := by
  cases w with
  | nil => exact Walk.nil
  | @cons u u' v h q =>
    have hwSG := isDownloadable_iff.1 hwSG
    conv at hwSG => left; simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp]
    conv at hwSG => right; simp only [Walk.edgeSet_cons, insert, Set.insert,
      Set.mem_setOf, forall_eq_or_imp]
    have : SG1.coe.Adj ⟨u.1, hwSG.1.1⟩ ⟨u'.1, hwSG.1.2 u' q.start_mem_support⟩ := by
      conv at hwSG => right; simp only [Sym2.map_pair_eq, Subgraph.mem_edgeSet];
      exact hwSG.2.1
    exact Walk.cons this <| q.download <| isDownloadable_iff.2 ⟨hwSG.1.2, hwSG.2.2⟩

open SimpleGraph SimpleGraph.Subgraph in
@[simp] lemma _root_.SimpleGraph.Walk.download_nil {G : SimpleGraph V}
  {SG1 SG2 : Subgraph G} {u : ↑SG2.verts} {hwSG : IsDownloadable SG2 Walk.nil SG1} :
  (Walk.nil : SG2.coe.Walk u u).download hwSG = Walk.nil := by simp [Walk.download]

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.Walk.download_mem_support_iff {G : SimpleGraph V}
  {SG1 SG2 : Subgraph G} {u v : ↑SG2.verts} {w : SG2.coe.Walk u v}
  {hwSG : IsDownloadable SG2 w SG1} {x : ↑SG2.verts} {hx : x.1 ∈ SG1.verts} :
  ⟨x, hx⟩ ∈ (w.download hwSG).support ↔ x ∈ w.support := by
  constructor
  · intro hx'; induction w with
    | nil => simp at hx'; simp; apply Subtype.ext; assumption
    | @cons u u' v h q hq =>
      obtain ⟨hw1, hw2⟩ := isDownloadable_iff.1 hwSG
      unfold Walk.download at hx'; simp at hx'; simp
      simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at hw1
      simp only [Walk.edgeSet_cons, insert, Set.insert, Set.mem_setOf, forall_eq_or_imp] at hw2
      cases hx'
      · left; apply Subtype.ext; assumption
      · exact Or.inr <| @hq (isDownloadable_iff.2 ⟨hw1.2, hw2.2⟩) ‹_›
  · intro hx'; induction w with
    | nil => simp at hx'; simp; exact congrArg Subtype.val hx'
    | @cons u u' v h q hq =>
      unfold Walk.download; simp; simp at hx'
      obtain ⟨hw1, hw2⟩ := isDownloadable_iff.1 hwSG
      simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at hw1
      simp only [Walk.edgeSet_cons, insert, Set.insert, Set.mem_setOf, forall_eq_or_imp] at hw2
      cases hx'
      · left; exact congrArg Subtype.val ‹_›
      · exact Or.inr <| @hq (isDownloadable_iff.2 ⟨hw1.2, hw2.2⟩) ‹_›

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.Walk.download_getVert {G : SimpleGraph V}
  {SG1 SG2 : Subgraph G} {u v : ↑SG2.verts} {w : SG2.coe.Walk u v}
  {hwSG : IsDownloadable SG2 w SG1} :
  ∀ n, (w.download hwSG).getVert n = ⟨w.getVert n,
    (isDownloadable_iff.1 hwSG).1 (w.getVert n) <| Walk.getVert_mem_support w n⟩ := by
  induction w with
  | nil => simp
  | cons h q h' =>
    intro n; induction n with
    | zero => simp
    | succ n' hn' =>
      unfold Walk.download; simp; exact @h' (isDownloadable_cons hwSG) n'

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.Walk.download_ext {G : SimpleGraph V}
  {SG1 SG2 : Subgraph G} {u v : ↑SG2.verts} {w1 w2 : SG2.coe.Walk u v}
  {hw1SG : IsDownloadable SG2 w1 SG1} {hw2SG : IsDownloadable SG2 w2 SG1} :
  w1.download hw1SG = w2.download hw2SG → w1 = w2 := by
  intro h12; apply Walk.ext_getVert; intro k
  exact Subtype.ext <| (eq_iff_iff.1 <| Subtype.mk.injEq _ _ _ _).1 <|
    w1.download_getVert k ▸ w2.download_getVert k ▸ Walk.ext_getVert_iff.2 h12 k

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.Walk.download_isPath_iff_isPath {G : SimpleGraph V}
  {SG1 SG2 : Subgraph G} {u v : ↑SG2.verts} {w : SG2.coe.Walk u v}
  {hwSG : IsDownloadable SG2 w SG1} : w.IsPath ↔ (w.download hwSG).IsPath := by
  constructor
  · intro hw'; induction w with
    | nil => simp
    | @cons u u' v h q hq =>
      unfold Walk.download; simp at ⊢ hw'
      obtain ⟨hw1, hw2⟩ := isDownloadable_iff.1 hwSG
      simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at hw1
      simp only [Walk.edgeSet_cons, insert, Set.insert, Set.mem_setOf, forall_eq_or_imp] at hw2
      constructor
      · exact @hq (isDownloadable_iff.2 ⟨hw1.2, hw2.2⟩) hw'.1
      · exact not_imp_not.2 Walk.download_mem_support_iff.1 hw'.2
  · intro hw'; induction w with
    | nil => simp
    | @cons u u' v h q hq =>
      simp; unfold Walk.download at hw'; simp at hw'
      obtain ⟨hw1, hw2⟩ := isDownloadable_iff.1 hwSG
      simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at hw1
      simp only [Walk.edgeSet_cons, insert, Set.insert, Set.mem_setOf, forall_eq_or_imp] at hw2
      constructor
      · exact @hq (isDownloadable_iff.2 ⟨hw1.2, hw2.2⟩) hw'.1
      · exact not_imp_not.2 Walk.download_mem_support_iff.2 hw'.2

-- ## toWalk_onTopSubgraph

open SimpleGraph in
def _root_.SimpleGraph.Walk.toWalk_onTopSubgraph {G : SimpleGraph V} :
  ∀ {u v : V}, G.Walk u v →
    (⊤ : Subgraph G).coe.Walk ⟨u, by simp⟩ ⟨v, by simp⟩
| _, _, Walk.nil => Walk.nil
| _, _, @Walk.cons _ _ u u' v h q =>
  let adj_top : (⊤ : Subgraph G).coe.Adj ⟨u, by simp⟩ ⟨u', by simp⟩ := by simpa
  Walk.cons adj_top (toWalk_onTopSubgraph q)

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.Walk.toWalk_onTopSubgraph_mem_support_iff
  {G : SimpleGraph V} {u v x : V} {w : G.Walk u v} :
  ⟨x, by simp⟩ ∈ w.toWalk_onTopSubgraph.support ↔ x ∈ w.support:= by
  induction w with
  | nil => simp [Walk.toWalk_onTopSubgraph]
  | @ cons u u' v h q h' =>
    simp [Walk.toWalk_onTopSubgraph]; constructor
    · intro this; cases this
      · exact Or.inl ‹_›
      · exact Or.inr <| h'.1 ‹_›
    · intro this; cases this
      · exact Or.inl ‹_›
      · exact Or.inr <| h'.2 ‹_›

open SimpleGraph SimpleGraph.Subgraph in
lemma _root_.SimpleGraph.Walk.toWalk_onTopSubgraph_isPath_iff_isPath
  {G : SimpleGraph V} {u v : V} {w : G.Walk u v} : w.IsPath ↔
  w.toWalk_onTopSubgraph.IsPath := by
  induction w with
  | nil => simp [Walk.toWalk_onTopSubgraph]
  | @ cons u u' v h q h' =>
    simp [Walk.toWalk_onTopSubgraph]; constructor
    · intro this; obtain ⟨h1, h2⟩ := this; exact ⟨h'.1 h1,
        not_imp_not.2 Walk.toWalk_onTopSubgraph_mem_support_iff.1 h2 ⟩
    · intro this; obtain ⟨h1, h2⟩ := this; exact ⟨h'.2 h1,
        not_imp_not.2 Walk.toWalk_onTopSubgraph_mem_support_iff.2 h2 ⟩


-- ## Other Private Similar Functions

open SimpleGraph in
private def _root_.SimpleGraph.Walk.toWalk_on_subgraph {G : SimpleGraph V}
  {SG : Subgraph G} {u v : V} (w : G.Walk u v) (hw : ∀ x ∈ w.support, x ∈ SG.verts)
  (hSG : ∀ x y : ↑SG.verts, SG.Adj x y = G.Adj x y) :
  SG.coe.Walk ⟨u, hw u w.start_mem_support⟩ ⟨v, hw v w.end_mem_support⟩ := by
  cases w with
  | nil => exact Walk.nil
  | @cons u u' v h q =>
    simp at hw; simp [Subgraph.coe]
    have : SG.Adj u u' := by
      have := hSG ⟨u, hw.1⟩ ⟨u', hw.2 u' q.start_mem_support⟩; simp at this; exact this.2 h
    exact Walk.cons this (toWalk_on_subgraph q hw.2 hSG)

open SimpleGraph in
private lemma _root_.SimpleGraph.Walk.toWalk_on_subgraph_mem_support_iff
  {G : SimpleGraph V} {SG : Subgraph G} {u v x : V} {w : G.Walk u v} {hx : x ∈ SG.verts}
  {hw : ∀ x ∈ w.support, x ∈ SG.verts} {hSG : ∀ x y : ↑SG.verts, SG.Adj x y = G.Adj x y} :
  ⟨x, hx⟩ ∈ (w.toWalk_on_subgraph hw hSG).support ↔ x ∈ w.support := by
  constructor
  · intro hx'; induction w with
    | nil => simp [Walk.toWalk_on_subgraph] at hx'; simpa
    | @cons u u' v h q hq =>
      unfold Walk.toWalk_on_subgraph at hx'; simp at hx' hw; simp; cases hx'
      · exact Or.inl ‹_›
      · exact Or.inr <| @hq hw.2 ‹_›
  · intro hx'; induction w with
    | nil => simp at hx'; simpa [Walk.toWalk_on_subgraph]
    | @cons u u' v h q hq =>
      unfold Walk.toWalk_on_subgraph; simp; simp at hx' hw; cases hx'
      · exact Or.inl ‹_›
      · exact Or.inr <| @hq hw.2 ‹_›

open SimpleGraph in
private lemma _root_.SimpleGraph.Walk.toWalk_on_subgraph_getVert
  {G : SimpleGraph V} {SG : Subgraph G} {u v : V} {w : G.Walk u v}
  {hw : ∀ x ∈ w.support, x ∈ SG.verts} {hSG : ∀ x y : ↑SG.verts, SG.Adj x y = G.Adj x y} :
  ∀ n, (w.toWalk_on_subgraph hw hSG).getVert n =
    ⟨w.getVert n, by apply hw; simp [Walk.getVert_mem_support]⟩ := by
  induction w with
  | nil => simp [Walk.toWalk_on_subgraph]
  | @cons u u' v h q hq =>
    intro n; induction n with
    | zero => simp
    | succ n' hn' => unfold Walk.toWalk_on_subgraph; simp at ⊢ hw; exact @hq hw.2 n'

open SimpleGraph in
private lemma _root_.SimpleGraph.Walk.toWalk_on_subgraph_ext
  {G : SimpleGraph V} {SG : Subgraph G} {u v : V} {w1 w2 : G.Walk u v}
  {hw1 : ∀ x ∈ w1.support, x ∈ SG.verts} {hw2 : ∀ x ∈ w2.support, x ∈ SG.verts}
  {hSG : ∀ x y : ↑SG.verts, SG.Adj x y = G.Adj x y} :
  w1.toWalk_on_subgraph hw1 hSG = w2.toWalk_on_subgraph hw2 hSG → w1 = w2 := by
  intro h12; apply Walk.ext_getVert; intro k
  exact (eq_iff_iff.1 <| Subtype.mk.injEq _ _ _ _).1 <| w1.toWalk_on_subgraph_getVert k
    ▸ w2.toWalk_on_subgraph_getVert k ▸ Walk.ext_getVert_iff.2 h12 k

open SimpleGraph in
private def _root_.SimpleGraph.Walk.toWalk_on_subgraph_isPath_iff_isPath
  {G : SimpleGraph V} {SG : Subgraph G} {u v : V} {w : G.Walk u v}
  {hw : ∀ x ∈ w.support, x ∈ SG.verts} {hSG : ∀ x y : ↑SG.verts, SG.Adj x y = G.Adj x y} :
  w.IsPath ↔ (w.toWalk_on_subgraph hw hSG).IsPath := by
  constructor
  · intro hw'; induction w with
    | nil => simp [Walk.toWalk_on_subgraph]
    | @cons u u' v h q hq =>
      unfold Walk.toWalk_on_subgraph; simp at ⊢ hw; constructor
      · exact @hq hw.2 (Walk.isPath_of_isSubwalk (q.isSubwalk_cons h) hw')
      · by_contra; simp [Walk.isPath_def] at hw'
        exact hw'.left <| Walk.toWalk_on_subgraph_mem_support_iff.mp ‹_›
  · intro hw'; induction w with
    | nil => simp
    | @cons u u' v h q hq =>
      simp; unfold Walk.toWalk_on_subgraph at hw'; simp at hw' hw; constructor
      · exact @hq hw.2 hw'.left
      · exact not_imp_not.mpr Walk.toWalk_on_subgraph_mem_support_iff.mpr hw'.right

open SimpleGraph in
private def _root_.SimpleGraph.Walk.toWalk_on_support_aux {G : SimpleGraph V}
  {u v : V} {w : G.Walk u v} (hu : u ∈ G.subgraph_of_support.verts)
  (hv : v ∈ G.subgraph_of_support.verts) : ∀ x ∈ w.support, x ∈ G.subgraph_of_support.verts := by
  by_cases w.length < 2
  · by_cases w.length < 1
    · obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 <| Nat.zero_add 1
        ▸ (by omega : w.length = 0) ▸ w.length_support
      have := ha ▸ w.start_mem_support; simp at this; have := Eq.symm this ▸ ha
      intro x hx; have := this ▸ hx; simp at this; rw [this]; exact hu
    · have := (by omega : w.length = 1) ▸ w.length_support
      obtain ⟨a, b, habw⟩ := w.support.length_eq_two.1 <| this
      have := w.getVert_eq_support_getElem (by omega : w.length ≤ w.length)
      simp [habw] at this; simp [(by omega : w.length = 1)] at this
      have := w.getVert_eq_support_getElem (by omega : 0 ≤ w.length)
      simp [habw] at this; subst_vars; intro x hx; have := habw ▸ hx; simp at this
      rcases this <;> subst_vars <;> first | exact hu | exact hv
  · simp [support]; intro x hx; obtain ⟨n, hxn, hnw⟩ := w.mem_support_iff_exists_getVert.1 hx
    by_cases hnw' : n = w.length
    · simp [hnw', Walk.getVert_length] at hxn
      have := (show w.length - 1 + 1 = w.length from by omega)
        ▸ w.adj_getVert_succ (show w.length - 1 < w.length from by omega)
      simp at this; exact ⟨w.getVert (w.length - 1), hxn ▸ Adj.symm this⟩
    · have := hxn ▸ w.adj_getVert_succ (by omega : n < w.length); use w.getVert (n + 1)

open SimpleGraph in
private def _root_.SimpleGraph.Walk.toWalk_on_support {G : SimpleGraph V} {u v : V}
  (w : G.Walk u v) (hu : u ∈ G.subgraph_of_support.verts)
  (hv : v ∈ G.subgraph_of_support.verts) : G.graph_of_support.Walk ⟨u, hu⟩ ⟨v, hv⟩ :=
  Walk.toWalk_on_subgraph w (Walk.toWalk_on_support_aux hu hv) (by simp)

open SimpleGraph in
private lemma _root_.SimpleGraph.Walk.toWalk_on_support_mem_support_iff {G : SimpleGraph V}
  {u v x : V} {w : G.Walk u v} {hu : u ∈ G.subgraph_of_support.verts}
  {hv : v ∈ G.subgraph_of_support.verts} {hx : x ∈ G.subgraph_of_support.verts} :
  ⟨x, hx⟩ ∈ (w.toWalk_on_support hu hv).support ↔ x ∈ w.support := by
  simp [Walk.toWalk_on_support]; exact @Walk.toWalk_on_subgraph_mem_support_iff
    _ _ G.subgraph_of_support _ _ _ w hx (Walk.toWalk_on_support_aux hu hv) (by simp)

open SimpleGraph in
private def _root_.SimpleGraph.Walk.toWalk_on_support_isPath_iff_isPath {G : SimpleGraph V}
  {u v : V} {w : G.Walk u v} {hu : u ∈ G.subgraph_of_support.verts}
  {hv : v ∈ G.subgraph_of_support.verts} : w.IsPath ↔ (w.toWalk_on_support hu hv).IsPath := by
  simp [Walk.toWalk_on_support]; exact @Walk.toWalk_on_subgraph_isPath_iff_isPath
    _ _ G.subgraph_of_support _ _ w (Walk.toWalk_on_support_aux hu hv) (by simp)
end Upload_Downlad_And_Other_Private_Similar_Functions

open SimpleGraph in
instance _root_.SimpleGraph.instIsoComponentSupportComponent {G : SimpleGraph V} {v : V}
  {hv : v ∈ G.subgraph_of_support.verts} : Iso (G.connectedComponentMk v).toSimpleGraph
  (G.graph_of_support.connectedComponentMk ⟨v, hv⟩).toSimpleGraph where
  toFun u := by
    rcases u with ⟨u, hu⟩; simp [SetLike.instMembership, SetLike.coe, Reachable] at hu
    apply Nonempty.some at hu
    have hu2 : u ∈ G.subgraph_of_support.verts := by
      simp only [subgraph_of_support, support, SetRel.mem_dom, Set.mem_setOf_eq]
      by_cases huv : u = v
      · rwa [←huv] at hv
      · have := Walk.end_mem_support hu
        have := Walk.start_mem_support hu
        have := List.length_pos_iff_exists_mem.mpr ⟨u, this⟩
        have : 1 < hu.support.length := by
          by_contra
          have := hu.support.length_eq_one_iff.mp (by omega : hu.support.length = 1)
          rcases this; simp_all only [subgraph_of_support, List.mem_cons, List.not_mem_nil,
            or_false, List.length_cons, List.length_nil, zero_add, zero_lt_one,
            lt_self_iff_false, not_false_eq_true, not_true_eq_false]
        have := hu.length_support
        have := hu.adj_getVert_succ (by omega : 0 < hu.length)
        rw [hu.getVert_zero] at this;
        simp_all only [subgraph_of_support, Walk.end_mem_support, Walk.start_mem_support,
          lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, Walk.length_support, zero_add]
        apply Exists.intro
        · exact this
    exact ⟨⟨u, hu2⟩, by
      simp only [subgraph_of_support, SetLike.instMembership, SetLike.coe,
        ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, Reachable]
      exact ⟨hu.toWalk_on_support hu2 hv⟩
    ⟩
  invFun u := by
    rcases u with ⟨u, hu⟩; simp [SetLike.instMembership, SetLike.coe, Reachable] at hu
    apply Nonempty.some at hu; rcases u with ⟨u, hu2⟩; exact ⟨u, by
      simp [SetLike.instMembership, SetLike.coe, Reachable]
      have := Walk.map G.subgraph_of_support.hom hu; simp [Subgraph.hom] at this
      exact ⟨this⟩
    ⟩
  map_rel_iff' := by
    intro u0 v0
    dsimp only [subgraph_of_support, Lean.Elab.WF.paramLet, Equiv.coe_fn_mk]
    simp [ConnectedComponent.toSimpleGraph, graph_of_support]

open SimpleGraph in
lemma _root_.SimpleGraph.isAcyclic_of_hom_inj {V : Type*} {V' : Type*} {G : SimpleGraph V}
  {G' : SimpleGraph V'} (hG : IsAcyclic G) (hom : G' →g G) (hom_inj : Function.Injective hom) :
  IsAcyclic G' := by
  dsimp [IsAcyclic] at hG ⊢; intros v c; by_contra hc
  set c' := SimpleGraph.Walk.map hom c
  specialize hG c'; contrapose hG; simp only [not_not]; clear hG
  exact SimpleGraph.Walk.IsCycle.map hom_inj hc

def toSimpleGraph' (B : Branching V β) := B.toSimpleGraph.graph_of_support
lemma isAcyclic' (B : Branching V β) : SimpleGraph.IsAcyclic B.toSimpleGraph'
  := SimpleGraph.isAcyclic_of_hom_inj B.isAcyclic B.toSimpleGraph.subgraph_of_support.hom
    B.toSimpleGraph.subgraph_of_support.hom_injective
def component' {B : Branching V β} (v : V) (hv : v ∈ B.toSimpleGraph.subgraph_of_support.verts)
  := B.toSimpleGraph'.connectedComponentMk ⟨v, hv⟩
def tree' {B : Branching V β} (v : V) (hv : v ∈ B.toSimpleGraph.subgraph_of_support.verts)
  := (B.component' v hv).toSimpleGraph
def tree'_hom {B : Branching V β} {v : V} {hv : v ∈ B.toSimpleGraph.subgraph_of_support.verts}
  := (B.component' v hv).toSimpleGraph_hom
open SimpleGraph in
@[simp] def tree'_isTree {B : Branching V β} {v : V}
  {hv : v ∈ B.toSimpleGraph.subgraph_of_support.verts} :
  SimpleGraph.IsTree (B.tree' v hv) := ⟨
    (B.component' v hv).connected_toSimpleGraph, by
      simp [SimpleGraph.IsAcyclic]; intro x hx hx' c
      set c' := Walk.map B.tree'_hom c
      simp [tree'_hom, ConnectedComponent.toSimpleGraph_hom_apply] at c'
      have := B.isAcyclic' c'; contrapose this; simp only [not_not] at this ⊢
      have hinj : Function.Injective (@B.tree'_hom _ _ v hv) := by
        simp [Function.Injective, tree'_hom, component', ConnectedComponent.toSimpleGraph_hom]
      exact Walk.IsCycle.map hinj this
  ⟩
instance instIsoTreeSubgraphTree (B : Branching V β) {v : V}
  {hv : v ∈ B.toSimpleGraph.subgraph_of_support.verts} : SimpleGraph.Iso (B.tree v) (B.tree' v hv)
  := @SimpleGraph.instIsoComponentSupportComponent V B.toSimpleGraph v hv

namespace Forest
variable {V : Type*} {β : V → Type*} {ρ : Unit → Type*}
open SimpleGraph Branching in
lemma two_origins_not_reachable {F : Forest V β} (u v : V) (hu : F.is_origin u) (hv : F.is_origin v)
  (huv : u ≠ v) : ¬ F.toSimpleGraph.Reachable u v := by
  by_contra hr
  have h : IsTree (F.tree v) := F.tree_isTree
  have := h.existsUnique_path
    ⟨u, by
      simp [component, ConnectedComponent.sound (reachable_comm.mp hr)];
      simp_all only [ne_eq, tree_isTree]; rfl⟩
    ⟨v, by simp_all only [ne_eq, tree_isTree]; rfl⟩
  rcases this with ⟨w, hw1, hw2⟩
  by_cases h1 : ∃ u0, ∃ (hu0 : u0 ∈ F.component v),
    ∃ w' : (F.tree v).Walk ⟨u0, hu0⟩ ⟨v, by simp_all only [ne_eq, tree_isTree]; rfl⟩,
    ∃ (hw' : w'.IsPath),
    ∃ i ≤ w'.length, ∃ j ≤ w'.length, ∃ k ≤ w'.length, (i ≠ k) ∧
    (↑(w'.getVert j)) ∈ (Set.range <| F.branch <| w'.getVert i) ∧
    (↑(w'.getVert j)) ∈ (Set.range <| F.branch <| w'.getVert k)
  · rcases h1 with ⟨v0, hv0, w', hw', i, hi, j, hj, k, hk, hne, hij, hjk⟩
    have h2 := F.acyclic_wedge (w'.getVert i) (w'.getVert k); contrapose h2
    simp at ⊢ hij hjk; rcases hij with ⟨m, hij⟩; rcases hjk with ⟨n, hjk⟩; constructor
    · simp [Walk.isPath_def, List.Nodup, List.pairwise_iff_get] at hw'
      have := w'.length_support
      rw [w'.getVert_eq_support_getElem hi, w'.getVert_eq_support_getElem hk]
      by_cases i < k
      · specialize hw' ⟨i, by omega⟩ ⟨k, by omega⟩ (by omega)
        simp [component] at hw1; assumption
      · have := (by omega : k < i)
        specialize hw' ⟨k, by omega⟩ ⟨i, by omega⟩ (by omega)
        simp [component] at hw1;
        simp_all only [ne_eq, tree_isTree, not_false_eq_true, not_lt]
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [not_true_eq_false]
    · by_contra h_empty; have := h_empty ▸ Set.mem_inter (Set.mem_range.mpr ⟨m, hij⟩)
        (Set.mem_range.mpr ⟨n, hjk⟩); contradiction
  · simp [-forall_exists_index] at h1
    have : ∃ j, F.branch (w.getVert 1) j = w.getVert 0 := by
      generalize hw3 : w.length = n
      clear hw2 h hu
      revert u
      induction n with
      | zero =>
        intro _ _ _ _ _ hw; rw [←Walk.nil_iff_length_eq] at hw
        apply Walk.Nil.eq at hw; injection hw; contradiction
      | succ n' hn' =>
        intro u huv hr w hw1 hw2
        by_cases hw3 : w.length = 1
        · rw [←hw3, w.getVert_length]; simp
          apply Walk.adj_of_length_eq_one at hw3
          apply Hom.map_adj F.tree_hom at hw3
          simp [tree_hom, ConnectedComponent.toSimpleGraph_hom_apply,
            toSimpleGraph, parent_child_def] at hw3
          simp [is_origin_def, parent_child_def] at hv; rcases hv with ⟨_, _⟩;
          simp_all only [forall_exists_index, ne_eq, Walk.getVert_zero, exists_false, false_or]
        · have hw3 := (by omega : w.length > 1)
          specialize hn' (w.getVert 1) (by
              simp [Walk.isPath_def, List.Nodup, List.pairwise_iff_get] at hw1
              have := w.length_support
              have h' := w.getVert_eq_support_getElem (by omega : 1 ≤ w.length)
              have h'' := w.getVert_eq_support_getElem (by omega : w.length ≤ w.length)
              specialize hw1 ⟨1, by omega⟩ ⟨w.length, by omega⟩ (by omega)
              simp at hw1; rw [←h', ←h'', w.getVert_length] at hw1; contrapose hw1
              simp only [ne_eq, not_not] at hw1 ⊢; apply Subtype.ext; simpa
            ) (by
              have := Walk.map F.tree_hom <| w.drop 1
              simp [tree_hom, ConnectedComponent.toSimpleGraph_hom_apply] at this
              exact ⟨this⟩
            ) (w.drop 1) (by
              have : (w.drop 1).IsSubwalk w := by
                simp [Walk.IsSubwalk]; use (w.take 1), Walk.nil
                apply Walk.ext_getVert; intro k; simp [Walk.getVert_append]; split_ifs
                · rw[(by omega : min 1 k = k)]
                · rw[(by omega : 1 + (k - min 1 w.length) = k)]
              have := Walk.isPath_of_isSubwalk this ‹_›
              simp [Walk.isPath_def] at this ⊢; assumption
            ) (by simp; omega)
          have hn' := (w.drop_getVert 1 1) ▸ hn'; simp at hn'
          specialize h1 u
            (by
              simp [component, ConnectedComponent.sound (reachable_comm.mp hr)];
              rename_i hn'_1
              simp_all only [forall_exists_index, ne_eq, Nat.add_eq_right, gt_iff_lt,
                lt_add_iff_pos_left, SetLike.eta, Walk.getVert_zero]
              obtain ⟨w_1, h⟩ := hn'_1
              obtain ⟨w_2, h_1⟩ := hn'
              rfl
            )
            w hw1 2 (by omega) 1 (by omega) 0 (by omega) (by omega) hn'
          have hw4 := w.adj_getVert_succ (by omega : 0 < w.length)
          apply Hom.map_adj F.tree_hom at hw4; simp [-Walk.getVert_zero, tree_hom, component,
            ConnectedComponent.toSimpleGraph_hom, toSimpleGraph, parent_child_def] at hw4
          simp_all only [ne_eq, Nat.add_eq_right, gt_iff_lt, lt_add_iff_pos_left, exists_false,
            Walk.getVert_zero, false_or]
    simp at this; rcases this with ⟨j, hj⟩
    simp [is_origin_def, parent_child_def] at hu; rcases hu with ⟨_, hu2⟩
    specialize hu2 ↑(w.getVert 1) j hj
    contradiction

open SimpleGraph in
lemma origin_component_ne {F : Forest V β} (u v : V) (hu : F.is_origin u) (hv : F.is_origin v)
  (huv : u ≠ v) : F.toSimpleGraph.connectedComponentMk u
  ≠ F.toSimpleGraph.connectedComponentMk v := by
  by_contra; exact F.two_origins_not_reachable u v hu hv huv <| ConnectedComponent.exact ‹_›

open SimpleGraph in
lemma origin_reachable {F : Forest V β} (u : V) (hu : F.is_origin u ∨ ∃ v, v ᵖ<[F] u) :
  ∃ v, ∃ (_ : F.is_origin v), F.toSimpleGraph.Reachable u v := by
  induction u using F.origin_wellfounded.induction with
  | h u0 hu0 =>
    by_cases hu0' : F.is_origin u0
    · use u0
    · have := Or.resolve_left hu hu0'
      rcases this with ⟨v, hv⟩; specialize hu0 v hv
      by_cases hv' : F.is_origin v ∨ ∃ v', v' ᵖ<[F] v
      · specialize hu0 hv'; rcases hu0 with ⟨v', hv', ⟨wvv'⟩⟩; use v', hv'
        exact ⟨(Adj.toWalk (adj_of_parent_child v u0 hv)).reverse.append wvv'⟩
      · simp only [is_origin_def_parent_child, not_or, not_and'] at hv';
        simp_all only [parent_child_def, false_or, Branching.parent_child_def,
          exists_prop, not_exists, forall_apply_eq_imp_iff, not_false_eq_true,
          implies_true, exists_false, or_false]
        obtain ⟨w, h⟩ := hu
        obtain ⟨w_1, h_1⟩ := hv
        obtain ⟨left, right⟩ := hv'
        obtain ⟨w_2, h⟩ := h
        subst h_1
        simp_all only [not_false_eq_true, implies_true, forall_const]
        apply Exists.intro
        · apply And.intro
          on_goal 2 => { rfl
          }
          · simp_all only
            apply left
            exact w_1

namespace Rooted

lemma adj_rooted_of_parent_child {FR : Rooted V β ρ} {u v : V} (huv : u ᵖ<[FR] v) :
  FR.toSimpleGraph_rooted.Adj u v := by
  simp only [toSimpleGraph_rooted]; simp_all only [root_parent_child, true_or]

lemma adj_rooted_of_root_origin {FR : Rooted V β ρ} {v : V} (hv : FR.is_origin v) :
  FR.toSimpleGraph_rooted.Adj () v := by
  obtain ⟨j, _, hj⟩ := (Set.mem_image _ _ _).mp
    <| Set.mem_of_subset_of_mem FR.root_surj <| Set.mem_setOf.mpr hv
  simp only [toSimpleGraph_rooted]; subst hj
  simp_all only [Set.mem_univ, root_parent_child, exists_apply_eq_apply, or_false]

lemma ne_root_of_adj_root_of_rooted {FR : Rooted V β ρ} {v : WithRoot V}
  (hv : FR.toSimpleGraph_rooted.Adj () v) : v ≠ () := by
  by_contra; subst_vars; exact FR.toSimpleGraph_rooted.loopless () hv

lemma is_origin_of_adj_root_of_rooted₀ {FR : Rooted V β ρ} {v' : WithRoot V}
  (hv : FR.toSimpleGraph_rooted.Adj () v') :
  FR.is_origin (unroot v' <| ne_root_of_adj_root_of_rooted hv) := by
  have := @node_unroot _ v' <| ne_root_of_adj_root_of_rooted hv
  set v := unroot v' <| ne_root_of_adj_root_of_rooted hv
  rw [←this] at hv
  simp [toSimpleGraph_rooted] at hv; rcases hv with ⟨i, hi⟩; let hi' := hi
  have : Nonempty (ρ ()) := ⟨i⟩
  have := FR.root_inv_surj; simp only [Set.SurjOn] at this
  apply congrArg FR.root_inv at hi
  conv at hi => lhs; simp [root_inv_def, FR.root_inv_on.left (Set.mem_univ i)]
  have := Set.mem_of_subset_of_mem ‹_› (hi ▸ Set.mem_univ i)
  simp only [Set.mem_image] at this; rcases this with ⟨v0, ⟨hv0, hvv0⟩ ⟩
  simp only [Set.mem_setOf_eq] at hv0
  rw [←hi] at hvv0; apply congrArg FR.root at hvv0
  rw [FR.root_inv_on.right <| Set.mem_setOf.mpr hv0, hi'] at hvv0
  exact hvv0 ▸ hv0

lemma is_origin_of_adj_root_of_rooted {FR : Rooted V β ρ} (v : V)
  (hv : FR.toSimpleGraph_rooted.Adj () v) : FR.is_origin v := by
  have := @is_origin_of_adj_root_of_rooted₀ _ _ _ FR v hv; simp [unroot] at this; exact this

open SimpleGraph in
lemma ne_root_getVert_one_of_walk_from_root_of_rooted {FR : Rooted V β ρ} {v : WithRoot V}
  (w : FR.toSimpleGraph_rooted.Walk () v) (hw : ¬w.Nil) : w.getVert 1 ≠ () := by
  by_contra h
  have := w.adj_getVert_succ <| Walk.not_nil_iff_lt_length.1 hw; simp at this
  have := h ▸ this; exact FR.toSimpleGraph_rooted.loopless () this

open SimpleGraph in
lemma is_origin_getVert_one_of_walk_from_root_of_rooted {FR : Rooted V β ρ}
  {v : WithRoot V} (w : FR.toSimpleGraph_rooted.Walk () v) (hw : ¬w.Nil) :
  FR.is_origin (unroot (w.getVert 1)
    (ne_root_getVert_one_of_walk_from_root_of_rooted w hw) ) := by
  have := w.adj_getVert_succ <| Walk.not_nil_iff_lt_length.1 hw; simp at this
  exact is_origin_of_adj_root_of_rooted₀ this

def toSimpleGraph_rooted' (FR : Rooted V β ρ) := FR.toSimpleGraph_rooted.graph_of_support

open SimpleGraph in
lemma adj_rooted'_of_parent_child {FR : Rooted V β ρ} {u v : V} (huv : u ᵖ<[FR] v) :
  FR.toSimpleGraph_rooted'.Adj ⟨u, by
    simp [subgraph_of_support, support]; use v; simp [toSimpleGraph_rooted]; exact Or.inl huv
  ⟩  ⟨v, by
    simp [subgraph_of_support, support]; use u; simp [toSimpleGraph_rooted]; exact Or.inr huv
  ⟩ := by
  simp [toSimpleGraph_rooted', graph_of_support, toSimpleGraph_rooted]; exact Or.inl huv

open SimpleGraph in
lemma adj_rooted'_of_root_origin {FR : Rooted V β ρ} {v : V} (hv : FR.is_origin v) :
  FR.toSimpleGraph_rooted'.Adj ⟨(), by
    simp [subgraph_of_support, support]; use v; simp [toSimpleGraph_rooted]
    obtain ⟨j, _, hj⟩ := (Set.mem_image _ _ _).1 <| Set.mem_of_subset_of_mem FR.root_surj
      <| Set.mem_setOf.2 hv; exact ⟨j, hj⟩
  ⟩  ⟨v, by
    simp [subgraph_of_support, support]; use (); simp [toSimpleGraph_rooted]
    obtain ⟨j, _, hj⟩ := (Set.mem_image _ _ _).1 <| Set.mem_of_subset_of_mem FR.root_surj
      <| Set.mem_setOf.2 hv; exact ⟨j, hj⟩
  ⟩ := by
  simp [toSimpleGraph_rooted', graph_of_support, toSimpleGraph_rooted]
  obtain ⟨j, _, hj⟩ := (Set.mem_image _ _ _).1 <| Set.mem_of_subset_of_mem FR.root_surj
    <| Set.mem_setOf.2 hv; exact ⟨j, hj⟩

lemma mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root {FR : Rooted V β ρ}
  {v : WithRoot V} : v ∈ FR.toSimpleGraph_unrooted_sub.verts ↔ v ≠ () := by
  constructor
  · intro hv; simp [toSimpleGraph_unrooted_sub] at hv; obtain ⟨v0, hvv0⟩ := hv
    match v with
    | () => simp_all only [reduceCtorEq]
    | .node u => simp
  · intro hv; simp [toSimpleGraph_unrooted_sub]; match v with
    | () => simp_all only [ne_eq, not_true_eq_false]
    | .node u => use u

lemma node_mem_unrooted {FR : Rooted V β ρ} (v : V) :
  WithRoot.node v ∈ FR.toSimpleGraph_unrooted_sub.verts := by
  have : WithRoot.node v ≠ () := by simp
  exact FR.mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 this

instance (FR : Rooted V β ρ) : Coe V (↑FR.toSimpleGraph_unrooted_sub.verts) where
  coe v := ⟨.node v, v, rfl⟩

def toSimpleGraph_unrooted' (FR : Rooted V β ρ) := FR.toSimpleGraph_unrooted.graph_of_support

lemma mem_toSimpleGraph_unrooted_subgraph_of_support_verts_of_is_origin {FR : Rooted V β ρ}
  {v : V} (hv : FR.is_origin v) : ↑v ∈ FR.toSimpleGraph_unrooted.subgraph_of_support.verts := by
  simp [SimpleGraph.support]; simp [is_origin_def] at hv; obtain ⟨⟨u, hu⟩, _⟩ := hv
  use u; simp [toSimpleGraph_unrooted_sub, toSimpleGraph_unrooted, toSimpleGraph_rooted]
  exact Or.inl hu

lemma adj_unrooted_of_parent_child {FR : Rooted V β ρ} {u v : V} (huv : u ᵖ<[FR] v) :
  FR.toSimpleGraph_unrooted.Adj u v := by
  simp [toSimpleGraph_unrooted, toSimpleGraph_unrooted_sub]
  exact adj_rooted_of_parent_child huv

def unrooted_sub_hom {FR : Rooted V β ρ} := FR.toSimpleGraph_unrooted_sub.coe_hom

open SimpleGraph in
@[simp]
instance insIsoUnrooted (FR : Rooted V β ρ) : Iso FR.toSimpleGraph FR.toSimpleGraph_unrooted
  := {
    toFun v := ⟨.node v, v, rfl⟩
    invFun := fun ⟨w, hw⟩ => match w, hw with
      | .node v, _ => v
      | .root _, h => False.elim (by rcases h with ⟨a, ha⟩; cases ha)
    right_inv := by intro ⟨w, hw⟩; match w with
      | .node v => dsimp
      | .root _ => exact False.elim (by rcases hw with ⟨a, ha⟩; cases ha)
    map_rel_iff' := by
      intro u v
      dsimp [toSimpleGraph, toSimpleGraph_unrooted_sub, toSimpleGraph_unrooted,
        toSimpleGraph_rooted, parent_child]
      simp
  }

def unroot_iso_hom {FR : Rooted V β ρ} := FR.insIsoUnrooted.symm.toRelEmbedding.toRelHom

open SimpleGraph in
lemma isAcyclic_unrooted (FR : Rooted V β ρ) : IsAcyclic FR.toSimpleGraph_unrooted :=
  SimpleGraph.isAcyclic_of_hom_inj FR.isAcyclic FR.unroot_iso_hom
    FR.insIsoUnrooted.symm.injective
def component_unrooted {FR : Rooted V β ρ} (v : V)
  := FR.toSimpleGraph_unrooted.connectedComponentMk ⟨v, v, rfl⟩
def tree_unrooted {FR : Rooted V β ρ} (v : V) := (FR.component_unrooted v).toSimpleGraph
open SimpleGraph in
@[simp]
def tree_unrooted_isTree (FR : Rooted V β ρ) (v : V) : IsTree (FR.tree_unrooted v) :=
  ⟨(FR.component_unrooted v).connected_toSimpleGraph, by
    simp [IsAcyclic]; intro x hx hx' c
    set c' := Walk.map (FR.component_unrooted v).toSimpleGraph_hom c
    set c'' := Walk.map FR.unroot_iso_hom c'
    have h1 := FR.toForest.isAcyclic; dsimp [IsAcyclic] at h1 ⊢
    by_contra hc; specialize h1 c''; contrapose h1; simp only [not_not]; clear h1
    have h2 : Function.Injective FR.unroot_iso_hom :=
      FR.insIsoUnrooted.symm.injective
    have h3 : Function.Injective (FR.component_unrooted v).toSimpleGraph_hom := by
      simp [Function.Injective, ConnectedComponent.toSimpleGraph_hom]
    exact Walk.IsCycle.map h2 <| Walk.IsCycle.map h3 hc
  ⟩

open SimpleGraph in
private instance instIsoTreeUnrootedInduced {FR : Forest.Rooted V β ρ} (z : V) :
  Iso (FR.tree_unrooted z)
  ((⊤ : Subgraph FR.toSimpleGraph_unrooted).induce (FR.component_unrooted z).supp).coe :=
  {
    toFun := by
      intro x; obtain ⟨⟨x, hx'⟩, hx⟩ := x
      exact ⟨⟨x, hx'⟩, by
        simp; simp only [component_unrooted] at hx ⊢
        exact (ConnectedComponent.mem_supp_iff _ _).1 hx ⟩
    invFun := by
      intro x; obtain ⟨x, hx⟩ := x; simp at hx
      exact ⟨x, by
        simp only [component_unrooted] at hx ⊢
        exact (ConnectedComponent.mem_supp_iff _ _).2 hx ⟩
    map_rel_iff' := by
      intro x y; obtain ⟨⟨x, hx'⟩, hx⟩ := x; obtain ⟨⟨y, hy'⟩, hy⟩ := y
      simp [Subgraph.coe, tree_unrooted, component_unrooted, ConnectedComponent.toSimpleGraph,
        toSimpleGraph_unrooted]
  }

open SimpleGraph in
private def _root_.SimpleGraph.Walk.toWalk_on_component_unrooted
  {FR : Forest.Rooted V β ρ}
  {u v : ↑FR.toSimpleGraph_unrooted_sub.verts} (z : V)
  (w : FR.toSimpleGraph_unrooted.Walk u v)
  (hu : u ∈ FR.component_unrooted z) (hv : v ∈ FR.component_unrooted z) :
  (FR.tree_unrooted z).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  have : IsDownloadable (⊤ : Subgraph FR.toSimpleGraph_unrooted) w.toWalk_onTopSubgraph
    ((⊤ : Subgraph FR.toSimpleGraph_unrooted).induce (FR.component_unrooted z).supp) := by
    simp [isDownloadable_iff]; constructor
    · intro x hx hx'; induction w with
      | nil =>
        simp [Walk.toWalk_onTopSubgraph] at hx'; subst hx'
        simp only [component_unrooted] at hv ⊢
        exact (ConnectedComponent.mem_supp_iff _ _).1 hv
      | cons h q h' =>
        simp [Walk.toWalk_onTopSubgraph] at hx'; cases hx'
        · subst_vars; simp only [component_unrooted] at hu ⊢
          exact (ConnectedComponent.mem_supp_iff _ _).1 hu
        · exact h' (by
            simp [component_unrooted] at hu ⊢
            have hu := ConnectedComponent.exact <| (ConnectedComponent.mem_supp_iff _ _).1 hu
            simp [Membership.mem, Set.Mem, SetLike.coe, ConnectedComponent.supp, setOf]
            simp [Reachable] at hu ⊢; obtain ⟨wuz⟩ := hu; exact ⟨h.toWalk.reverse.append wuz⟩
          ) hv ‹_›
    · intro x hx; induction w with
      | nil => simp [Walk.toWalk_onTopSubgraph] at hx
      | cons h q h' =>
        simp [Walk.toWalk_onTopSubgraph] at hx; cases hx
        · subst_vars; simp; exact ⟨by
            simp only [component_unrooted] at hu ⊢;
            exact (ConnectedComponent.mem_supp_iff _ _).1 hu, by
            simp [component_unrooted] at hu ⊢
            have hu := ConnectedComponent.exact <| (ConnectedComponent.mem_supp_iff _ _).1 hu
            simp [Reachable] at hu ⊢; obtain ⟨wuz⟩ := hu; exact ⟨h.toWalk.reverse.append wuz⟩, h⟩
        · exact h' (by
            simp [component_unrooted] at hu ⊢
            have hu := ConnectedComponent.exact <| (ConnectedComponent.mem_supp_iff _ _).1 hu
            simp [Membership.mem, Set.Mem, SetLike.coe, ConnectedComponent.supp, setOf]
            simp [Reachable] at hu ⊢; obtain ⟨wuz⟩ := hu; exact ⟨h.toWalk.reverse.append wuz⟩)
            hv ‹_›
  exact ((w.toWalk_onTopSubgraph.download this).map
    (FR.instIsoTreeUnrootedInduced z).symm.toRelEmbedding.toRelHom).copy
    (by simp [instIsoTreeUnrootedInduced]) (by simp [instIsoTreeUnrootedInduced])

open SimpleGraph SimpleGraph.Subgraph in
private lemma _root_.SimpleGraph.Walk.toWalk_on_component_unrooted_mem_support_iff
  {FR : Forest.Rooted V β ρ}
  {u v x : ↑FR.toSimpleGraph_unrooted_sub.verts} {z : V}
  {w : FR.toSimpleGraph_unrooted.Walk u v}
  {hu : u ∈ FR.component_unrooted z} {hv : v ∈ FR.component_unrooted z}
  {hx : x ∈ FR.component_unrooted z} :
  ⟨x, hx⟩ ∈ (w.toWalk_on_component_unrooted z hu hv).support ↔ x ∈ w.support := by
  induction w with
  | nil => simp [Walk.toWalk_on_component_unrooted, instIsoTreeUnrootedInduced,
      Walk.toWalk_onTopSubgraph, Walk.download]
  | @ cons u u' v h q h' =>
    simp [Walk.toWalk_on_component_unrooted, Walk.toWalk_onTopSubgraph,
      instIsoTreeUnrootedInduced] at ⊢ h'
    unfold Walk.download; simp
    have hu' : u' ∈ component_unrooted z := by
      simp [component_unrooted, Membership.mem, Set.Mem, SetLike.coe,
        ConnectedComponent.supp, setOf, Reachable] at hu ⊢; obtain ⟨wuz⟩ := hu
      exact ⟨h.toWalk.reverse.append wuz⟩
    constructor
    · intro this; cases this
      · exact Or.inl ‹_›
      · exact Or.inr <| (@h' hu' hv).1 ‹_›
    · intro this; cases this
      · exact Or.inl ‹_›
      · exact Or.inr <| (@h' hu' hv).2 ‹_›

open SimpleGraph Subgraph Walk ConnectedComponent in
private lemma _root_.SimpleGraph.Walk.toWalk_on_component_unrooted_getVert
  {FR : Forest.Rooted V β ρ}
  {u v : ↑FR.toSimpleGraph_unrooted_sub.verts} {z : V}
  {w : FR.toSimpleGraph_unrooted.Walk u v}
  {hu : u ∈ FR.component_unrooted z} {hv : v ∈ FR.component_unrooted z} :
  ∀ n, (w.toWalk_on_component_unrooted z hu hv).getVert n = ⟨w.getVert n, by
    simp [component_unrooted, Membership.mem, Set.Mem, SetLike.coe, supp, setOf, Reachable]
      at ⊢ hv; obtain ⟨wvz⟩ := hv; exact ⟨(w.drop n).append wvz⟩
  ⟩ := by
  induction w with
  | nil => simp [toWalk_on_component_unrooted, instIsoTreeUnrootedInduced,
      Walk.toWalk_onTopSubgraph, Walk.download];
  | cons h q h' =>
    intro n; induction n with
    | zero => simp
    | succ n' hn' =>
      simp [toWalk_on_component_unrooted, instIsoTreeUnrootedInduced,
      Walk.toWalk_onTopSubgraph]
      unfold download; simp [RelEmbedding.toRelHom, Walk.map]
      specialize @h' (by
        simp [component_unrooted, Membership.mem, Set.Mem, SetLike.coe, supp, setOf, Reachable]
          at ⊢ hu; obtain ⟨wuz⟩ := hu; exact ⟨h.symm.toWalk.append wuz⟩) hv n'
      simp [toWalk_on_component_unrooted, instIsoTreeUnrootedInduced, RelIso.toRelEmbedding,
        RelEmbedding.toRelHom] at h'; assumption

open SimpleGraph SimpleGraph.Subgraph in
private lemma _root_.SimpleGraph.Walk.toWalk_on_component_unrooted_ext
  {FR : Forest.Rooted V β ρ}
  {u v : ↑FR.toSimpleGraph_unrooted_sub.verts} {z : V}
  {w1 w2 : FR.toSimpleGraph_unrooted.Walk u v}
  {hu : u ∈ FR.component_unrooted z} {hv : v ∈ FR.component_unrooted z} :
  w1.toWalk_on_component_unrooted z hu hv = w2.toWalk_on_component_unrooted z hu hv
  → w1 = w2 := by
  intro h12; apply Walk.ext_getVert; intro k
  exact (eq_iff_iff.1 <| Subtype.mk.injEq _ _ _ _).1 <|
    w1.toWalk_on_component_unrooted_getVert k
    ▸ w2.toWalk_on_component_unrooted_getVert k ▸ Walk.ext_getVert_iff.2 h12 k

open SimpleGraph SimpleGraph.Subgraph in
private lemma _root_.SimpleGraph.Walk.toWalk_on_component_unrooted_isPath_iff_isPath
  {FR : Forest.Rooted V β ρ}
  {u v : ↑FR.toSimpleGraph_unrooted_sub.verts} {z : V}
  {w : FR.toSimpleGraph_unrooted.Walk u v}
  {hu : u ∈ FR.component_unrooted z} {hv : v ∈ FR.component_unrooted z} :
  w.IsPath ↔ (w.toWalk_on_component_unrooted z hu hv).IsPath := by
  induction w with
  | nil => simp [Walk.toWalk_on_component_unrooted, instIsoTreeUnrootedInduced,
      Walk.toWalk_onTopSubgraph, Walk.download]
  | @ cons u u' v h q h' =>
    simp [Walk.toWalk_on_component_unrooted, Walk.toWalk_onTopSubgraph] at ⊢ h'
    unfold Walk.download; simp
    conv =>
      right; right; ext x; ext hx; ext hx'; rw [←not_and]; congr;
      simp [instIsoTreeUnrootedInduced]
      rw [@Walk.download_mem_support_iff _ _ _ _ _ _ q.toWalk_onTopSubgraph _
        ⟨⟨x, hx⟩, (by simp)⟩  _]
      rw [@Walk.toWalk_onTopSubgraph_mem_support_iff _ _ _ _ ⟨x, hx⟩ q]
    constructor
    · intro this; obtain ⟨h1, h2⟩ := this; exact ⟨h'.1 h1, by aesop⟩
    · intro this; obtain ⟨h1, h2⟩ := this; exact ⟨h'.2 h1, by aesop⟩

lemma isAcyclic' (B : Rooted V β ρ) : SimpleGraph.IsAcyclic B.toSimpleGraph_unrooted'
  := SimpleGraph.isAcyclic_of_hom_inj B.isAcyclic_unrooted
    B.toSimpleGraph_unrooted.subgraph_of_support.hom
    B.toSimpleGraph_unrooted.subgraph_of_support.hom_injective
def component_unrooted' {B : Rooted V β ρ} (v : V)
  (hv : ↑v ∈ B.toSimpleGraph_unrooted.subgraph_of_support.verts)
  := B.toSimpleGraph_unrooted'.connectedComponentMk ⟨v, hv⟩
def tree_unrooted' {B : Rooted V β ρ} (v : V)
  (hv : ↑v ∈ B.toSimpleGraph_unrooted.subgraph_of_support.verts)
  := (B.component_unrooted' v hv).toSimpleGraph
def tree_unrooted'_hom {B : Rooted V β ρ} {v : V}
  {hv : ↑v ∈ B.toSimpleGraph_unrooted.subgraph_of_support.verts}
  := (B.component_unrooted' v hv).toSimpleGraph_hom
def tree_unrooted'_hom_inj {B : Rooted V β ρ} {v : V}
  {hv : ↑v ∈ B.toSimpleGraph_unrooted.subgraph_of_support.verts} :
  Function.Injective (@B.tree_unrooted'_hom _ _ _ v hv) := by
    simp [Function.Injective, tree_unrooted'_hom, component_unrooted',
      SimpleGraph.ConnectedComponent.toSimpleGraph_hom]
open SimpleGraph in
@[simp] def tree_unrooted'_isTree (B : Rooted V β ρ) (v : V)
  (hv : ↑v ∈ B.toSimpleGraph_unrooted.subgraph_of_support.verts) :
  SimpleGraph.IsTree (B.tree_unrooted' v hv) := ⟨
    (B.component_unrooted' v hv).connected_toSimpleGraph, by
      simp [SimpleGraph.IsAcyclic]; intro x hx hx' hx'' c
      set c' := Walk.map B.tree_unrooted'_hom c
      simp [tree_unrooted'_hom, ConnectedComponent.toSimpleGraph_hom_apply] at c'
      have := B.isAcyclic' c'; contrapose this; simp only [not_not] at this ⊢
      exact Walk.IsCycle.map tree_unrooted'_hom_inj this
  ⟩
instance instIsoTreeSubgraphTree (B : Rooted V β ρ) {v : V}
  {hv : ↑v ∈ B.toSimpleGraph_unrooted.subgraph_of_support.verts} :
    SimpleGraph.Iso (B.tree_unrooted v) (B.tree_unrooted' v hv)
  := @SimpleGraph.instIsoComponentSupportComponent _ B.toSimpleGraph_unrooted v hv

open SimpleGraph in
lemma origin_not_reachable_unrooted {FR : Rooted V β ρ} (u v : V) (hu : FR.is_origin u)
  (hv : FR.is_origin v) (huv : u ≠ v) : ¬ FR.toSimpleGraph_unrooted.Reachable u v := by
    simp only [Reachable]; by_contra hw; rcases hw with ⟨w⟩
    set w' := Walk.map FR.unroot_iso_hom w; simp [unroot_iso_hom] at w'
    exact FR.toForest.two_origins_not_reachable u v hu hv huv ⟨w'⟩

open SimpleGraph in
lemma origin_component_ne_unrooted {FR : Rooted V β ρ} (u v : V) (hu : FR.is_origin u)
  (hv : FR.is_origin v) (huv : u ≠ v) :
  FR.toSimpleGraph_unrooted.connectedComponentMk u
  ≠ FR.toSimpleGraph_unrooted.connectedComponentMk v := by
  by_contra; exact FR.origin_not_reachable_unrooted u v hu hv huv
    <| ConnectedComponent.exact ‹_›

open SimpleGraph in
lemma exists_origin_of_rooted'_nonempty {FR : Rooted V β ρ}
  [h : Nonempty ↑FR.toSimpleGraph_rooted.subgraph_of_support.verts] :
  ∃ v0, FR.is_origin v0 := by
  simp at h; rcases h with ⟨x, hx⟩;
  simp [support] at hx ⊢; rcases hx with ⟨y, hxy⟩
  match x, y with
  | (), () => exact False.elim <| FR.toSimpleGraph_rooted.loopless () hxy
  | (), (v : V) => exact ⟨v, is_origin_of_adj_root_of_rooted _ ‹_›⟩
  | (u : V), () => exact ⟨u, is_origin_of_adj_root_of_rooted _ <| Adj.symm ‹_›⟩
  | (v : V), (u : V) =>
    set s := FR.toSimpleGraph_rooted.graph_of_support.connectedComponentMk
      ⟨v, by simp [support]; use u⟩ with hs
    set s' : Set (WithRoot V) := s.supp.image (↑) with hs'
    set s'' : Set V := { v | (.node v) ∈ s' } with hs''
    simp [hs', hs, support, Reachable] at hs''
    have := FR.origin_wellfounded.has_min s'' ⟨u, by
      simp [hs'']; use ⟨v, hxy.symm⟩; exact ⟨hxy.symm.toWalk.toWalk_on_support
        (by simp [support]; use v; exact hxy.symm)
        (by simp [support]; use u)⟩⟩
    rcases this with ⟨v0, hv0_1, hv0_2⟩
    simp [hs''] at hv0_1; rcases hv0_1 with ⟨hv0_1, ⟨wv0v⟩⟩
    have hv0_2 : ∀ x, ¬Branching.parent_child β x v0 := by
      intro u0; by_cases hu0 : u0 ∈ s''
      · exact hv0_2 u0 hu0
      · by_contra hu0v0; apply adj_rooted_of_parent_child at hu0v0
        have : u0 ∈ s'' := by
          simp [hs'']; use ⟨v0, hu0v0⟩; have := hu0v0.toWalk.toWalk_on_support
            (by simp [support]; use v0) (by simpa [support])
          exact ⟨this.append wv0v⟩
        contradiction
    rcases hv0_1 with ⟨z, hzv0⟩; match z with
    | () => exact ⟨v0, is_origin_of_adj_root_of_rooted _ <| Adj.symm ‹_›⟩
    | .node z =>
      simp [toSimpleGraph_rooted] at hzv0; use v0; simp [is_origin_def]
      exact ⟨⟨z, Or.resolve_right hzv0 <| hv0_2 z⟩, hv0_2⟩

open SimpleGraph in
lemma root_mem_rooted'_of_nonempty {FR : Rooted V β ρ}
  [h : Nonempty ↑FR.toSimpleGraph_rooted.subgraph_of_support.verts] :
  .root () ∈ ↑FR.toSimpleGraph_rooted.subgraph_of_support.verts := by
  obtain ⟨_, _⟩ := @exists_origin_of_rooted'_nonempty _ _ _ _ h
  simp [support]; exact ⟨_, adj_rooted_of_root_origin ‹_›⟩

open SimpleGraph in
private def _root_.SimpleGraph.Walk.toWalk_on_unrooted
  {FR : Rooted V β ρ} {u v : WithRoot V}
  (w : FR.toSimpleGraph_rooted.Walk u v) (hw : ∀ v ∈ w.support, v ≠ ()) :=
  @Walk.toWalk_on_subgraph _ _ FR.toSimpleGraph_unrooted_sub _ _ w
    (by simp [mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root]; exact hw)
    (by simp [toSimpleGraph_unrooted_sub])

open SimpleGraph Walk in
private lemma _root_.SimpleGraph.Walk.toWalk_on_unrooted_getVert
  {FR : Rooted V β ρ} {u v : WithRoot V}
  {w : FR.toSimpleGraph_rooted.Walk u v} {hw : ∀ v ∈ w.support, v ≠ ()} :
  ∀ n, (toWalk_on_unrooted w hw).getVert n =
    ⟨w.getVert n, by
      simp [mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root]
      apply hw; simp [Walk.getVert_mem_support]
    ⟩ := by
    simp [toWalk_on_unrooted]; exact @Walk.toWalk_on_subgraph_getVert
      _ _ FR.toSimpleGraph_unrooted_sub _ _ w
      (by simpa [mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root])
      (by simp [toSimpleGraph_unrooted_sub])

open SimpleGraph Subgraph Walk in
private lemma _root_.SimpleGraph.Walk.toWalk_on_unrooted_mem_support_iff
  {FR : Rooted V β ρ} {u v x : WithRoot V}
  {w : FR.toSimpleGraph_rooted.Walk u v} {hw : ∀ v ∈ w.support, v ≠ ()} {hx : x ≠ ()} :
  ⟨x, by simpa [mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root]⟩
    ∈ (toWalk_on_unrooted w hw).support ↔ x ∈ w.support := by
  simp [toWalk_on_unrooted]; exact @Walk.toWalk_on_subgraph_mem_support_iff
    _ _ FR.toSimpleGraph_unrooted_sub _ _ x w
    (by simpa [mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root])
    (by simp [mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root]; exact hw)
    (by simp [toSimpleGraph_unrooted_sub])

open SimpleGraph Walk in
private lemma _root_.SimpleGraph.Walk.toWalk_on_unrooted_ext
  {FR : Rooted V β ρ} {u v : WithRoot V}
  {w1 w2 : FR.toSimpleGraph_rooted.Walk u v}
  {hw1 : ∀ v ∈ w1.support, v ≠ ()} {hw2 : ∀ v ∈ w2.support, v ≠ ()} :
  toWalk_on_unrooted w1 hw1 = toWalk_on_unrooted w2 hw2 → w1 = w2 := by
  intro h12; simp [toWalk_on_unrooted] at h12; exact Walk.toWalk_on_subgraph_ext h12

open SimpleGraph Walk in
private lemma _root_.SimpleGraph.Walk.toWalk_on_unrooted_isPath_iff_isPath
  {FR : Rooted V β ρ} {u v : WithRoot V}
  {w : FR.toSimpleGraph_rooted.Walk u v} {hw : ∀ v ∈ w.support, v ≠ ()} :
  w.IsPath ↔ (toWalk_on_unrooted w hw).IsPath := by
  simp [toWalk_on_unrooted]; exact @Walk.toWalk_on_subgraph_isPath_iff_isPath
    _ _ FR.toSimpleGraph_unrooted_sub _ _ w
    (by simp [mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root]; exact hw)
    (by simp [toSimpleGraph_unrooted_sub])

open SimpleGraph in
lemma mem_unrooted_support_iff_mem_rooted_support {FR : Rooted V β ρ}
  {v : V} : (↑v ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts) ↔
  ↑v ∈ FR.toSimpleGraph_unrooted.subgraph_of_support.verts := by
  constructor
  · intro hv; simp [support] at hv ⊢; obtain ⟨x, hvx⟩ := hv; match x with
    | () =>
      have := is_origin_of_adj_root_of_rooted v <| Adj.symm hvx
      simp [is_origin_def] at this; obtain ⟨⟨u, hu⟩, _⟩ := this; use u
      simp [toSimpleGraph_unrooted, toSimpleGraph_unrooted_sub]
      exact adj_rooted_of_parent_child hu
    | .node u =>
      use u; simpa [toSimpleGraph_unrooted, toSimpleGraph_unrooted_sub]
  · intro hv; simp [support] at hv ⊢; obtain ⟨x, hx, hvx⟩ := hv; match x with
    | () => simp [toSimpleGraph_unrooted_sub] at hx
    | .node u =>
      use u; simpa [toSimpleGraph_unrooted, toSimpleGraph_unrooted_sub]

open SimpleGraph ConnectedComponent in
lemma exists_origin_on_component_of_unrooted'_point {FR : Rooted V β ρ}
  (v : V) (hv : ↑v ∈ FR.toSimpleGraph_unrooted.subgraph_of_support.verts) :
  ∃ v0, FR.is_origin v0 ∧ ∃ (hv0 : ↑v0 ∈ FR.toSimpleGraph_unrooted.subgraph_of_support.verts),
  ⟨↑v0, hv0⟩ ∈ FR.toSimpleGraph_unrooted.graph_of_support.connectedComponentMk ⟨↑v, hv⟩ := by
  simp [support] at hv; rcases hv with ⟨u, hu, hvu⟩; match u with
  | () => simp [toSimpleGraph_unrooted_sub] at hu
  | .node u =>
    set s := FR.toSimpleGraph_unrooted.graph_of_support.connectedComponentMk ⟨v, hv⟩ with hs
    set s' : Set (WithRoot V) := s.supp.image (↑) with hs'
    set s'' : Set V := { v | (.node v) ∈ s' } with hs''
    simp [hs', hs, support, Reachable] at hs''
    have := FR.origin_wellfounded.has_min s'' ⟨u, by
      simp [hs'']; exact ⟨hu, ⟨v, by simp [toSimpleGraph_unrooted_sub], hvu.symm⟩,
        ⟨hvu.symm.toWalk.toWalk_on_support (by
          simp [support]; exact ⟨v, by simp [toSimpleGraph_unrooted_sub], hvu.symm⟩)
        (hv)⟩⟩⟩
    rcases this with ⟨v0, hv0_1, hv0_2⟩
    simp [hs''] at hv0_1; rcases hv0_1 with ⟨hv0_1, hv0_4, ⟨wv0v⟩⟩
    have hv0_2 : ∀ x, ¬Branching.parent_child β x v0 := by
      intro u0; by_cases hu0 : u0 ∈ s''
      · exact hv0_2 u0 hu0
      · by_contra hu0v0; apply adj_unrooted_of_parent_child at hu0v0
        have : u0 ∈ s'' := by
          simp [hs'']; use (by simp [toSimpleGraph_unrooted_sub]);
          use ⟨v0, by simp [toSimpleGraph_unrooted_sub], hu0v0⟩;
          have := hu0v0.toWalk.toWalk_on_support
            (by simp [support]; use v0, (by simp [toSimpleGraph_unrooted_sub])) (by simpa [support])
          exact ⟨this.append wv0v⟩
        contradiction
    let hv0_5 := hv0_4; rcases hv0_4 with ⟨z, hz, hzv0⟩
    match z with
    | () => simp [toSimpleGraph_unrooted, toSimpleGraph_unrooted_sub] at hzv0
    | .node z =>
      simp [toSimpleGraph_unrooted] at hzv0; use v0; simp [is_origin_def]
      exact ⟨⟨⟨z, Or.resolve_right hzv0 <| hv0_2 z⟩, hv0_2⟩,
        by simp [support]; exact hv0_5, by
        simp [s, SetLike.instMembership, SetLike.coe,
          ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, Reachable]
        exact ⟨wv0v⟩⟩

-- open SimpleGraph ConnectedComponent in
-- lemma exists_origin_on_component_of_rooted'_point {FR : Rooted V β ρ}
--   {v : V} {hv : ↑v ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts} :
--   ∃ v0, FR.is_origin v0 ∧ ∃ (hv0 : ↑v0 ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts),
--   ⟨↑v0, hv0⟩ ∈ FR.toSimpleGraph_rooted.graph_of_support.connectedComponentMk ⟨↑v, hv⟩ := by
--   simp [support] at hv; rcases hv with ⟨u, hvu⟩; match u with
--   | () => exact ⟨v, is_origin_of_adj_root_of_rooted v <| Adj.symm hvu, hv,
--     connectedComponentMk_mem⟩
--   | .node u =>
--     set s := FR.toSimpleGraph_rooted.graph_of_support.connectedComponentMk ⟨v, hv⟩ with hs
--     set s' : Set (WithRoot V) := s.supp.image (↑) with hs'
--     set s'' : Set V := { v | (.node v) ∈ s' } with hs''
--     simp [hs', hs, support, Reachable] at hs''
--     have := FR.origin_wellfounded.has_min s'' ⟨u, by
--       simp [hs'']; use ⟨v, hvu.symm⟩; exact ⟨hvu.symm.toWalk.toWalk_on_support
--         (by simp [support]; use v; exact hvu.symm)
--         (hv)⟩⟩
--     rcases this with ⟨v0, hv0_1, hv0_2⟩; let hv0_3 := hv0_1
--     simp [hs''] at hv0_1; rcases hv0_1 with ⟨hv0_1, ⟨wv0v⟩⟩
--     have hv0_2 : ∀ x, ¬Branching.parent_child β x v0 := by
--       intro u0; by_cases hu0 : u0 ∈ s''
--       · exact hv0_2 u0 hu0
--       · by_contra hu0v0; apply adj_rooted_of_parent_child at hu0v0
--         have : u0 ∈ s'' := by
--           simp [hs'']; use ⟨v0, hu0v0⟩; have := hu0v0.toWalk.toWalk_on_support
--             (by simp [support]; use v0) (by simpa [support])
--           exact ⟨this.append wv0v⟩
--         contradiction
--     rcases hv0_1 with ⟨z, hzv0⟩
--     simp [s''] at hv0_3; rw [hs'] at hv0_3
--     obtain ⟨x, _, hxv0⟩ := (Set.mem_image _ _ _).mp hv0_3
--     match z with
--     | () =>
--       exact ⟨v0, is_origin_of_adj_root_of_rooted _ <| Adj.symm ‹_›,
--         hxv0 ▸ Subtype.coe_prop x, by
--         simp [s, SetLike.instMembership, SetLike.coe,
--           ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, Reachable]
--         exact ⟨wv0v⟩⟩
--     | .node z =>
--       simp [toSimpleGraph_rooted] at hzv0; use v0; simp [is_origin_def]
--       exact ⟨⟨⟨z, Or.resolve_right hzv0 <| hv0_2 z⟩, hv0_2⟩,
--         hxv0 ▸ Subtype.coe_prop x, by
--         simp [s, SetLike.instMembership, SetLike.coe,
--           ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, Reachable]
--         exact ⟨wv0v⟩⟩

open SimpleGraph ConnectedComponent in
lemma exists_path_from_root_to_node_along_same_component
  {FR : Rooted V β ρ} (x y : WithRoot V)
  (hx' : x = ()) (hy' : ¬y = ())
  (hx : x ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts)
  (hy : y ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts) :
  ∃ w : FR.toSimpleGraph_rooted'.Walk ⟨x, hx⟩ ⟨y, hy⟩,
    w.IsPath
    ∧ (∀ z ∈ w.support.tail,  ∃ (hz' : ¬ (z : WithRoot V) = ()),
      ⟨z, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 hz'⟩
        ∈ FR.toSimpleGraph_unrooted.connectedComponentMk ↑(unroot y hy')
      ∧ ∃ (hz : ⟨z, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 hz'⟩
        ∈ FR.toSimpleGraph_unrooted.subgraph_of_support.verts),
          ⟨⟨z, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 hz'⟩, hz⟩
          ∈ FR.toSimpleGraph_unrooted'.connectedComponentMk ⟨↑(unroot y hy'), by
            have := @node_unroot _ _ hy'
            have := mem_unrooted_support_iff_mem_rooted_support.1 (this ▸ hy)
            exact this⟩)
  := by
  set y0 := unroot y hy' with hyy0
  obtain ⟨v0, hv0_1, hv0_2, hv0_3⟩ :=
    @exists_origin_on_component_of_unrooted'_point _ _ _ FR y0
    (mem_unrooted_support_iff_mem_rooted_support.mp <| node_unroot ▸ hy)
  have hy0 := (hyy0 ▸ node_unroot) ▸ hy
  have := And.right <| isTree_iff_existsUnique_path.mp <| FR.tree_unrooted'_isTree y0
    (mem_unrooted_support_iff_mem_rooted_support.mp <| hy0)
  simp only [component_unrooted', toSimpleGraph_unrooted'] at this
  specialize this ⟨⟨y0, (mem_unrooted_support_iff_mem_rooted_support.mp <| hy0)⟩,
    connectedComponentMk_mem⟩ ⟨⟨v0, hv0_2⟩, hv0_3⟩
  obtain ⟨wy0v0_tree_unrooted', hwy0v0_tree_unrooted', _⟩ := this
  have := (wy0v0_tree_unrooted'.map_isPath_iff_of_injective tree_unrooted'_hom_inj).mpr
    hwy0v0_tree_unrooted'
  set wy0v0_unrooted' := wy0v0_tree_unrooted'.map FR.tree_unrooted'_hom
  simp [tree_unrooted'_hom, toSimpleGraph_hom] at wy0v0_unrooted'
  have := (wy0v0_unrooted'.map_isPath_iff_of_injective
    FR.toSimpleGraph_unrooted.subgraph_of_support.hom_injective).mpr ‹_›
  set wy0v0_unrooted := wy0v0_unrooted'.map
    FR.toSimpleGraph_unrooted.subgraph_of_support.hom
  simp [Subgraph.hom] at wy0v0_unrooted
  have := (wy0v0_unrooted.map_isPath_iff_of_injective
    FR.toSimpleGraph_unrooted_sub.hom_injective).mpr ‹_›
  set wy0v0_rooted := wy0v0_unrooted.map FR.toSimpleGraph_unrooted_sub.hom
  simp [Subgraph.hom] at wy0v0_rooted
  have := (@Walk.toWalk_on_support_isPath_iff_isPath _ _ _ _ wy0v0_rooted hy0
    (mem_unrooted_support_iff_mem_rooted_support.mpr <| hv0_2)).mp ‹_›
  set wy0v0_rooted' := wy0v0_rooted.toWalk_on_support hy0
    (mem_unrooted_support_iff_mem_rooted_support.mpr <| hv0_2)
  have := wy0v0_rooted'.isPath_reverse_iff.mpr ‹_›
  set wv0y0_rooted' := wy0v0_rooted'.reverse
  have := (Walk.cons_isPath_iff (adj_rooted'_of_root_origin hv0_1) wv0y0_rooted').2
    ⟨‹_›, by
    simp [wv0y0_rooted', wy0v0_rooted']
    apply not_imp_not.2 Walk.toWalk_on_support_mem_support_iff.1
    simp [wy0v0_rooted]; intro h _
    simp [toSimpleGraph_unrooted_sub] at h⟩
  set wx0y0_rooted' := Walk.cons (adj_rooted'_of_root_origin hv0_1) wv0y0_rooted'
  have hyy0' := hyy0 ▸ @node_unroot _ _ hy'
  have copy_rfl_1 := Eq.symm <| @Subtype.ext _ _ ⟨x, hx⟩ ⟨(), hx' ▸ hx⟩ hx'
  have copy_rfl_2 := @Subtype.ext _ _ ⟨↑y0, hyy0' ▸ hy⟩ ⟨y, hy⟩ <| hyy0'
  have := (Walk.isPath_copy _ copy_rfl_1 copy_rfl_2).mpr this
  set wx0y0_rooted'_copy := wx0y0_rooted'.copy copy_rfl_1 copy_rfl_2
  use wx0y0_rooted'_copy, this; intro z hzw
  simp [wx0y0_rooted'_copy, wx0y0_rooted', wv0y0_rooted', wy0v0_rooted'] at hzw
  rw [Walk.toWalk_on_support_mem_support_iff] at hzw; simp [wy0v0_rooted] at hzw
  obtain ⟨hz', hzw⟩ := hzw; simp [toSimpleGraph_unrooted_sub] at hz'
  obtain ⟨z0, hzz0⟩ := hz'; have : ¬WithRoot.node z0 = .root () := by simp
  use hzz0 ▸ this; simp only [node_unroot]; constructor
  · simp [SetLike.instMembership, SetLike.coe, Reachable]
    obtain ⟨wy0z0_unrooted, _⟩ := Walk.mem_support_iff_exists_append.1 hzw
    simp [hyy0'] at wy0z0_unrooted; exact ⟨wy0z0_unrooted.reverse⟩
  · simp [wy0v0_unrooted, Subgraph.hom] at hzw; obtain ⟨hz', hzw⟩ := hzw; use hz'
    simp [SetLike.instMembership, SetLike.coe, Reachable, toSimpleGraph_unrooted',
      graph_of_support, Subgraph.coe]
    obtain ⟨wy0z0_unrooted', _⟩ := Walk.mem_support_iff_exists_append.1 hzw
    simp [hyy0', Subgraph.coe] at wy0z0_unrooted'; exact ⟨wy0z0_unrooted'.reverse⟩

open SimpleGraph ConnectedComponent in
lemma exists_path_from_node_to_node_on_same_component_unrooted'
  {FR : Rooted V β ρ} (x y : WithRoot V) (hx' : ¬x = ()) (hy' : ¬y = ())
  (hx : x ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts)
  (hy : y ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts)
  (hxy : FR.component_unrooted' (unroot x hx') (by
      have := Iff.mp <| @mem_unrooted_support_iff_mem_rooted_support _ _ _ FR (unroot x hx')
      (conv at this => arg 1; rw [node_unroot]); exact this hx)
    = FR.component_unrooted' (unroot y hy') (by
      have := Iff.mp <| @mem_unrooted_support_iff_mem_rooted_support _ _ _ FR (unroot y hy')
      (conv at this => arg 1; rw [node_unroot]); exact this hy)) :
  ∃ w : FR.toSimpleGraph_rooted'.Walk ⟨x, hx⟩ ⟨y, hy⟩, w.IsPath := by
  set x0 := unroot x hx' with hxx0
  set y0 := unroot y hy' with hyy0
  have hx0 := (hxx0 ▸ node_unroot) ▸ hx
  have hy0 := (hyy0 ▸ node_unroot) ▸ hy
  have hxx0' := hxx0 ▸ @node_unroot _ _ hx'
  have hyy0' := hyy0 ▸ @node_unroot _ _ hy'
  have := And.right <| isTree_iff_existsUnique_path.mp <| FR.tree_unrooted'_isTree y0
    (mem_unrooted_support_iff_mem_rooted_support.mp <| hy0)
  simp only [component_unrooted', toSimpleGraph_unrooted'] at this
  simp only [component_unrooted'] at hxy
  specialize this
    ⟨⟨x0, (mem_unrooted_support_iff_mem_rooted_support.mp <| hx0)⟩, hxy ▸ connectedComponentMk_mem⟩
    ⟨⟨y0, (mem_unrooted_support_iff_mem_rooted_support.mp <| hy0)⟩, connectedComponentMk_mem⟩
  obtain ⟨wx0y0_tree_unrooted', hwx0y0_tree_unrooted', _⟩ := this
  have := (wx0y0_tree_unrooted'.map_isPath_iff_of_injective tree_unrooted'_hom_inj).mpr
    hwx0y0_tree_unrooted'
  set wx0y0_unrooted' := wx0y0_tree_unrooted'.map FR.tree_unrooted'_hom
  simp [tree_unrooted'_hom, toSimpleGraph_hom] at wx0y0_unrooted'
  have := (wx0y0_unrooted'.map_isPath_iff_of_injective
    FR.toSimpleGraph_unrooted.subgraph_of_support.hom_injective).mpr ‹_›
  set wx0y0_unrooted := wx0y0_unrooted'.map
    FR.toSimpleGraph_unrooted.subgraph_of_support.hom
  simp [Subgraph.hom] at wx0y0_unrooted
  have := (wx0y0_unrooted.map_isPath_iff_of_injective
    FR.toSimpleGraph_unrooted_sub.hom_injective).mpr ‹_›
  set wx0y0_rooted := wx0y0_unrooted.map FR.toSimpleGraph_unrooted_sub.hom
  simp [Subgraph.hom] at wx0y0_rooted
  have := (@Walk.toWalk_on_support_isPath_iff_isPath _ _ _ _ wx0y0_rooted hx0 hy0).mp ‹_›
  set wx0y0_rooted' := wx0y0_rooted.toWalk_on_support hx0 hy0
  have copy_rfl_1 := @Subtype.ext _ _ ⟨↑x0, hxx0' ▸ hx⟩ ⟨x, hx⟩ <| hxx0'
  have copy_rfl_2 := @Subtype.ext _ _ ⟨↑y0, hyy0' ▸ hy⟩ ⟨y, hy⟩ <| hyy0'
  have := (Walk.isPath_copy _ copy_rfl_1 copy_rfl_2).mpr this
  set wx0y0_rooted'_copy := wx0y0_rooted'.copy copy_rfl_1 copy_rfl_2
  exact ⟨wx0y0_rooted'_copy, this⟩


open SimpleGraph in
lemma same_origin_getVert_one_of_any_walk_from_root_of_rooted {FR : Rooted V β ρ}
  {v : WithRoot V} (v_mem_unrooted : v ∈ FR.toSimpleGraph_unrooted_sub.verts)
  (vS_mem_unrooted' :
    ⟨v, v_mem_unrooted⟩ ∈ FR.toSimpleGraph_unrooted.subgraph_of_support.verts) :
  ∃ z : WithRoot V, ∃ (hz : z ≠ ()), FR.is_origin (unroot z hz)
    ∧ ∀ w : FR.toSimpleGraph_rooted.Walk () v, w.getVert 1 = z := by
    have v_ne_root := mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.1 v_mem_unrooted
    set vV := unroot v v_ne_root with heq_vV
    have heq_vVN_v : WithRoot.node vV = v := by simp [vV]
    have vVN_mem_unrooted := FR.node_mem_unrooted vV
    have heq_vVNS_vS_unrooted :
      (⟨WithRoot.node vV, vVN_mem_unrooted⟩ : ↑FR.toSimpleGraph_unrooted_sub.verts) =
      (⟨v, v_mem_unrooted⟩ : ↑FR.toSimpleGraph_unrooted_sub.verts) := by simpa
    have vVNS_mem_unrooted' := heq_vVNS_vS_unrooted ▸ vS_mem_unrooted'
    have vVN_mem_rooted' :=
      FR.mem_unrooted_support_iff_mem_rooted_support.2 vVNS_mem_unrooted'
    have v_mem_rooted' := heq_vVN_v ▸ vVN_mem_rooted'
    have : Nonempty ↑FR.toSimpleGraph_rooted.subgraph_of_support.verts :=
      ⟨v, v_mem_rooted'⟩
    obtain ⟨w, w_isPath, hw2⟩
      := FR.exists_path_from_root_to_node_along_same_component () v rfl v_ne_root
      root_mem_rooted'_of_nonempty v_mem_rooted'

    sorry

open SimpleGraph ConnectedComponent in
@[simp] lemma _root_.SimpleGraph.ConnectedComponent.mem_component_iff
  {V : Type*} {G : SimpleGraph V} {C : G.ConnectedComponent} {x : V} :
  x ∈ C ↔ x ∈ C.supp := by
  constructor <;> intro <;> simp_all only [Membership.mem, SetLike.coe, Set.Mem]

open SimpleGraph ConnectedComponent in
lemma _root_.SimpleGraph.ConnectedComponent.forall_ne_of_component_ne
  {V : Type*} {G : SimpleGraph V} {C D : G.ConnectedComponent}
  (hCD : C ≠ D) : ∀ x ∈ C, ∀ y ∈ D, x ≠ y := by
  intro x hx y hy; simp at hx hy; by_contra; exact hCD <| (‹_› ▸ hx) ▸ hy

open SimpleGraph in
lemma _root.SimpleGraph.Walk.two_le_length_of_closed_not_nil {V : Type*} {G : SimpleGraph V}
  {u : V} {w : G.Walk u u} {hw : ¬w.Nil} : 2 ≤ w.length := by
  have hw := not_imp_not.2 Walk.nil_iff_length_eq.2 hw
  by_cases w.length = 1
  · exact False.elim <| G.loopless u <| w.adj_of_length_eq_one ‹_›
  · omega

open SimpleGraph in
lemma _root_.SimpleGraph.Walk.isCycle_of_isPath_not_nil {V : Type*} {G : SimpleGraph V}
  {u : V} {w : G.Walk u u} (hw : w.IsPath) (hw' : ¬w.Nil) : w.IsCycle := by
  have := hw.isTrail
  rw [Walk.isPath_def, List.Nodup, ←(w.support.cons_head_tail w.support_ne_nil),
    List.pairwise_cons] at hw
  exact ⟨⟨this, not_imp_not.2 Walk.nil_iff_eq_nil.2 hw'⟩, hw.2⟩

open SimpleGraph ConnectedComponent in
def _root_.SimpleGraph.ConnectedComponent.walk_toSimpleGraph'
    {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) (p : G.Walk u v) : C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w ∈ C := C.mem_supp_of_adj_mem_supp hu h
    have h' : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (C.walk_toSimpleGraph' hw hv p)

-- open SimpleGraph Walk in
-- lemma _root_.SimpleGraph.Walk.map_getVert {V : Type*} {V' : Type*}
--   {G : SimpleGraph V} {G' : SimpleGraph V'} {f : G →g G'} {u v : V} {w : G.Walk u v} :
--   ∀ i, (w.map f).getVert i = f (w.getVert i) := by
--   intro i; revert u; induction i with
--   | zero => simp
--   | succ i' hi' =>
--     intro u w
--     induction w with
--     | nil => simp
--     | @cons u u' v h q h' => simp at *; exact @hi' u' q

open SimpleGraph ConnectedComponent Walk in
private lemma isTree_aux₀ {FR : Rooted V β ρ}
  [Nonempty ↑FR.toSimpleGraph_rooted.subgraph_of_support.verts]
  {x y : WithRoot V} {hx : x ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts}
  {hy : y ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts}
  {w1 w2 : FR.toSimpleGraph_rooted'.Walk ⟨x, hx⟩ ⟨y, hy⟩}
  {h1 : w1.IsPath} {h2 : w2.IsPath} {hx' : x = WithRoot.root ()}
  {hy' : ¬y = WithRoot.root ()} : w1 = w2 := by
  by_contra h12; have h12 := not_imp_not.2 Walk.ext_support h12
  -- to Rooted
  have h_isPath_w1_rooted := w1.map_isPath_of_injective
    FR.toSimpleGraph_rooted.subgraph_of_support.hom_injective h1
  have h_isPath_w2_rooted := w2.map_isPath_of_injective
    FR.toSimpleGraph_rooted.subgraph_of_support.hom_injective h2
  have h12 := (w1.support_map FR.toSimpleGraph_rooted.subgraph_of_support.hom)
    ▸ (w2.support_map FR.toSimpleGraph_rooted.subgraph_of_support.hom)
    ▸ not_imp_not.2 (@List.map_injective_iff.2
    FR.toSimpleGraph_rooted.subgraph_of_support.hom_injective _ _) h12
  set w1_rooted := w1.map FR.toSimpleGraph_rooted.subgraph_of_support.hom
  set w2_rooted := w2.map FR.toSimpleGraph_rooted.subgraph_of_support.hom
  simp [Subgraph.hom] at w1_rooted w2_rooted
  -- Drop 1 at Rooted
  have h_not_nil_w1_rooted := w1_rooted.not_nil_of_ne <| Ne.symm <| hx' ▸ hy'
  have h_not_nil_w2_rooted := w2_rooted.not_nil_of_ne <| Ne.symm <| hx' ▸ hy'
  have h_support_w1_rooted := @List.drop_one _ w1_rooted.support
    ▸ (min_eq_left <| Nat.zero_add 1
      ▸ Nat.add_one_le_of_lt <| Walk.not_nil_iff_lt_length.1 <| h_not_nil_w1_rooted)
    ▸ w1_rooted.drop_support_eq_support_drop_min 1
  have h_support_w2_rooted := @List.drop_one _ w2_rooted.support
    ▸ (min_eq_left <| Nat.zero_add 1
      ▸ Nat.add_one_le_of_lt <| Walk.not_nil_iff_lt_length.1 <| h_not_nil_w2_rooted)
    ▸ w2_rooted.drop_support_eq_support_drop_min 1
  have h12 := h_support_w1_rooted ▸ h_support_w2_rooted ▸
    not_and.1 (not_imp_not.2 (List.cons.injEq _ _ _ _).mpr (
        (w1_rooted.head_support ▸ List.cons_head_tail w1_rooted.support_ne_nil)
      ▸ (w2_rooted.head_support ▸ List.cons_head_tail w2_rooted.support_ne_nil)
      ▸ h12
    )) rfl
  have h_adj_root_w1_rooted := w1_rooted.getVert_zero
    ▸ w1_rooted.adj_getVert_succ <| Walk.not_nil_iff_lt_length.1 h_not_nil_w1_rooted
  have h_adj_root_w2_rooted := w2_rooted.getVert_zero
    ▸ w2_rooted.adj_getVert_succ <| Walk.not_nil_iff_lt_length.1 h_not_nil_w2_rooted
  have := Walk.isPath_of_isSubwalk (
    (show Walk.cons h_adj_root_w1_rooted (w1_rooted.drop 1) = w1_rooted from by
      apply Walk.ext_getVert; intro k; by_cases hk : k = 0
      · subst_vars; simp
      · simp [Walk.getVert_cons _ _ hk]; congr; omega
    ) ▸ Walk.isSubwalk_cons (w1_rooted.drop 1) ‹_›) ‹_›
  have := Walk.isPath_of_isSubwalk (
    (show Walk.cons h_adj_root_w2_rooted (w2_rooted.drop 1) = w2_rooted from by
      apply Walk.ext_getVert; intro k; by_cases hk : k = 0
      · subst_vars; simp
      · simp [Walk.getVert_cons _ _ hk]; congr; omega
    ) ▸ Walk.isSubwalk_cons (w2_rooted.drop 1) ‹_›) ‹_›
  simp [Walk.isPath_def, List.Nodup] at h_isPath_w1_rooted h_isPath_w2_rooted
  have h_isPath_w1_rooted :=
    (w1_rooted.head_support ▸ List.cons_head_tail w1_rooted.support_ne_nil)
    ▸ h_isPath_w1_rooted
  have h_isPath_w2_rooted :=
    (w2_rooted.head_support ▸ List.cons_head_tail w2_rooted.support_ne_nil)
    ▸ h_isPath_w2_rooted
  simp [hx'] at h_isPath_w1_rooted h_isPath_w2_rooted
  conv at h_isPath_w1_rooted => left; ext; arg 2; congr; rw [eq_comm]
  conv at h_isPath_w2_rooted => left; ext; arg 2; congr; rw [eq_comm]
  set w1_rooted_tail := w1_rooted.drop 1
  set w2_rooted_tail := w2_rooted.drop 1
  rw [←h_support_w1_rooted] at h_isPath_w1_rooted
  rw [←h_support_w2_rooted] at h_isPath_w2_rooted
  clear h_not_nil_w1_rooted h_not_nil_w2_rooted
    h_adj_root_w1_rooted h_adj_root_w2_rooted
    h_support_w1_rooted h_support_w2_rooted
  -- to Unroot
  have := (@toWalk_on_unrooted_isPath_iff_isPath _ _ _ _ _ _
    w1_rooted_tail h_isPath_w1_rooted.1).1 ‹_›
  have := (@toWalk_on_unrooted_isPath_iff_isPath _ _ _ _ _ _
    w2_rooted_tail h_isPath_w2_rooted.1).1 ‹_›
  have h1_origin := is_origin_getVert_one_of_walk_from_root_of_rooted
    (w1_rooted.copy hx' rfl)
    <| @Walk.not_nil_of_ne _ _ _ _ (w1_rooted.copy hx' rfl) (Ne.symm hy')
  simp only [Walk.getVert_copy] at h1_origin
  have h2_origin := is_origin_getVert_one_of_walk_from_root_of_rooted
    (w2_rooted.copy hx' rfl)
    <| @Walk.not_nil_of_ne _ _ _ _ (w2_rooted.copy hx' rfl) (Ne.symm hy')
  simp only [Walk.getVert_copy] at h2_origin
  by_cases h12' : ¬ w1_rooted.getVert 1 = w2_rooted.getVert 1
  · set w1_unrooted := w1_rooted_tail.toWalk_on_unrooted h_isPath_w1_rooted.1
    set w2_unrooted := w2_rooted_tail.toWalk_on_unrooted h_isPath_w2_rooted.1
    have := origin_not_reachable_unrooted _ _ h1_origin h2_origin
      (by by_contra; exact h12' <| @unroot_ext _ _ _ _ _ ‹_›)
    simp [Reachable] at this
    exact this.false <| w1_unrooted.append <| w2_unrooted.reverse
  · simp only [not_not] at h12'
    have h12 := not_imp_not.2 (@toWalk_on_unrooted_ext _ _ _ _ _ _
      (w1_rooted_tail.copy h12' rfl) w2_rooted_tail
      (Walk.support_copy w1_rooted_tail h12' rfl ▸ h_isPath_w1_rooted.1)
      h_isPath_w2_rooted.1) <| not_imp_not.2 Walk.ext_support_iff.2
      <| Walk.support_copy w1_rooted_tail h12' rfl ▸ h12
    have := (@toWalk_on_unrooted_isPath_iff_isPath _ _ _ _ _ _
      (w1_rooted_tail.copy h12' rfl) (by have := h_isPath_w1_rooted.1; simpa)).1
      <| (Walk.isPath_copy w1_rooted_tail h12' rfl).2 ‹_›
    set w1_unrooted := toWalk_on_unrooted (w1_rooted_tail.copy h12' rfl)
      <| Walk.support_copy w1_rooted_tail h12' rfl ▸ h_isPath_w1_rooted.1
    set w2_unrooted := toWalk_on_unrooted w2_rooted_tail h_isPath_w2_rooted.1
    -- to Component
    have : w2_rooted.getVert 1 ≠ () := by
      have := node_unroot ▸ ne_root_of_is_origin h2_origin; exact this
    have := (@Walk.toWalk_on_component_unrooted_isPath_iff_isPath _ _ _ _ _ _
      (unroot (w2_rooted.getVert 1) ‹_›) w1_unrooted (by simp [component_unrooted])
      (by simp [component_unrooted, Reachable]; exact ⟨w2_unrooted.reverse⟩)).1 ‹_›
    have := (@Walk.toWalk_on_component_unrooted_isPath_iff_isPath _ _ _ _ _ _
      (unroot (w2_rooted.getVert 1) ‹_›) w2_unrooted (by simp [component_unrooted])
      (by simp [component_unrooted, Reachable]; exact ⟨w2_unrooted.reverse⟩)).1 ‹_›
    -- have := @Walk.toWalk_on_component_unrooted_mem_support_iff _ _ _ _ _ _
    have h12 := not_imp_not.2 (@Walk.toWalk_on_component_unrooted_ext
      _ _ _ _ _ _ (unroot (w2_rooted.getVert 1) ‹_›) w1_unrooted w2_unrooted
      (by simp [component_unrooted])
      (by simp [component_unrooted, Reachable]; exact ⟨w2_unrooted.reverse⟩)) h12
    set w1_unrooted_tree := w1_unrooted.toWalk_on_component_unrooted
      (unroot (w2_rooted.getVert 1) ‹_›)
      (by simp [component_unrooted])
      (by simp [component_unrooted, Reachable]; exact ⟨w2_unrooted.reverse⟩)
    set w2_unrooted_tree := w2_unrooted.toWalk_on_component_unrooted
      (unroot (w2_rooted.getVert 1) ‹_›)
      (by simp [component_unrooted])
      (by simp [component_unrooted, Reachable]; exact ⟨w2_unrooted.reverse⟩)
    have := w1_unrooted_tree.getVert 0
    have := w1_unrooted_tree.getVert_zero
    have := @ExistsUnique.unique _ _ ((isTree_iff_existsUnique_path.1
      <| FR.tree_unrooted_isTree (unroot (w2_rooted.getVert 1) ‹_›)).2
      ⟨⟨w2_rooted.getVert 1, by
        apply mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2
        assumption⟩, by simp [component_unrooted]⟩
      ⟨⟨y, by
        apply mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2
        assumption⟩, by simp [component_unrooted, Reachable]; exact ⟨w2_unrooted.reverse⟩⟩)
      w1_unrooted_tree w2_unrooted_tree ‹_› ‹_›
    exact h12 this

open SimpleGraph ConnectedComponent in
lemma isTree (FR : Rooted V β ρ) [Nonempty ↑FR.toSimpleGraph_rooted.subgraph_of_support.verts] :
  IsTree FR.toSimpleGraph_rooted' := by
  rw [isTree_iff_existsUnique_path]; constructor
  · assumption
  · by_contra h1; simp only [not_forall] at h1
    rcases h1 with ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩; contrapose hxy
    clear hxy; simp only [not_not]; apply existsUnique_of_exists_of_unique
    · by_cases hx' : x = ()
      · by_cases hy' : y = ()
        · rw [←hy'] at hx'
          use (@Walk.nil _ FR.toSimpleGraph_rooted' ⟨x, hx⟩).copy rfl (by congr)
          simp only [subgraph_of_support, Walk.isPath_copy, Walk.isPath_iff_eq_nil]
        · obtain ⟨w, hw, _⟩ := exists_path_from_root_to_node_along_same_component x y hx' hy' hx hy
          exact ⟨w, hw⟩
      · by_cases hy' : y = ()
        · obtain ⟨w, hw, _⟩ := exists_path_from_root_to_node_along_same_component y x hy' hx' hy hx
          have := w.isPath_reverse_iff.mpr ‹_›; set w' := w.reverse; use w'
        · by_cases hxy : FR.component_unrooted' (unroot x hx') (by
              have := Iff.mp <| @mem_unrooted_support_iff_mem_rooted_support _ _ _ FR (unroot x hx')
              (conv at this => arg 1; rw [node_unroot]); exact this hx)
            = FR.component_unrooted' (unroot y hy') (by
              have := Iff.mp <| @mem_unrooted_support_iff_mem_rooted_support _ _ _ FR (unroot y hy')
              (conv at this => arg 1; rw [node_unroot]); exact this hy)
          · exact exists_path_from_node_to_node_on_same_component_unrooted' x y hx' hy' hx hy hxy
          · simp only [component_unrooted'] at hxy
            obtain ⟨wx, hwx, hwx'⟩ := exists_path_from_root_to_node_along_same_component
              () x rfl hx' root_mem_rooted'_of_nonempty hx
            obtain ⟨wy, hwy, hwy'⟩ := exists_path_from_root_to_node_along_same_component
              () y rfl hy' root_mem_rooted'_of_nonempty hy
            set wxy := wx.reverse.append wy; use wxy; simp [Walk.isPath_def, List.Nodup,
              wxy, Walk.support_append, List.pairwise_append, List.pairwise_reverse]; constructor
            · simp [Walk.isPath_def, List.Nodup] at hwx; conv => arg 1; ext; ext; rw [eq_comm]
              exact hwx
            · constructor
              · simp [Walk.isPath_def, List.Nodup] at hwy
                apply List.Pairwise.tail at hwy; exact hwy
              · intro a ha hawx b hb hbwy
                rw [←(List.cons_head_tail <| List.ne_nil_of_mem hawx)] at hawx
                simp at hawx; rcases hawx with (hawx|hawx)
                · simp [Walk.isPath_def, List.Nodup] at hwy
                  rw [←(List.cons_head_tail <| List.ne_nil_of_mem
                    <| List.mem_of_mem_tail hbwy)] at hwy
                  simp only [List.pairwise_cons, Walk.head_support] at hwy
                  have := hwy.left ⟨b, hb⟩ hbwy; simp at this; exact Eq.symm hawx ▸ this
                · specialize hwx' ⟨a, ha⟩ hawx; obtain ⟨_, _, _, hax⟩ := hwx'
                  specialize hwy' ⟨b, hb⟩ hbwy; obtain ⟨_, _, _, hbx⟩ := hwy'
                  simp only [node_unroot] at hax hbx hxy
                  have := forall_ne_of_component_ne hxy _ hax _ hbx; simp at this; exact this
    · intro w1 w2 h1 h2
      have h₀ := fun (w1 w2 : FR.toSimpleGraph_rooted'.Walk ⟨x, hx⟩ ⟨y, hy⟩)
        (hw1 : w1.Nil) (hw2 : ¬ w2.Nil) (h2 : w2.IsPath) => show False from by
        have hw1 := w1.nil_iff_length_eq.1 hw1
        have := w1.getVert_zero
        have := w1.getVert_length
        have : x = y := by aesop
        have hw2 := not_imp_not.2 w2.nil_iff_length_eq.2 hw2
        have := w2.getVert_length
        have := w2.getVert_zero
        have := w2.getVert_eq_support_getElem (by omega : 0 ≤ w2.length)
        have := w2.getVert_eq_support_getElem (by omega : w2.length ≤ w2.length)
        have : w2.support[0] = w2.support[w2.length] := by aesop
        simp [Walk.isPath_def, List.Nodup, List.pairwise_iff_getElem] at h2
        exact h2 0 w2.length (by omega) (by omega) (by omega) ‹_›
      by_cases ¬(¬ w1.Nil ∧ ¬ w2.Nil)
      · by_cases hw1 : w1.Nil
        · by_cases hw2 : w2.Nil
          · have hw1 := w1.nil_iff_length_eq.1 hw1
            have := w1.getVert_zero
            have := w1.getVert_length
            have : x = y := by aesop
            subst_vars
            apply Walk.ext_support
            have := w1.nil_iff_support_eq
            have := w2.nil_iff_support_eq
            aesop
          · exact False.elim <| h₀ w1 w2 hw1 hw2 h2
        · have hw2 : w2.Nil := by aesop
          exact False.elim <| h₀ w2 w1 hw2 hw1 h1
      · have hw1 : ¬ w1.Nil := by aesop
        have hw2 : ¬ w2.Nil := by aesop
        by_cases hx' : x = ()
        · by_cases hy' : y = ()
          · subst_vars; simp at h1 h2; exact h2 ▸ h1
          · exact @isTree_aux₀ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hx' hy'
        · by_cases hy' : y = ()
          · have h12 := @isTree_aux₀ _ _ _ _ _ y x hy hx w1.reverse w2.reverse
              (by simpa) (by simpa) hy' hx'; apply Walk.ext_getVert_le_length
            · exact w1.length_reverse ▸ w2.length_reverse ▸ Walk.length_eq_of_eq h12
            · intro k hk
              have h12' := w1.length_reverse ▸ w2.length_reverse ▸ Walk.length_eq_of_eq h12
              have h12'' := Walk.ext_getVert_iff.2 h12 (w1.length - k)
              conv at h12'' => arg 2; rw [h12']
              simp [Walk.getVert_reverse] at h12''
              have := (by omega : w1.length - (w1.length - k) = k)
              conv at h12'' => left; rw[this]
              have := (by omega : w2.length - (w2.length - k) = k)
              conv at h12'' => right; rw[this]
              exact h12''
          · -- ## Basics For x
            have := FR.exists_path_from_root_to_node_along_same_component
              () x rfl hx' root_mem_rooted'_of_nonempty hx
            obtain ⟨w0x_rooted', hw0x_rooted', hw0x'_rooted'⟩ := this
            have w0x_rooted'_pos_len : 0 < w0x_rooted'.length :=
              w0x_rooted'.not_nil_iff_lt_length.1 <| w0x_rooted'.not_nil_of_ne
              (not_imp_not.2 (@Subtype.mk.inj _ _ (.root ()) root_mem_rooted'_of_nonempty x hx)
                <| Ne.symm hx')
            set x0_rooted := w0x_rooted'.support.tail[0]'
              (by simp; exact w0x_rooted'_pos_len) with heq_x0
            obtain ⟨x0, hx0⟩ := x0_rooted
            have heq_x0' : ⟨x0, hx0⟩ = w0x_rooted'.getVert 1 := by
              simp at heq_x0
              exact w0x_rooted'.getVert_eq_support_getElem (by omega : 1 ≤ w0x_rooted'.length)
                ▸ heq_x0
            specialize hw0x'_rooted' ⟨x0, hx0⟩ (List.mem_of_getElem <| Eq.symm heq_x0)
            obtain ⟨hw0x'_rooted', hx0x, hx0', hx0x'⟩ := hw0x'_rooted'
            simp [node_unroot, Reachable] at *
            obtain ⟨wx0x_unrooted⟩ := hx0x; obtain ⟨wx0x_unrooted'⟩ := hx0x'
            have heq''_x0 : (w0x_rooted'.map
              FR.toSimpleGraph_rooted.subgraph_of_support.hom).getVert 1 = x0 := by
              simp [Subgraph.hom, ←heq_x0']
            have hx0'' := is_origin_getVert_one_of_walk_from_root_of_rooted
              (w0x_rooted'.map FR.toSimpleGraph_rooted.subgraph_of_support.hom)
              (by simp [Walk.nil_iff_length_eq]; omega)
            conv at hx0'' => congr; congr; rw[heq''_x0]
            simp at hx0' hw0x'_rooted'
            -- ## Basics For y
            have := FR.exists_path_from_root_to_node_along_same_component
              () y rfl hy' root_mem_rooted'_of_nonempty hy
            obtain ⟨w0y_rooted', hw0y_rooted', hw0y'_rooted'⟩ := this
            have w0y_rooted'_pos_len : 0 < w0y_rooted'.length :=
              w0y_rooted'.not_nil_iff_lt_length.1 <| w0y_rooted'.not_nil_of_ne
              (not_imp_not.2 (@Subtype.mk.inj _ _ (.root ()) root_mem_rooted'_of_nonempty y hy)
                <| Ne.symm hy')
            set y0_rooted := w0y_rooted'.support.tail[0]'
              (by simp; exact w0y_rooted'_pos_len) with heq_y0
            obtain ⟨y0, hy0⟩ := y0_rooted
            have heq_y0' : ⟨y0, hy0⟩ = w0y_rooted'.getVert 1 := by
              simp at heq_y0
              exact w0y_rooted'.getVert_eq_support_getElem (by omega : 1 ≤ w0y_rooted'.length)
                ▸ heq_y0
            specialize hw0y'_rooted' ⟨y0, hy0⟩ (List.mem_of_getElem <| Eq.symm heq_y0)
            obtain ⟨hw0y'_rooted', hy0y, hy0', hy0y'⟩ := hw0y'_rooted'
            simp [node_unroot, Reachable] at *
            obtain ⟨wy0y_unrooted⟩ := hy0y; obtain ⟨wy0y_unrooted'⟩ := hy0y'
            have heq''_y0 : (w0y_rooted'.map
              FR.toSimpleGraph_rooted.subgraph_of_support.hom).getVert 1 = y0 := by
              simp [Subgraph.hom, ←heq_y0']
            have hy0'' := is_origin_getVert_one_of_walk_from_root_of_rooted
              (w0y_rooted'.map FR.toSimpleGraph_rooted.subgraph_of_support.hom)
              (by simp [Walk.nil_iff_length_eq]; omega)
            conv at hy0'' => congr; congr; rw[heq''_y0]
            simp at hy0' hw0y'_rooted'
            -- ## some walk from x to y not passing root => x ↔ y
            have h₀ := fun (w : FR.toSimpleGraph_rooted'.Walk ⟨x, hx⟩ ⟨y, hy⟩)
              (hw : ⟨(), root_mem_rooted'_of_nonempty⟩ ∉ w.support) =>
                show ∀ v ∈ (w.map FR.toSimpleGraph_rooted.subgraph_of_support.hom).support,
                ¬ v = () from by
                simp only [Walk.mem_support_iff_exists_getVert, Walk.getVert_map,
                  Walk.length_map, Subgraph.hom, DFunLike.coe];
                simp only [Walk.mem_support_iff_exists_getVert, not_exists, not_and'] at hw
                intro x ⟨n, hn1, hn2⟩;
                have h := @Subtype.property _
                  (fun x => x ∈ FR.toSimpleGraph_rooted.subgraph_of_support.verts) (w.getVert n)
                have := Eq.trans (Eq.symm <| Subtype.coe_eta (w.getVert n) h)
                  <| (eq_iff_iff.1 <| Subtype.mk.injEq ↑(w.getVert n) h x (hn1 ▸ h)).2 hn1
                exact not_imp_not.2 (eq_iff_iff.1 <| Subtype.mk.injEq
                  x (hn1 ▸ h) (.root ()) root_mem_rooted'_of_nonempty).2 <| this ▸ hw n hn2
            have h₁ := fun (w : FR.toSimpleGraph_rooted'.Walk ⟨x, hx⟩ ⟨y, hy⟩)
              (hw : ⟨(), root_mem_rooted'_of_nonempty⟩ ∉ w.support) =>
                show FR.toSimpleGraph_unrooted.Reachable
                ⟨x, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 hx'⟩
                ⟨y, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 hy'⟩ from ⟨(w.map
                FR.toSimpleGraph_rooted.subgraph_of_support.hom).toWalk_on_unrooted <| h₀ w hw⟩
            have := fun (h :
                ∃ w : FR.toSimpleGraph_rooted'.Walk ⟨x, hx⟩ ⟨y, hy⟩,
                  w.IsPath ∧ ¬w.Nil ∧ ⟨(), root_mem_rooted'_of_nonempty⟩ ∈ w.support
              ) => show ∀ w : FR.toSimpleGraph_rooted'.Walk ⟨x, hx⟩ ⟨y, hy⟩,
                  w.IsPath ∧ ¬w.Nil →
                    ⟨(), root_mem_rooted'_of_nonempty⟩ ∈ w.support from by
                /- We first have a walk w from x to y that is a path, a non-nil walk,
                and passes the root -/
                obtain ⟨w, hw1, hw3, hw2⟩ := h

                /- We want to prove that all walks from x to y, as long as it is a path,
                and a non-nil walk, it should also pass the root. We prove by contrary
                that if there exsits such a walk w' that is a path, a non-nil walk, but
                does not pass the root, then there should be a contradiction. The
                contradiction will be constructed as follows: `(1)` There is a walk on
                the unrooted graph from x to y denoted by `wxy_unrooted` (constructed
                from the previous lemma `h₁` using the fact that w' does not pass the
                root); `(2)` Then from the w (on the rooted support graph, which passes
                the root, and is also a non-nil path), we construct two walks on the
                unrooted graph, one from x to the origin just before the root on w,
                denoted by `wxx0'_unrooted`, the other from y to the origin just after
                the root on w, denoted by `wyy0'_unrooted`, we need to prove that (2a)
                these two origin `x0'` and `y0'` are not the same, and that (2b) these
                two subwalks are all paths which means they do not have duplicate
                vertices and most importantly, do not pass the root; `(3)` We construct
                a walk `wx0'y0'_unrooted` by sequencing reverse of `wxx0'_unrooted`,
                `wxy_unrooted` and `wyy0'_unrooted`, and then using the previous lemma
                `origin_not_reachable_unrooted` to get to a contradiction (since the two
                origins `x0'` and `y0'` are not the same one). -/
                by_contra this; simp at this; obtain ⟨w', hw'1, hw'3, hw'2⟩ := this

                /- We first get the walk on the unrooted graph from x to y. -/
                obtain ⟨wxy_unrooted⟩ := h₁ w' hw'2

                /- We can actually construct a walk `wx0y0_unrooted` from the previous
                basic facts. But in this way, we need prove that `x0` and `y0` are on
                the `w` and that they are not the same. We actually need a lemma saying
                that every walk from x to the root should passes the `x0` just before
                the root. -/
                have wx0y0_unrooted := (wx0x_unrooted.append wxy_unrooted).append
                  wy0y_unrooted.reverse


                obtain ⟨n, hwn1, hwn2⟩ := Walk.mem_support_iff_exists_getVert.1 hw2
                have := ((w.take n).copy rfl hwn1).reverse
                have hw4 := is_origin_getVert_one_of_walk_from_root_of_rooted
                  (((w.take n).copy rfl hwn1).reverse.map
                    FR.toSimpleGraph_rooted.subgraph_of_support.hom)
                  (by
                    simp [Subgraph.hom, Walk.nil_iff_length_eq]
                    conv => right; simp [←Walk.nil_iff_length_eq]
                    by_contra this; simp [-not_and, not_and_or] at this
                    rcases this with (this|this)
                    · simp [this] at hwn1; exact hx' hwn1
                    · exact hw3 this )
                simp [Subgraph.hom,
                  (by omega : min n w.length - 1 = n - 1)] at hw4
                have hw5 := is_origin_getVert_one_of_walk_from_root_of_rooted
                  (((w.drop n).copy hwn1 rfl).map
                    FR.toSimpleGraph_rooted.subgraph_of_support.hom)
                  (by
                    simp [Subgraph.hom, Walk.nil_iff_length_eq]; by_contra
                    have := Subtype.mk.inj
                      <| ((by omega : w.length = n) ▸ hwn1) ▸ w.getVert_length
                    exact Ne.symm hy' this )
                simp [Subgraph.hom] at hw5

                have : x0 ≠ y0 := sorry
                sorry
            by_cases ⟨(), root_mem_rooted'_of_nonempty⟩ ∈ w1.support ∧
              ⟨(), root_mem_rooted'_of_nonempty⟩ ∈ w2.support
            · sorry
            ·
              sorry


-- have :
          --   FR.toSimpleGraph_unrooted.connectedComponentMk
          --     ⟨x, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 ‹_›⟩ =
          --   FR.toSimpleGraph_unrooted.connectedComponentMk
          --     ⟨y, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 ‹_›⟩ := by
          --     sorry


          -- by_cases h : ⟨(), root_mem_rooted'_of_nonempty⟩ ∉ w1.support ∨
          --   ⟨(), root_mem_rooted'_of_nonempty⟩ ∉ w2.support
          -- · by_cases h' : ∃ z,
          --     ⟨x, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 ‹_›⟩
          --       ∈ FR.component_unrooted z ∧
          --     ⟨y, mem_toSimpleGraph_unrooted_sub_verts_iff_ne_root.2 ‹_›⟩
          --       ∈ FR.component_unrooted z
          --   · by_contra h12; have h12 := not_imp_not.2 Walk.ext_support h12
          --     obtain ⟨z, hxz, hyz⟩ := h'
          --     -- to Rooted
          --     have h_isPath_w1_rooted := w1.map_isPath_of_injective
          --       FR.toSimpleGraph_rooted.subgraph_of_support.hom_injective h1
          --     have h_isPath_w2_rooted := w2.map_isPath_of_injective
          --       FR.toSimpleGraph_rooted.subgraph_of_support.hom_injective h2
          --     have h12 := (w1.support_map FR.toSimpleGraph_rooted.subgraph_of_support.hom)
          --       ▸ (w2.support_map FR.toSimpleGraph_rooted.subgraph_of_support.hom)
          --       ▸ not_imp_not.2 (@List.map_injective_iff.2
          --       FR.toSimpleGraph_rooted.subgraph_of_support.hom_injective _ _) h12
          --     set w1_rooted := w1.map FR.toSimpleGraph_rooted.subgraph_of_support.hom
          --     set w2_rooted := w2.map FR.toSimpleGraph_rooted.subgraph_of_support.hom
          --     simp [Subgraph.hom] at w1_rooted w2_rooted
          --     have w1_unrooted_tree :=
          --       (w1_rooted.toWalk_on_unrooted (by sorry)).toWalk_on_component_unrooted z hxz hyz
          --     have w2_unrooted_tree :=
          --       (w2_rooted.toWalk_on_unrooted (by sorry)).toWalk_on_component_unrooted z hxz hyz
          --     sorry
          --   · sorry
          -- · sorry


end Rooted

namespace Standard
variable {V : Type*} [DecidableEq V] {β : V → ℕ} {ρ : Unit → ℕ} (FS : Standard V β ρ)

instance : CoeOut (Standard V β ρ) (Rooted V (fun v => Fin (β v)) (fun r => Fin (ρ r))) where
  coe FS := FS.toRooted

instance instNonemptyForestStandard_SubgraphSupport :
  Nonempty FS.toSimpleGraph_rooted.support := sorry

instance instNonemptyForestStandard_SubgraphSupportVerts :
  Nonempty ↑FS.toSimpleGraph_rooted.subgraph_of_support.verts := ⟨⟨(), by
    simp []
    sorry
  ⟩⟩

-- protected def _root_.Branching.Forest.RootedSupport (V : Type*) (β : V → Type*) (F : Forest V β)
--   := ↑(Forest.toRooted V β F).toSimpleGraph_rooted.subgraph_of_support.verts

-- protected def _root_.Branching.Forest.toRootedSimpleGraph (F : Forest V β)
--   := F.toRooted.toSimpleGraph_rooted'

variable (FS : Forest.Standard ℕ (fun _ => 2) fun _ => 2)
#check FS.isAcyclic
#check 1 ᵖ< 2
end Standard

end Forest

end Branching



          -- have : w1.Nil := by
          --   by_contra hw1;
          --   have := w1.isCycle_of_isPath_not_nil h1 hw1
          --   have := this.three_le_length

          --   -- have h_list_map := w1.support_map FR.toSimpleGraph_rooted.subgraph_of_support.hom
          --   -- have := (w1.map_isCycle_iff_of_injective
          --   --   FR.toSimpleGraph_rooted.subgraph_of_support.hom_injective).2 ‹_›
          --   -- have := this.three_le_length
          --   -- have := w1.length_map FR.toSimpleGraph_rooted.subgraph_of_support.hom
          --   -- have := w1.support.length_map FR.toSimpleGraph_rooted.subgraph_of_support.hom
          --   -- set w1_rooted := w1.map FR.toSimpleGraph_rooted.subgraph_of_support.hom
          --   -- simp [Subgraph.hom] at w1_rooted
          --   -- have := w1.getVert_eq_support_getElem (by omega : 1 ≤ w1.length)
          --   -- have := w1.getVert_eq_support_getElem (by omega : w1.length - 1 ≤ w1.length)
          --   -- have := w1_rooted.getVert_eq_support_getElem (by omega : 1 ≤ w1_rooted.length)
          --   -- have := w1_rooted.getVert_eq_support_getElem
          --   --   (by omega : w1_rooted.length - 1 ≤ w1_rooted.length)
          --   -- conv at this => arg 1; arg 2; arg 1; rw[(by omega : w1_rooted.length = w1.length)]
          --   -- conv at this => arg 2; arg 2; arg 1; rw[(by omega : w1_rooted.length = w1.length)]

          --   have hr1 := w1.adj_getVert_succ (by omega : 0 < w1.length)
          --   have hr2 := w1.adj_getVert_succ (by omega : w1.length - 1 < w1.length)
          --   simp [(by omega : w1.length - 1 + 1 = w1.length), toSimpleGraph_rooted',
          --     graph_of_support, Subgraph.coe] at hr1 hr2
          --   have := is_origin_of_adj_root_of_rooted₀ hr1
          --   have := is_origin_of_adj_root_of_rooted₀ <| Adj.symm hr2

          --   set w1'_rooted' := ((w1.take (w1.length - 1)).drop 1).copy
          --     (show (w1.take (w1.length - 1)).getVert 1 = w1.getVert 1 from by
          --       simp; congr; omega ) rfl
          --   have : ⟨(), root_mem_rooted'_of_nonempty⟩  ∉ w1'_rooted'.support := by
          --     unfold w1'_rooted'
          --     sorry





          --   sorry
-/
