import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.Truncation
import Mathlib.Probability.RandomGraph.Tree.RootedLabeledTree.LocallyFinite
import Mathlib.Topology.MetricSpace.Ultra.Basic

open TreeNode ENNReal NNReal ENat Cardinal

namespace RLTree

variable {T T1 T2 : 𝕋₀} {v : 𝕍}

-- ## heightCongr

noncomputable def heightCongr (T1 T2 : 𝕋₀) : ℕ∞ :=
  (⨆ (n : ℕ) (_ : T1↾(n) = T2↾(n)), n : WithTop ℕ)

scoped[RLTree] notation "‖" T1 ", " T2 "‖ₕ" => heightCongr T1 T2

@[simp] lemma heightCongr_comm {T1 T2 : 𝕋₀} : ‖T1, T2‖ₕ = ‖T2, T1‖ₕ := by
  simp [heightCongr, eq_comm]

lemma ext_of_top_heightCongr {T1 T2 : 𝕋₀} (h : ‖T1, T2‖ₕ = ⊤) : T1 = T2 := by
  simp only [heightCongr] at h
  have h' := (@iSup₂_eq_top (WithTop ℕ) ℕ _ _ (fun n => fun _ => n)).1 h
  apply ext_of_truncation; intro n; obtain ⟨m, hm, hnm⟩ := h' n (by simp)
  have := ENat.coe_lt_coe.1 hnm
  have := congrArg (fun T : 𝕋₀ => T↾(n)) hm
  simp only [truncation_truncation, (show min m n = n from by omega)] at this; exact this

@[simp] lemma heightCongr_self_eq_top {T : 𝕋₀} : ‖T, T‖ₕ = ⊤ := by
  simp only [heightCongr, iSup_pos]; apply (@iSup_eq_top (WithTop ℕ) ℕ _ _).2; intro n hn
  set n' := n.untop (by aesop) with hn'; have := (WithTop.untop_eq_iff _).1 (Eq.symm hn')
  use n' + 1; rw [this]; exact WithTop.coe_lt_coe.2 (show n' < n' + 1 from by omega)

@[simp] lemma heightCongr_apply {T T' : 𝕋₀} (n : ℕ) (hn : n ≤ ‖T, T'‖ₕ) : T↾(n) = T'↾(n) := by
  by_cases h : ‖T, T'‖ₕ = ⊤
  · exact congrArg (fun T => T↾(n)) <| ext_of_top_heightCongr h
  · by_cases n = 0
    · subst_vars; simp
    · have : n - 1 < ‖T, T'‖ₕ := by
        obtain ⟨n', hn'⟩ := WithTop.ne_top_iff_exists.1 h
        rw [←hn'] at ⊢ hn; simp only [ENat.some_eq_coe, Nat.cast_le] at ⊢ hn
        apply ENat.coe_lt_coe.2; omega
      rw [heightCongr, iSup_subtype', iSup] at hn this
      obtain ⟨n', hn'1, hn'2⟩ := (@lt_sSup_iff (WithTop ℕ) _ _ _).1 this
      simp only [Set.mem_range, Subtype.exists, exists_prop] at hn'1
      obtain ⟨n'', hn'3, hn'4⟩ := hn'1
      simp only [← hn'4] at hn'2; have := ENat.coe_lt_coe.1 hn'2
      have := congrArg (fun T => T↾(n)) hn'3
      simp only [truncation_truncation, show min n'' n = n from by omega] at this; exact this

@[simp] lemma heightCongr_apply_iff {T T' : 𝕋₀} (n : ℕ) :
  n ≤ ‖T, T'‖ₕ ↔ T↾(n) = T'↾(n) := by
  constructor
  · exact heightCongr_apply n
  · intro hn; rw [heightCongr, iSup_subtype', iSup]
    apply (@le_sSup_iff (WithTop ℕ) _ _ _).2; simp only [upperBounds, Set.mem_range,
      Subtype.exists, exists_prop, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Set.mem_setOf_eq]
    intro m hm; exact hm n hn

lemma heightCongr_ultra (T1 T2 T3 : 𝕋₀) :
  min ‖T1, T2‖ₕ ‖T2, T3‖ₕ ≤ ‖T1, T3‖ₕ := by
  by_cases h' : ‖T1, T3‖ₕ = ⊤
  · simp [*]
  · by_contra h; simp only [inf_le_iff, not_or, not_le] at h
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
      (m' + 1) (fun n => fun _ => (n : WithTop ℕ)) (m' + 1) ‹_› (by simp); simp only at this
    have heq := @rfl _ ‖T1, T3‖ₕ; conv at heq => left; simp [heightCongr]
    conv at this => rhs; rw [heq, ←hm, hm'']
    have := ENat.coe_le_coe.1 this; simp at this

-- ## treeDist

noncomputable def treeDist (T1 T2 : 𝕋₀) : ℝ :=
  ((1 + (‖T1, T2‖ₕ : ℝ≥0∞))⁻¹).toReal

scoped[RLTree] notation "‖" T1 ", " T2 "‖ₜ₁" => treeDist T1 T2

lemma ext_of_zero_treeDist {T1 T2 : 𝕋₀} (h12 : ‖T1, T2‖ₜ₁ = 0) : T1 = T2 := by
  simp only [treeDist, ENNReal.toReal, ENNReal.toNNReal, NNReal.coe_eq_zero,
    WithTop.untopD_eq_self_iff, WithTop.coe_zero] at h12
  rcases h12 with (h12|h12)
  · have h12 := ENNReal.inv_eq_zero.1 h12; simp only [add_eq_top, ENNReal.one_ne_top,
    toENNReal_eq_top, false_or] at h12
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
  simp only [le_sup_iff]; by_contra h; simp only [not_or, not_le] at h
  have := heightCongr_ultra T1 T2 T3; contrapose this; simp only [inf_le_iff, not_or, not_le]
  constructor
  · by_contra h'; simp only [not_lt] at h'; have := treeDist_mono h'
    conv at this => left; rw [@treeDist_eq_aux T1 T2]
    conv at this => right; rw [@treeDist_eq_aux T1 T3]
    simp only [neg_le_neg_iff] at this; exact lt_iff_not_ge.1 h.1 this
  · by_contra h'; simp only [not_lt] at h'; have := treeDist_mono h'
    conv at this => left; rw [@treeDist_eq_aux T2 T3]
    conv at this => right; rw [@treeDist_eq_aux T1 T3]
    simp only [neg_le_neg_iff] at this; exact lt_iff_not_ge.1 h.2 this

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
    simp only [true_and]; intro ε hε; obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε)
    use n; simp only [inv_lt_iff_inv_lt] at hn; simp only [inv_le_iff_inv_le]
    exact le_of_lt <| lt_trans hn (by apply ENNReal.coe_lt_coe.2; simp))

def uniformityBasis := fun n => {p : 𝕋₀ × 𝕋₀ | (p.1)↾(n + 1) = (p.2)↾(n + 1)}

private lemma uniformityBasis_eq_aux : (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ℝ≥0∞))⁻¹})
  = uniformityBasis := by
  ext n p; simp only [edist, PseudoMetricSpace.edist, treeDist, toReal_inv, Set.mem_setOf_eq,
    uniformityBasis]; constructor
  · intro h; have h := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 h
    simp only [← toReal_inv, coe_toReal, coe_mk, ne_eq, inv_eq_top, add_eq_zero, one_ne_zero,
      false_and, not_false_eq_true, Nat.cast_eq_zero, toReal_lt_toReal, ENNReal.inv_lt_inv] at h
    have h := (ENNReal.add_lt_add_iff_left (by simp)).1 h
    rw [show (n : ℝ≥0∞) = ((n : ℕ∞) : ℝ≥0∞) from by simp] at h
    simp only [toENNReal_lt] at h
    exact heightCongr_apply _ <| (ENat.add_one_le_iff (by simp)).2 h
  · intro h
    have := (heightCongr_apply_iff _).2 h
    set m := heightCongr p.1 p.2 with hm
    conv => left; congr; congr; congr; congr; right; congr; rw [←hm]
    apply (ENNReal.toReal_lt_toReal (by simp) (by simp)).1
    simp only [← toReal_inv, coe_toReal, coe_mk, ne_eq, inv_eq_top, add_eq_zero, one_ne_zero,
      false_and, not_false_eq_true, Nat.cast_eq_zero, toReal_lt_toReal, ENNReal.inv_lt_inv]
    by_cases h' : m = ⊤
    · simp [h']
    · have := (ENat.lt_add_one_iff h').2 this
      have := ENat.toENNReal_lt.2 this; simp only [Nat.cast_add, Nat.cast_one, toENNReal_add,
        toENNReal_coe, toENNReal_one] at this
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
      have h1 := congrArg (fun T => T↾(n)) h1; simp only [truncation_truncation,
        le_add_iff_nonneg_right, zero_le, inf_of_le_right] at h1
      exact h1 ▸ h2
    set Tval : Set 𝕍 := {v | v ∈ (T' ‖v‖ₕ)↾(‖v‖ₕ)}
    set T : 𝕋₀ := ⟨Tval, by
      ext v; constructor
      · intro hv; induction hv with
        | mem v' hv' => assumption
        | tail m v' hv' ih =>
          simp only [Set.mem_setOf_eq, ← hT'tr ‖v'‖ₕ 1, Tval]
          exact mem_truncation_of_mem_other_truncation (by omega) <| tail_mem ih
        | less m v' hv' n hnm ih =>
          exact @less_mem ((T' (‖v'‖ₕ + 1))↾(‖v'‖ₕ + 1)) m n v' ih hnm
      · exact generateSet.mem v
      , Set.nonempty_iff_ne_empty.1 ⟨[], by simp [Tval]⟩⟩
    use T; have := @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T
    simp only [uniformityBasis, Set.mem_setOf_eq] at this
    refine (this.ge_iff.mpr ?_); simp only [forall_const]
    have hTtr (n : ℕ) : T↾(n) = (T' n)↾(n) := by
      simp only [truncation, mk.injEq]; congr; ext v; simp only [truncation, mem_iff,
        Set.mem_setOf_eq, le_refl, true_and, and_congr_right_iff, T, Tval]; intro hv
      have := (show ‖v‖ₕ + (n - ‖v‖ₕ) = n from by omega) ▸ hT'tr ‖v‖ₕ (n - ‖v‖ₕ)
      constructor
      · intro hv'; exact @mem_of_mem_truncation _ ‖v‖ₕ _
          (this ▸ mem_truncation_of_mem (by omega) hv')
      · intro hv'; exact @mem_of_mem_truncation _ ‖v‖ₕ _
          (Eq.symm this ▸ mem_truncation_of_mem (by omega) hv')
    intro n; exact f.sets_of_superset (hSmem (n + 1)) (by
      simp only [Set.subset_def, Set.mem_setOf_eq]; intro U hU; rw [hTtr (n + 1)]
      exact hSsub' (n + 1) U (T' (n + 1)) hU (hT'mem (n + 1)))

instance : MeasurableSpace 𝕋₀ := borel 𝕋₀

namespace LocallyFinite

noncomputable instance : MetricSpace 𝕋 := .induced @toRLTree toRLTree_inj RLTree.instMetricSpace

instance : IsUltrametricDist 𝕋 where
  dist_triangle_max T1 T2 T3 := treeDist_ultra T1 T2 T3


private instance instUniformityBasis' : (uniformity 𝕋).HasBasis
  (fun _ => True) (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ℝ≥0∞))⁻¹}) :=
  EMetric.mk_uniformity_basis (by simp) (by
    simp only [true_and]; intro ε hε; obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε)
    use n; simp only [inv_lt_iff_inv_lt] at hn; simp only [inv_le_iff_inv_le]
    exact le_of_lt <| lt_trans hn (by apply ENNReal.coe_lt_coe.2; simp))

def uniformityBasis := fun n => {p : 𝕋 × 𝕋 | ((p.1)↾(n + 1) : 𝕋) = ((p.2)↾(n + 1) : 𝕋)}

private lemma uniformityBasis_eq_aux : (fun (n : ℕ) => {p | edist p.1 p.2 < (1 + (n : ℝ≥0∞))⁻¹})
  = uniformityBasis := by
  ext n p; simp only [edist, PseudoMetricSpace.edist, treeDist, toReal_inv, Set.mem_setOf_eq,
    uniformityBasis, truncation, mk.injEq]; constructor
  · intro h; have h := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 h
    simp only [← toReal_inv, coe_toReal, coe_mk, ne_eq, inv_eq_top, add_eq_zero, one_ne_zero,
      false_and, not_false_eq_true, Nat.cast_eq_zero, toReal_lt_toReal, ENNReal.inv_lt_inv] at h
    have h := (ENNReal.add_lt_add_iff_left (by simp)).1 h
    rw [show (n : ℝ≥0∞) = ((n : ℕ∞) : ℝ≥0∞) from by simp] at h
    simp only [toENNReal_lt] at h;
    exact heightCongr_apply _ <| (ENat.add_one_le_iff (by simp)).2 h
  · intro h; simp only at h
    have := (heightCongr_apply_iff _).2 h
    set m := ‖p.1, p.2‖ₕ with hm
    conv => left; congr; congr; congr; congr; right; congr; rw [←hm]
    apply (ENNReal.toReal_lt_toReal (by simp) (by simp)).1
    simp only [← toReal_inv, coe_toReal, coe_mk, ne_eq, inv_eq_top, add_eq_zero, one_ne_zero,
      false_and, not_false_eq_true, Nat.cast_eq_zero, toReal_lt_toReal, ENNReal.inv_lt_inv]
    by_cases h' : m = ⊤
    · simp [h']
    · have := (ENat.lt_add_one_iff h').2 this
      have := ENat.toENNReal_lt.2 this; simp only [Nat.cast_add, Nat.cast_one, toENNReal_add,
        toENNReal_coe, toENNReal_one] at this
      conv => lhs; rw [add_comm]
      conv => rhs; rw [add_comm]
      exact this

instance instUniformityBasis : (uniformity 𝕋).HasBasis
  (fun _ => True) uniformityBasis := uniformityBasis_eq_aux ▸ instUniformityBasis'

instance : CompleteSpace 𝕋 where
  complete := by
    intro f hf; have hf' := (by simpa [Cauchy] using hf)
    let E (n : ℕ) := {p : 𝕋 × 𝕋 | (p.1.toRLTree)↾(n) = (p.2.toRLTree)↾(n)}
    have memE (n : ℕ): E n ∈ uniformity 𝕋 := by
      by_cases h : n = 0
      · simp [h, E]
      · have : E n = uniformityBasis (n - 1) := by
          simp only [uniformityBasis, truncation, E]
          conv => right; congr; ext p; rw [(show n - 1 + 1 = n from by omega), ←toRLTree_iff]; simp
        exact (Filter.HasBasis.mem_iff instUniformityBasis).2 (by
          use (n - 1); simp only [this, subset_refl, and_self])
    have (n : ℕ) : ∃ Sn ∈ f, Sn.Nonempty ∧ Sn ×ˢ Sn ⊆ E n := by
      simp only [LE.le] at hf'; have hf'2 := @hf'.2 (E n) (memE n)
      obtain ⟨Sn, hSmem, _⟩ := Filter.mem_prod_same_iff.1 hf'2; use Sn
      simp only [and_true, true_and, *]; by_contra h
      exact (not_imp_not.2 Filter.empty_mem_iff_bot.1 <| Filter.neBot_iff.1 hf'.1)
        <| (Set.not_nonempty_iff_eq_empty.1 h) ▸ hSmem
    choose S hSmem hSne hSsub using this
    have hSsub' (n : ℕ) (T1 T2) : T1 ∈ S n → T2 ∈ S n → (T1↾(n) : 𝕋) = (T2↾(n) : 𝕋) := by
      intro h1 h2; have : (T1, T2) ∈ (S n) ×ˢ (S n) := by
        simp only [Set.mem_prod, and_self, h1, h2]
      have := Set.mem_of_subset_of_mem (hSsub n) this; simp only [Set.mem_setOf_eq, E] at this
      apply toRLTree_iff.1; exact this
    choose T' hT'mem using hSne
    have hT'tr (n m : ℕ) : ((T' (n + m))↾(n) : 𝕋) = ((T' n)↾(n) : 𝕋) := by
      obtain ⟨U, hU⟩ : (S (n + m) ∩ S n).Nonempty := by
        by_contra h; exact (not_imp_not.2 Filter.empty_mem_iff_bot.1 <| Filter.neBot_iff.1 hf'.1)
          <| (Set.not_nonempty_iff_eq_empty.1 h) ▸ f.inter_mem (hSmem (n + m)) (hSmem n)
      have h1 := hSsub' (n + m) U (T' (n + m)) ((Set.mem_inter_iff _ _ _).1 hU).1 (hT'mem (n + m))
      have h2 := hSsub' n U (T' n) ((Set.mem_inter_iff _ _ _).1 hU).2 (hT'mem n)
      have h1 := congrArg (fun T : 𝕋 => (T↾(n) : 𝕋)) h1; simp only [truncation,
        truncation_truncation, le_add_iff_nonneg_right, zero_le, inf_of_le_right, mk.injEq] at h1 h2
      have := h1 ▸ h2;
      apply toRLTree_inj; exact this
    let Tval : Set 𝕍 := {v | v ∈ ((T' ‖v‖ₕ)↾(‖v‖ₕ) : 𝕋)}
    set _T : 𝕋₀ := ⟨Tval, by
      ext v; constructor
      · intro hv; induction hv with
        | mem v' hv' => assumption
        | tail m v' hv' ih =>
          have := hT'tr ‖v'‖ₕ 1; simp only [truncation] at this
          rw [←toRLTree_iff] at this; simp only at this
          simp only [truncation, mem_iff, Set.mem_setOf_eq, ← this, Tval]
          exact mem_truncation_of_mem_other_truncation (by omega) <| tail_mem ih
        | less m v' hv' n hnm ih =>
          exact @less_mem ((T' (‖v'‖ₕ + 1))↾(‖v'‖ₕ + 1) : 𝕋).toRLTree m n v' ih hnm
      · exact generateSet.mem v
      , Set.nonempty_iff_ne_empty.1 ⟨[], by simp [mem_iff, Tval]⟩⟩
    have hTtr (n : ℕ) : _T↾(n) = (T' n).toRLTree↾(n) := by
      simp only [RLTree.truncation, truncation, RLTree.mk.injEq, _T, Tval]; congr; ext v
      simp only [RLTree.mem_iff, mem_iff, Set.mem_setOf_eq, le_refl, true_and, and_congr_right_iff]
      intro hv; have := (show ‖v‖ₕ + (n - ‖v‖ₕ) = n from by omega) ▸ hT'tr ‖v‖ₕ (n - ‖v‖ₕ)
      simp only [truncation] at this; rw [←toRLTree_iff] at this; simp only at this
      constructor
      · intro hv'; exact @mem_of_mem_truncation _ ‖v‖ₕ _
          (this ▸ mem_truncation_of_mem (by omega) hv')
      · intro hv'; exact @mem_of_mem_truncation _ ‖v‖ₕ _
          (Eq.symm this ▸ mem_truncation_of_mem (by omega) hv')
    set T : 𝕋 := @mk _T (by
      simp only [isLocallyFinite_iff_forall_truncation_finite]; intro n; rw [hTtr n]
      have := ((T' n)↾(n) : 𝕋).locally_finite
      simp only [truncation, isLocallyFinite_iff_forall_truncation_finite,
        truncation_truncation] at this
      have := (show min n n = n from by omega) ▸ this n; exact this)
    use T; have := @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T
    simp only [uniformityBasis, Set.mem_setOf_eq] at this
    refine (this.ge_iff.mpr ?_); simp only [forall_const]
    have hTtr (n : ℕ) : (T↾(n) : 𝕋) = ((T' n)↾(n) : 𝕋) := by
      simp only [T, truncation]; apply toRLTree_inj; simp only; exact hTtr n
    intro n; exact f.sets_of_superset (hSmem (n + 1)) (by
      simp only [Set.subset_def]; intro U hU; rw [hTtr (n + 1)]
      exact hSsub' (n + 1) U (T' (n + 1)) hU (hT'mem (n + 1)))

instance instNhdsBasis (T : 𝕋) : (nhds T).HasBasis (fun _ => True)
  fun n => {T' | (T'↾(n + 1) : 𝕋) = (T↾(n + 1) : 𝕋)} :=
  @nhds_basis_uniformity _ _ _ _ _ instUniformityBasis T

instance : TopologicalSpace.SeparableSpace 𝕋 where
  exists_countable_dense := by
    let F := { s : Finset 𝕍 // s.Nonempty }
    let embed : F → 𝕋 := fun s => generateFinite s
      (by simp [Finset.nonempty_iff_ne_empty.1 s.property]) (by simp only [Finset.finite_toSet])
    -- `Countable` is inferred in `use` from `Set.countable_range` and `Countable F`, which in turn
    -- is inferred from `Subtype.countable`, `Finset.countable`, and `Countable TreeNode`
    use Set.range embed; constructor
    · exact Set.countable_range embed
    · simp only [Dense]; intro T; simp only [mem_closure_iff_nhds_basis (instNhdsBasis T),
      Set.mem_range, truncation, mk.injEq, Set.mem_setOf_eq, exists_exists_eq_and, forall_const]
      intro n
      -- In `Set.toFinset`, `Fintype ↑(T.toRLTree↾(n)).set` is required for element in `F`
      -- this means `LocallyFinite` is required here, because otherwise it is not `Fintype`
      use ⟨Set.toFinset (T.toRLTree↾(n + 1)).set, by
        use []; -- In `Set.mem_toFinset`, `Fintype (T.toRLTree↾(n)).set` is required likewise
        simp only [Set.mem_toFinset]; exact RLTree.mem_iff.1 nil_mem⟩
      simp only [generateFinite, Set.coe_toFinset, generateTree_set,
        truncation_truncation, min_self, embed]

instance : MeasurableSpace 𝕋 := borel 𝕋

end LocallyFinite

end RLTree
