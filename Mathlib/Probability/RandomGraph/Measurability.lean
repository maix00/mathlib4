import Mathlib.Probability.RandomGraph.Basic

open ENNReal NNReal ENat Cardinal

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
