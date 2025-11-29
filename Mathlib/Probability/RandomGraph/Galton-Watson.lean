import Mathlib.Probability.RandomGraph.RootedLabeledTree
import Mathlib.Probability.HasLaw
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

open MeasureTheory Measure RootedLabeledTree LocallyFinite

section GW

structure ProbabilitySpace where
  space : Type*
  space_measurable : MeasurableSpace space
  space_measure : @MeasureTheory.Measure space space_measurable
  space_measure_prob : MeasureTheory.IsProbabilityMeasure space_measure

instance (PS : ProbabilitySpace) : MeasurableSpace PS.space := PS.space_measurable

noncomputable instance : Inhabited ProbabilitySpace where
  default := ⟨ℕ, _, dirac 0, dirac.isProbabilityMeasure⟩

variable (L : PMF ℕ)

class GaltonWatson extends ProbabilitySpace where
  toField (ω : space) : RootedLabeledTree.LocallyFinite
  toProcess : TreeNode → space → ℕ
  toProcess_eq_toField : ∀ ω v, v ∈ toField ω → toProcess v ω = toField ω v
  toProcess_measurable (v : TreeNode) : Measurable (toProcess v)
  toProcess_hasLaw (v : TreeNode) : ProbabilityTheory.HasLaw (toProcess v) L.toMeasure space_measure
  toProcess_iIndep : ProbabilityTheory.iIndepFun (fun v => toProcess v) space_measure

export GaltonWatson (toProcess)

attribute [measurability] GaltonWatson.toProcess_measurable

noncomputable instance : Inhabited (GaltonWatson L) where
  default := by
    choose Ω mΩ ℙ X hX hX' hX'' hℙ using @ProbabilityTheory.exists_iid TreeNode ℕ _ L.toMeasure
      (PMF.toMeasure.isProbabilityMeasure L)
    set toField := fun ω => LocallyFinite.generateFromCountChildren (fun v => X v ω)
    exact ⟨⟨Ω, mΩ, ℙ, hℙ⟩, toField, X, (by
      simp; intro ω v hv; simp [toField, DFunLike.coe,
        LocallyFinite.generateFromCountChildren_countChildren_eq (fun v => X v ω) v]
      simp [toField, LocallyFinite.mem_iff, LocallyFinite.generateFromCountChildren,
        RootedLabeledTree.mem_iff, RootedLabeledTree.generateFromCountChildren, generateTree] at hv
      grind), hX, hX', hX''⟩

namespace GaltonWatson

variable {L : PMF ℕ} (GW : GaltonWatson L) (v : TreeNode) (ω : GW.space)

noncomputable def measureGaltonWatson := GW.space_measure.map GW.toField

@[simp] lemma toProcess_aemeasurable : AEMeasurable (GW.toProcess v) GW.space_measure :=
  (GW.toProcess_hasLaw v).aemeasurable

@[simp] lemma toProcess_ennreal_aemeasurable :
  AEMeasurable (fun ω => (GW.toProcess v ω : ENNReal)) GW.space_measure := by
  apply AEMeasurable.nat_ofNat_toENNReal; simp

@[simp] lemma toProcess_eq_countChildren :
  (GW.toField ω).countChildren v = GW.toProcess v ω := by
  -- simp [toProcess_eq_toField, RootedLabeledTree.LocallyFinite.instFunLikeTreeNodeNat]
  sorry

noncomputable def processGenerationSize : ℕ → GW.space → ℕ :=
  fun n ω => if n = 0 then 1 else (GW.toField ω).generationSizeFromLevel (n - 1)

@[simp] lemma processGenerationSize_ennreal_aemeasurable (n : ℕ) :
  AEMeasurable (fun ω => (GW.processGenerationSize n ω : ENNReal)) GW.space_measure := by
  by_cases h : n = 0
  · simp [processGenerationSize, h]
  · simp [processGenerationSize, h, generationSizeFromLevel_def_toRootedLabeledTree,
      generationSizeFromLevel_eq_tsum_sum, ENNReal.tsum_eq_iSup_nat, ←countChildren_toENat,
      toProcess_eq_countChildren]; apply AEMeasurable.iSup; intros
    refine Finset.aemeasurable_fun_sum _ ?_; intros
    refine Finset.aemeasurable_fun_sum _ ?_; intros; simp

@[simp] lemma processGenerationSize_aemeasurable (n : ℕ) :
  AEMeasurable (GW.processGenerationSize n) GW.space_measure := by
  apply AEMeasurable.ennreal_ofNat_toNat; simp

@[simp] lemma processGenerationSize_zero : GW.processGenerationSize 0 = 1 := by
  ext; simp [processGenerationSize]

@[simp] lemma processGenerationSize_one : GW.processGenerationSize 1 = GW.toProcess [] := by
  unfold processGenerationSize; simp [generationSizeFromLevel_def_toSum, setOfLevel]

end GaltonWatson

namespace GaltonWatson

variable (GW : GaltonWatson L) (v : TreeNode) (ω : GW.space)

open GaltonWatson ProbabilityTheory

@[simp, measurability] lemma toField_measurable : Measurable (GW.toField) := by

  sorry

@[simp] instance measureGaltonWatson_isProbabilityMeasure :
  IsProbabilityMeasure GW.measureGaltonWatson := by sorry

@[simp, measurability] lemma toProcess_ennreal_measurable :
  Measurable (fun ω => (GW.toProcess v ω : ENNReal)) := by
  apply Measurable.nat_ofNat_toENNReal; measurability

@[simp, measurability] lemma processGenerationSize_ennreal_measurable (n : ℕ) :
  Measurable (fun ω => (GW.processGenerationSize n ω : ENNReal)) := by
  by_cases h : n = 0
  · simp [processGenerationSize, h]
  · simp [processGenerationSize, h, generationSizeFromLevel_def_toRootedLabeledTree,
      generationSizeFromLevel_eq_tsum_sum, ENNReal.tsum_eq_iSup_nat, ←countChildren_toENat,
      toProcess_eq_countChildren]; apply Measurable.iSup; intros
    refine Finset.measurable_fun_sum _ ?_; intros
    refine Finset.measurable_fun_sum _ ?_; intros; measurability

@[simp, measurability] lemma processGenerationSize_measurable (n : ℕ) :
  Measurable (GW.processGenerationSize n) := by apply Measurable.ennreal_ofNat_toNat; simp

end GaltonWatson

section ProbabilityGeneratingFunction

noncomputable def pgf (L : PMF ℕ) (s : ENNReal) : ENNReal := ∑' k, (L k) * s ^ k

lemma pgf_zero (L : PMF ℕ) : pgf L 0 = L 0 := by
  rw [pgf, ←@Summable.sum_add_tsum_nat_add' _ _ _ _ _ _ 1 ENNReal.summable]; simp

end ProbabilityGeneratingFunction

namespace GaltonWatson

variable (GW : GaltonWatson L)

def eventExtinction := { ω | ∃ n, GW.processGenerationSize n ω = 0 }

-- lemma eventExtinction_ofAEIsTree :
--   GW.eventExtinction = { ω | ∃ n, GW.toProcess.forestSize_atMostK_atLevel 0 n ω = 0 } := sorry

lemma eventExtinction_measurable : MeasurableSet (GW.eventExtinction) := by
  simp only [eventExtinction]; conv => congr;
  sorry

end GaltonWatson
end GW


#check Set.finite_iUnion
