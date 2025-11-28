import Mathlib.Probability.RandomGraph.RootedLabeledTree
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

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

@[simp] lemma processGenerationSize_ennreal_aemeasurable (n : ℕ) :
  AEMeasurable (fun ω => (GW.processGenerationSize n ω : ENNReal)) ℙ := by
  simp [processGenerationSize, generationSizeAtLevel_def, generationSizeAtLevel_eq_tsum_sum]


  sorry

@[simp] lemma processGenerationSize_aemeasurable (n : ℕ) :
  AEMeasurable (GW.processGenerationSize n) ℙ := by apply AEMeasurable.ennreal_ofNat_toNat; simp

#check ENNReal.measurable_of_measurable_nnreal

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


#check Set.finite_iUnion
