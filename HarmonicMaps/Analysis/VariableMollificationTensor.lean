module

public import HarmonicMaps.Analysis.VariableMollificationSampling
public import HarmonicMaps.Analysis.VariableMollificationMatrix

/-!
# Actual tensor columns in variable smoothing

The source tensor integrand uses the original input gradient columns. Each
weighted column is integrable at every point, including zero sampling radius.
-/

public section

open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff

namespace HarmonicMaps

/-- Every literal weighted tensor column is integrable from local original
column data. No derivative or sampling estimate is an input. -/
theorem variableMollification_tensor_integrable {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    {Df : Domain n → Gradient n q}
    (hDf : ∀ j : Fin n, IntegrableOn (fun z => Df z j)
      (Metric.ball 0 (theta + 2 * delta)) volume) (x : Domain n) (i : Fin n) :
    IntegrableOn (fun y => fixedMollifierKernel n y •
      ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
        (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j •
        Df (variableShift s y x) j) (Metric.ball (0 : Domain n) 1) volume := by
  let c := fun (j : Fin n) (y : Domain n) =>
    ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)
      (EuclideanSpace.single i 1)) j
  have hc (j : Fin n) : Continuous (c j) := by
    change Continuous (fun y : Domain n =>
      (EuclideanSpace.single i 1) j - (fderiv ℝ s x (EuclideanSpace.single i 1)) * y j)
    fun_prop
  have hi (j : Fin n) : IntegrableOn (fun y => c j y •
      (fixedMollifierKernel n y • Df (variableShift s y x) j))
      (Metric.ball (0 : Domain n) 1) volume := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Domain n) 1).exists_bound_of_continuousOn
      (hc j).continuousOn
    apply (variableMollification_weighted_sampling_integrable hvalues hhbar hoff (hDf j) x).bdd_smul
      C (hc j).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hC y (Metric.ball_subset_closedBall hy)
  apply (integrable_finsetSum Finset.univ (fun j _ => hi j)).congr
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm (c j y) (fixedMollifierKernel n y) (Df (variableShift s y x) j)

/-- The source tensor has the sharp HS square bound for each sampled point. -/
theorem variableMollification_tensor_hsNormSq_le {n q : ℕ}
    {s : Domain n → ℝ} {L : ℝ} (hs : ContDiff ℝ ∞ s)
    (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) {y : Domain n} (hy : y ∈ Metric.ball 0 1)
    (Df : Domain n → Gradient n q) (x : Domain n) :
    hsNormSq (fun i => ∑ j : Fin n,
      ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)
        (EuclideanSpace.single i 1)) j • Df (variableShift s y x) j) ≤
      (1 + L) ^ 2 * hsNormSq (Df (variableShift s y x)) := by
  apply hsNormSq_right_comp_le_of_norm_le
  rw [← fderiv_variableShift ((hs.differentiable (by simp)) x) y]
  exact norm_fderiv_variableShift_le ((hs.differentiable (by simp)) x) hDs y hy

end HarmonicMaps
