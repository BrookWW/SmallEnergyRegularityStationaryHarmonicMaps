module

public import HarmonicMaps.Analysis.VariableMollificationPullback
public import HarmonicMaps.Analysis.MollificationDistanceBasic
public import HarmonicMaps.Analysis.MollificationLocalKernel

/-!
# Sampling geometry for variable smoothing

Every point of the closed averaging ball samples inside the source outer
ball. The closed averaging ball is used for compactness arguments.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- Closed unit-ball sampling stays inside the source outer ball. -/
theorem variableShift_mem_outerBall_of_mem_closedBall {n : ℕ}
    {s : Domain n → ℝ} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    {x y : Domain n} (hx : x ∈ Metric.ball 0 (theta + 2 * delta))
    (hy : y ∈ Metric.closedBall 0 1) :
    variableShift s y x ∈ Metric.ball 0 (theta + 2 * delta) := by
  by_cases hxin : x ∈ Metric.ball (0 : Domain n) (theta + delta)
  · have hxnorm : ‖x‖ < theta + delta := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxin
    have hynorm : ‖y‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    have hsnorm : ‖s x • y‖ ≤ delta := by
      rw [norm_smul, Real.norm_of_nonneg (hvalues x).1]
      exact (mul_le_mul_of_nonneg_left hynorm (hvalues x).1).trans
        (by simpa only [mul_one] using (hvalues x).2.trans hhbar)
    rw [Metric.mem_ball, dist_zero_right]
    change ‖x - s x • y‖ < theta + 2 * delta
    exact (norm_sub_le _ _).trans_lt (by linarith only [hxnorm, hsnorm])
  · rw [variableShift_eq_self_of_zero (hoff x hxin)]
    exact hx

/-- Evaluating a continuous linear map is summation over its actual columns. -/
theorem domain_clm_apply_eq_sum_columns {n q : ℕ}
    (D : Domain n →L[ℝ] Ambient q) (v : Domain n) :
    D v = ∑ j : Fin n, v j • D (EuclideanSpace.single j 1) := by
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply]

/-- The positive sampling ball lies inside the actual source domain. -/
theorem variableMollification_sampleBall_subset {n : ℕ} {s : Domain n → ℝ}
    {theta delta hbar : ℝ} (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (x : Domain n) : Metric.ball x (s x) ⊆ Metric.ball 0 (theta + 2 * delta) := by
  by_cases hx : x ∈ Metric.ball (0 : Domain n) (theta + delta)
  · apply Metric.ball_subset_ball'
    have hxnorm : ‖x‖ < theta + delta := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [dist_zero_right]
    linarith only [hxnorm, (hvalues x).2, hhbar]
  · rw [hoff x hx, Metric.ball_zero]
    exact empty_subset _

/-- Local Lp input gives actual pointwise sampling Lp membership at every
source point, including the zero-radius constant sampling case. -/
theorem variableMollification_sampling_memLp {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {s : Domain n → ℝ} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    {f : Domain n → E} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Metric.ball 0 (theta + 2 * delta))))
    (x : Domain n) : MemLp (fun y => f (variableShift s y x)) p
      (volume.restrict (Metric.ball (0 : Domain n) 1)) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  by_cases hx : s x = 0
  · simpa only [variableShift, hx, zero_smul, sub_zero] using
      (memLp_const (f x) : MemLp (fun _ : Domain n => f x) p
        (volume.restrict (Metric.ball (0 : Domain n) 1)))
  · let h : PositiveRadius := ⟨s x, lt_of_le_of_ne (hvalues x).1 (Ne.symm hx)⟩
    exact mollification_shift_memLp h x
      (hf.mono_measure (Measure.restrict_mono
        (variableMollification_sampleBall_subset hvalues hhbar hoff x) le_rfl))

/-- Local integrability gives genuine sampling integrability, with no global
input integrability assumption. -/
theorem variableMollification_sampling_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {s : Domain n → ℝ} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    {f : Domain n → E}
    (hf : IntegrableOn f (Metric.ball 0 (theta + 2 * delta)) volume)
    (x : Domain n) : IntegrableOn (fun y => f (variableShift s y x))
      (Metric.ball (0 : Domain n) 1) volume := by
  change Integrable (fun y => f (variableShift s y x))
    (volume.restrict (Metric.ball (0 : Domain n) 1))
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  by_cases hx : s x = 0
  · simpa only [variableShift, hx, zero_smul, sub_zero] using
      (integrable_const (f x) : Integrable (fun _ : Domain n => f x)
        (volume.restrict (Metric.ball (0 : Domain n) 1)))
  · let h : PositiveRadius := ⟨s x, lt_of_le_of_ne (hvalues x).1 (Ne.symm hx)⟩
    exact mollification_shift_integrableOn h x
      (hf.mono_set (variableMollification_sampleBall_subset hvalues hhbar hoff x))

/-- The bounded source kernel preserves actual sampling integrability. -/
theorem variableMollification_weighted_sampling_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Domain n → ℝ} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    {f : Domain n → E}
    (hf : IntegrableOn f (Metric.ball 0 (theta + 2 * delta)) volume)
    (x : Domain n) : IntegrableOn
      (fun y => fixedMollifierKernel n y • f (variableShift s y x))
      (Metric.ball (0 : Domain n) 1) volume := by
  apply (variableMollification_sampling_integrable hvalues hhbar hoff hf x).bdd_smul
      (fixedMollifierKernelBound n)
      (fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y)]
    exact fixedMollifierKernel_le_bound n y

end HarmonicMaps
