module

public import StationaryHarmonicMaps.Analysis.GrandKernelCutoffAverage
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import HarmonicMaps.Analysis.BallAverageDifferentiation

/-!
# Actual cutoff averages at Lebesgue points

A positive cutoff mass is bounded below by the inner ball volume.
The error of its original weighted average is controlled by the actual
norm average on the double ball. This estimate retains the original L1
function and arbitrary actual cutoffs between zero and one.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual original cutoff average has positive mass and its true error is bounded by the double-ball norm average. -/
theorem cutoff_average_error_le_ball_average {n : ℕ}
    (f : Domain n → ℝ) (hf : Integrable f volume) (a : Domain n)
    {r : ℝ} (hr : 0<r) (η : Domain n → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η⊆Metric.ball a (2*r))
    (hOne : ∀ x∈Metric.closedBall a r,η x=1)
    (hBound : ∀ x,0≤η x ∧ η x≤1) (c : ℝ) :
    0<(∫ x,η x) ∧
      |(∫ x,η x*f x)/(∫ x,η x)-c| ≤
        (2 : ℝ)^n*(⨍ x in Metric.ball a (2*r),|f x-c|) := by
  have hηI : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hcη
  have hηfI : Integrable (fun x=>η x*f x) volume :=
    hf.bdd_mul hη.continuous.aestronglyMeasurable (Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (hBound x).1]
      exact (hBound x).2)
  have hMass : volume.real (Metric.ball a r) ≤ ∫ x,η x := by
    have H := integral_mono_measure (Measure.restrict_le_self (s := Metric.ball a r))
      (Eventually.of_forall fun x=>(hBound x).1) hηI
    have hBall : (∫ x in Metric.ball a r,η x)=volume.real (Metric.ball a r) := by
      rw [setIntegral_congr_fun measurableSet_ball
        (fun x hx=>hOne x (Metric.ball_subset_closedBall hx))]
      simp only [integral_const,smul_eq_mul,mul_one,Measure.real,
        Measure.restrict_apply MeasurableSet.univ,univ_inter]
    rwa [hBall] at H
  have hVolumePos : 0<volume.real (Metric.ball a r) :=
    HolderToCK.ball_volume_real_pos a hr
  have hMassPos : 0<∫ x,η x := hVolumePos.trans_le hMass
  have hηcI := hηI.mul_const c
  have hDiffI : Integrable (fun x=>η x*(f x-c)) volume := by
    apply (hηfI.sub hηcI).congr
    exact Eventually.of_forall fun x=>by change η x*f x-η x*c=η x*(f x-c);ring
  have hAbsEq (x : Domain n) : |η x*(f x-c)|=η x*|f x-c| := by
    rw [abs_mul,abs_of_nonneg (hBound x).1]
  have hWeightedI : Integrable (fun x=>η x*|f x-c|) volume :=
    hDiffI.abs.congr (Eventually.of_forall hAbsEq)
  let T := Metric.ball a (2*r)
  letI : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hNormI : IntegrableOn (fun x=>|f x-c|) T volume :=
    ((hf.integrableOn).sub (integrable_const c)).abs
  have hSupportEq : (∫ x,η x*|f x-c|)=∫ x in T,η x*|f x-c| := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : η x=0 := image_eq_zero_of_notMem_tsupport (fun h=>hx (hsη h))
    rw [hz,zero_mul]
  have hRaw : |∫ x,η x*(f x-c)| ≤ ∫ x in T,|f x-c| := by
    calc
      _ ≤ ∫ x,|η x*(f x-c)| := abs_integral_le_integral_abs
      _ = ∫ x in T,η x*|f x-c| := by simp_rw [hAbsEq];exact hSupportEq
      _ ≤ _ := integral_mono hWeightedI.integrableOn hNormI
        (fun x=>mul_le_of_le_one_left (abs_nonneg _) (hBound x).2)
  have hIdentity : (∫ x,η x*f x)/(∫ x,η x)-c =
      (∫ x,η x*(f x-c))/(∫ x,η x) := by
    have hFun : (fun x=>η x*(f x-c))=(fun x=>η x*f x-η x*c) := by funext x;ring
    rw [hFun,integral_sub hηfI hηcI,integral_mul_const]
    field_simp [hMassPos.ne']
  have hAvg0 : 0≤⨍ x in T,|f x-c| := by
    rw [setAverage_eq,smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg fun x=>abs_nonneg _)
  have hAvgEq : (∫ x in T,|f x-c|)=
      volume.real T*(⨍ x in T,|f x-c|) := by
    simpa only [smul_eq_mul] using (measure_smul_setAverage
      (fun x=>|f x-c|) (show volume T≠(⊤ : ℝ≥0∞) from measure_ball_ne_top)).symm
  have hRatio : volume.real T=(2 : ℝ)^n*volume.real (Metric.ball a r) := by
    rw [show T=Metric.ball a (2*r) from rfl,
      HolderToCK.ball_volume_real a (by positivity : 0<2*r),
      HolderToCK.ball_volume_real a hr,mul_pow,mul_assoc]
  refine ⟨hMassPos,?_⟩
  rw [hIdentity,abs_div,abs_of_pos hMassPos,div_le_iff₀ hMassPos]
  calc
    _ ≤ ∫ x in T,|f x-c| := hRaw
    _ = ((2 : ℝ)^n*(⨍ x in T,|f x-c|))*volume.real (Metric.ball a r) := by
      rw [hAvgEq,hRatio]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMass (mul_nonneg (by positivity) hAvg0)

end StationaryHarmonicMaps.Analysis

end
