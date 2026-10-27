module

public import HarmonicMaps.Analysis.CompactParametricIntegral
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Actual radial Euler resolvents for the relative coexact range

Weighted radial integration gives smooth functions whose actual derivatives
are obtained from the same original field. The weights are nonnegative
integer powers, so the origin and both integration endpoints are included.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

@[expose] noncomputable def radialEulerResolvent {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a b : ℕ) (f : Domain n → G) (x : Domain n) : G :=
  ∫ t : Icc (0 : ℝ) 1, (t : ℝ) ^ a • f ((t : ℝ) ^ b • x)

/-- The compact-parameter radial resolvent is the ordinary weighted interval integral. -/
theorem radialEulerResolvent_eq_intervalIntegral {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (a b : ℕ) (f : Domain n → G) (x : Domain n) :
    radialEulerResolvent a b f x = ∫ t in (0 : ℝ)..1, t ^ a • f (t ^ b • x) := by
  change (∫ t : Icc (0 : ℝ) 1, (t : ℝ) ^ a • f ((t : ℝ) ^ b • x)
    ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Icc
    (fun t : ℝ => t ^ a • f (t ^ b • x)),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

private theorem radial_joint_smooth {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a b : ℕ) (f : Domain n → G) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : Domain n × ℝ => p.2 ^ a • f (p.2 ^ b • p.1)) :=
  (contDiff_snd.pow a).smul (hf.comp ((contDiff_snd.pow b).smul contDiff_fst))

/-- A genuine smooth field has a genuine smooth radial Euler resolvent. -/
theorem radialEulerResolvent_contDiff {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (a b : ℕ) (f : Domain n → G) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radialEulerResolvent a b f) := by
  let J : Domain n × ℝ → G := fun p => p.2 ^ a • f (p.2 ^ b • p.1)
  have hJ := radial_joint_smooth a b f hf
  have H := compactParametricIntegral_contDiffOn (volume : Measure (Icc (0 : ℝ) 1))
    (fun t : Icc (0 : ℝ) 1 => (t : ℝ)) continuous_subtype_val
    univ isOpen_univ univ isOpen_univ (fun _ _ _ => mem_univ _)
    J hJ.contDiffOn
  exact contDiffOn_univ.mp H

/-- The actual derivative of the radial resolvent integrates the original derivatives with their true dilation weight. -/
theorem radialEulerResolvent_hasFDerivAt {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (a b : ℕ) (f : Domain n → G) (hf : ContDiff ℝ ∞ f) (x : Domain n) :
    HasFDerivAt (radialEulerResolvent a b f)
      (∫ t : Icc (0 : ℝ) 1, (t : ℝ) ^ (a+b) • fderiv ℝ f ((t : ℝ) ^ b • x)) x := by
  let J : Domain n × ℝ → G := fun p => p.2 ^ a • f (p.2 ^ b • p.1)
  have hJ := radial_joint_smooth a b f hf
  have H := compactParametricIntegral_hasFDerivAt (volume : Measure (Icc (0 : ℝ) 1))
    (fun t : Icc (0 : ℝ) 1 => (t : ℝ)) continuous_subtype_val
    univ isOpen_univ univ isOpen_univ (fun _ _ _ => mem_univ _)
    J hJ.contDiffOn x (mem_univ x)
  have hSlice (t : ℝ) : HasFDerivAt (fun z : Domain n => t ^ a • f (t ^ b • z))
      (t ^ (a+b) • fderiv ℝ f (t ^ b • x)) x := by
    have HD := (((hf.differentiable (by simp) (t ^ b • x)).hasFDerivAt).comp x
      ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (t ^ b))).const_smul (t ^ a)
    have heq : t ^ a • ((fderiv ℝ f (t ^ b • x)).comp
        ((t ^ b) • ContinuousLinearMap.id ℝ (Domain n))) =
        t ^ (a+b) • fderiv ℝ f (t ^ b • x) := by
      ext v
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, map_smul, pow_add, mul_smul]
    rw [← heq]
    exact HD
  have hPartial (t : Icc (0 : ℝ) 1) :
      (fderiv ℝ J (x, (t : ℝ))).comp (ContinuousLinearMap.inl ℝ (Domain n) ℝ) =
        (t : ℝ) ^ (a+b) • fderiv ℝ f ((t : ℝ) ^ b • x) := by
    have hPair : HasFDerivAt (fun z : Domain n => (z, (t : ℝ)))
        (ContinuousLinearMap.inl ℝ (Domain n) ℝ) x := hasFDerivAt_prodMk_left x (t : ℝ)
    have hJD : HasFDerivAt J (fderiv ℝ J (x, (t : ℝ))) (x, (t : ℝ)) :=
      (hJ.differentiable (by simp) (x, (t : ℝ))).hasFDerivAt
    have HD : HasFDerivAt (fun z : Domain n => (t : ℝ)^a • f ((t : ℝ)^b • z))
        ((fderiv ℝ J (x, (t : ℝ))).comp (ContinuousLinearMap.inl ℝ (Domain n) ℝ)) x :=
      by simpa only [Function.comp_def, J] using hJD.comp x hPair
    exact HD.unique (hSlice t)
  have heq := integral_congr_ae (μ := (volume : Measure (Icc (0 : ℝ) 1)))
    (Eventually.of_forall hPartial)
  rw [heq] at H
  exact H

/-- Every original directional derivative has the same literal weighted integral formula. -/
theorem radialEulerResolvent_fderiv_apply {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (a b : ℕ) (f : Domain n → G) (hf : ContDiff ℝ ∞ f) (x v : Domain n) :
    fderiv ℝ (radialEulerResolvent a b f) x v =
      ∫ t : Icc (0 : ℝ) 1, (t : ℝ) ^ (a+b) • fderiv ℝ f ((t : ℝ) ^ b • x) v := by
  have hInt : Integrable (fun t : Icc (0 : ℝ) 1 =>
      (t : ℝ) ^ (a+b) • fderiv ℝ f ((t : ℝ) ^ b • x)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (continuous_subtype_val.pow (a+b)).smul
      ((hf.continuous_fderiv (by simp)).comp ((continuous_subtype_val.pow b).smul continuous_const))
  rw [(radialEulerResolvent_hasFDerivAt a b f hf x).fderiv,
    ContinuousLinearMap.integral_apply hInt]
  rfl


private theorem radial_weighted_curve_hasDerivAt {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a b : ℕ) (f : Domain n → G) (hf : ContDiff ℝ ∞ f) (x : Domain n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ (a+1) • f (s ^ b • x))
      (((a+1 : ℕ) : ℝ) • (t ^ a • f (t ^ b • x)) +
        (b : ℝ) • (t ^ (a+b) • fderiv ℝ f (t ^ b • x) x)) t := by
  have hCurve := ((hf.differentiable (by simp) (t ^ b • x)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_pow b t).smul_const x)
  have H := (hasDerivAt_pow (a+1) t).smul hCurve
  have hWeight : t ^ (a+1) * ((b : ℝ) * t ^ (b-1)) = (b : ℝ) * t ^ (a+b) := by
    by_cases hb : b = 0
    · simp only [hb, Nat.cast_zero, zero_mul, mul_zero]
    · have he : a+1+(b-1) = a+b := by omega
      rw [← mul_assoc, mul_comm (t ^ (a+1)) (b : ℝ), mul_assoc, ← pow_add, he]
  have hEq : t ^ (a+1) • (fderiv ℝ f (t ^ b • x) (((b : ℝ) * t ^ (b-1)) • x)) +
      (((a+1 : ℕ) : ℝ) * t ^ ((a+1)-1)) • f (t ^ b • x) =
      (((a+1 : ℕ) : ℝ) • (t ^ a • f (t ^ b • x)) +
        (b : ℝ) • (t ^ (a+b) • fderiv ℝ f (t ^ b • x) x)) := by
    rw [map_smul, ← mul_smul, hWeight]
    simp only [Nat.add_sub_cancel, mul_smul]
    exact add_comm _ _
  simp only [Function.comp_def] at H
  rw [hEq] at H
  exact H.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)

/-- Weighted radial integration is a genuine right inverse of its Euler operator, including the origin. -/
theorem radialEulerResolvent_euler_identity {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (a b : ℕ) (f : Domain n → G) (hf : ContDiff ℝ ∞ f) (x : Domain n) :
    (((a+1 : ℕ) : ℝ) • radialEulerResolvent a b f x) +
      (b : ℝ) • fderiv ℝ (radialEulerResolvent a b f) x x = f x := by
  let F := fun t : ℝ => t ^ a • f (t ^ b • x)
  let D := fun t : ℝ => t ^ (a+b) • fderiv ℝ f (t ^ b • x) x
  have hFC : Continuous F := (continuous_id.pow a).smul
    (hf.continuous.comp ((continuous_id.pow b).smul continuous_const))
  have hDC : Continuous D := (continuous_id.pow (a+b)).smul
    (((hf.continuous_fderiv (by simp)).comp
      ((continuous_id.pow b).smul continuous_const)).clm_apply continuous_const)
  have hDI : IntervalIntegrable (fun t => (b : ℝ) • D t) volume 0 1 :=
    (continuous_const.smul hDC).intervalIntegrable 0 1
  have hFI : IntervalIntegrable (fun t => (((a+1 : ℕ) : ℝ)) • F t) volume 0 1 :=
    (continuous_const.smul hFC).intervalIntegrable 0 1
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => radial_weighted_curve_hasDerivAt a b f hf x t)
    (hFI.add hDI)
  have hRight : (1 : ℝ) ^ (a+1) • f ((1 : ℝ) ^ b • x) -
      (0 : ℝ) ^ (a+1) • f ((0 : ℝ) ^ b • x) = f x := by
    simp only [pow_succ, one_pow, mul_one, mul_zero, one_smul, zero_smul, sub_zero]
  rw [hRight] at H
  have hSplit := intervalIntegral.integral_add hFI hDI
  change (∫ t in (0 : ℝ)..1, (((a+1 : ℕ) : ℝ)) • F t + (b : ℝ) • D t) = f x at H
  rw [hSplit] at H
  rw [radialEulerResolvent_eq_intervalIntegral, radialEulerResolvent_fderiv_apply a b f hf x x]
  have hDInterval : (∫ t : Icc (0 : ℝ) 1, (t : ℝ) ^ (a+b) •
      fderiv ℝ f ((t : ℝ) ^ b • x) x) = ∫ t in (0 : ℝ)..1, D t :=
    radialEulerResolvent_eq_intervalIntegral (a+b) b (fun y => fderiv ℝ f y x) x
  rw [hDInterval]
  simpa only [intervalIntegral.integral_smul, F, D] using H

end StationaryHarmonicMaps.Analysis

end
