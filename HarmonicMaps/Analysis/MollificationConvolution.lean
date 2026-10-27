module

public import HarmonicMaps.Analysis.MollificationBasic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth convolution of the zero extension

At each fixed positive radius, the scaled kernel is smooth and compactly supported.
The unit-ball zero extension of an integrable map is globally integrable, so its
convolution with this kernel is a globally smooth auxiliary.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Convolution

namespace HarmonicMaps

noncomputable section

theorem scaledMollifierKernel_contDiff (n : ℕ) (h : PositiveRadius) :
    ContDiff ℝ ∞ (scaledMollifierKernel n h) := by
  exact contDiff_const.mul
    ((fixedMollifierKernel_contDiff n).comp (contDiff_id.const_smul h.val⁻¹))

theorem scaledMollifierKernel_nonneg (n : ℕ) (h : PositiveRadius) (z : Domain n) :
    0 ≤ scaledMollifierKernel n h z :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg h.property.le n))
    (fixedMollifierKernel_nonneg n _)

theorem scaledMollifierKernel_rescaled_norm (n : ℕ) (h : PositiveRadius) (z : Domain n) :
    ‖h.val⁻¹ • z‖ = h.val⁻¹ * ‖z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h.property)]

theorem scaledMollifierKernel_tsupport_subset_halfBall (n : ℕ) (h : PositiveRadius) :
    tsupport (scaledMollifierKernel n h) ⊆
      Metric.closedBall (0 : Domain n) (h.val / 2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hkernel : scaledMollifierKernel n h z ≠ 0 := Function.mem_support.mp hz
  have hfixed : fixedMollifierKernel n (h.val⁻¹ • z) ≠ 0 := by
    intro hzero
    apply hkernel
    simp only [scaledMollifierKernel, hzero, mul_zero]
  have hnorm := fixedMollifierKernel_tsupport_subset_halfBall n
    (subset_tsupport _ (Function.mem_support.mpr hfixed))
  rw [Metric.mem_closedBall, dist_zero_right, scaledMollifierKernel_rescaled_norm] at hnorm
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖z‖ = h.val * (h.val⁻¹ * ‖z‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ h.property.ne', one_mul]
    _ ≤ h.val * (1 / 2) := mul_le_mul_of_nonneg_left hnorm h.property.le
    _ = h.val / 2 := by ring

theorem scaledMollifierKernel_hasCompactSupport (n : ℕ) (h : PositiveRadius) :
    HasCompactSupport (scaledMollifierKernel n h) :=
  (isCompact_closedBall (0 : Domain n) (h.val / 2)).of_isClosed_subset
    (isClosed_tsupport _) (scaledMollifierKernel_tsupport_subset_halfBall n h)

theorem scaledMollifierKernel_integrable (n : ℕ) (h : PositiveRadius) :
    Integrable (scaledMollifierKernel n h) volume :=
  (scaledMollifierKernel_contDiff n h).continuous.integrable_of_hasCompactSupport
    (scaledMollifierKernel_hasCompactSupport n h)

theorem unitBallZeroExtension_integrable {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) :
    Integrable (unitBallZeroExtension u) volume :=
  hu.integrable_indicator measurableSet_ball

theorem scaledMollifierKernel_smul_zeroExtension_integrable {n q : ℕ}
    (u : Domain n → Ambient q) (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1))
    (h : PositiveRadius) (x : Domain n) :
    Integrable (fun z => scaledMollifierKernel n h z • unitBallZeroExtension u (x - z))
      volume := by
  exact ((scaledMollifierKernel_hasCompactSupport n h).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMollifierKernel_contDiff n h).continuous
    (unitBallZeroExtension_integrable u hu).locallyIntegrable x).integrable

/-- The global convolution auxiliary formed from the explicit unit-ball zero extension. -/
def zeroExtendedMollification {n q : ℕ} (u : Domain n → Ambient q)
    (_hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (x : Domain n) : Ambient q :=
  ∫ z, scaledMollifierKernel n h z • unitBallZeroExtension u (x - z)

theorem zeroExtendedMollification_eq_convolution {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius) :
    zeroExtendedMollification u hu h =
      scaledMollifierKernel n h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        unitBallZeroExtension u := by
  rfl

theorem zeroExtendedMollification_contDiff {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius) :
    ContDiff ℝ ∞ (zeroExtendedMollification u hu h) := by
  rw [zeroExtendedMollification_eq_convolution]
  exact (scaledMollifierKernel_hasCompactSupport n h).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMollifierKernel_contDiff n h)
    (unitBallZeroExtension_integrable u hu).locallyIntegrable

end
end HarmonicMaps
