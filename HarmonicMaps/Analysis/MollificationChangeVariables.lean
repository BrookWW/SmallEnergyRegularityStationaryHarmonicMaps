module

public import HarmonicMaps.Analysis.MollificationConvolution
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Change of variables for interior mollification

Positive-radius scaling identifies the original unit-ball integral with the
convolution of the explicit zero extension. Interior sampling stays in the
unit ball when the radius is at most one quarter.
-/

@[expose] public section

open MeasureTheory Set

namespace HarmonicMaps

noncomputable section

/-- Interior samples of the original map remain in its unit-ball domain. -/
theorem mollification_sampling_mem_unitBall {n : ℕ} (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4) {x y : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4))
    (hy : y ∈ Metric.ball (0 : Domain n) 1) :
    x - h.val • y ∈ Metric.ball (0 : Domain n) 1 := by
  rw [Metric.mem_ball, dist_zero_right] at hx hy ⊢
  calc
    ‖x - h.val • y‖ ≤ ‖x‖ + ‖h.val • y‖ := norm_sub_le _ _
    _ = ‖x‖ + h.val * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos h.property]
    _ < 3 / 4 + h.val * 1 :=
      add_lt_add hx (mul_lt_mul_of_pos_left hy h.property)
    _ ≤ 1 := by linarith only [hh]

/-- Evaluating the scaled kernel at `h y` removes its inverse argument scale. -/
theorem scaledMollifierKernel_smul (n : ℕ) (h : PositiveRadius) (y : Domain n) :
    scaledMollifierKernel n h (h.val • y) =
      (h.val ^ n)⁻¹ * fixedMollifierKernel n y := by
  simp only [scaledMollifierKernel, smul_smul,
    inv_mul_cancel₀ h.property.ne', one_smul]

private theorem fixedMollifierKernel_smul_eq_scaled {n q : ℕ}
    (u : Domain n → Ambient q) (h : PositiveRadius) (x y : Domain n) :
    fixedMollifierKernel n y • unitBallZeroExtension u (x - h.val • y) =
      (h.val ^ n) • (scaledMollifierKernel n h (h.val • y) •
        unitBallZeroExtension u (x - h.val • y)) := by
  rw [scaledMollifierKernel_smul, smul_smul, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero n h.property.ne'), one_mul]

/-- The unscaled kernel-weighted zero extension is integrable. -/
theorem fixedMollifierKernel_smul_zeroExtension_integrable {n q : ℕ}
    (u : Domain n → Ambient q) (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1))
    (h : PositiveRadius) (x : Domain n) :
    Integrable (fun y => fixedMollifierKernel n y •
      unitBallZeroExtension u (x - h.val • y)) volume := by
  have hscaled :=
    (scaledMollifierKernel_smul_zeroExtension_integrable u hu h x).comp_smul
      h.property.ne'
  exact (Integrable.smul (h.val ^ n) hscaled).congr
    (Filter.Eventually.of_forall fun y =>
      (fixedMollifierKernel_smul_eq_scaled u h x y).symm)

/-- Positive scaling gives the Lebesgue change-of-variables identity. -/
theorem fixedMollifierKernel_integral_zeroExtension_eq {n q : ℕ}
    (u : Domain n → Ambient q) (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1))
    (h : PositiveRadius) (x : Domain n) :
    (∫ y, fixedMollifierKernel n y • unitBallZeroExtension u (x - h.val • y)) =
      zeroExtendedMollification u hu h x := by
  calc
    (∫ y, fixedMollifierKernel n y • unitBallZeroExtension u (x - h.val • y)) =
        ∫ y, (h.val ^ n) • (scaledMollifierKernel n h (h.val • y) •
          unitBallZeroExtension u (x - h.val • y)) := by
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fixedMollifierKernel_smul_eq_scaled u h x))
    _ = (h.val ^ n) • ∫ y, scaledMollifierKernel n h (h.val • y) •
          unitBallZeroExtension u (x - h.val • y) := integral_smul _ _
    _ = (h.val ^ n) • ((h.val ^ n)⁻¹ •
          ∫ z, scaledMollifierKernel n h z • unitBallZeroExtension u (x - z)) := by
      rw [Measure.integral_comp_smul_of_nonneg volume
        (fun z => scaledMollifierKernel n h z • unitBallZeroExtension u (x - z))
        h.val (hR := h.property.le)]
      rw [finrank_euclideanSpace_fin]
    _ = zeroExtendedMollification u hu h x := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero n h.property.ne'), one_smul]
      rfl

/-- The fixed kernel vanishes outside the open unit ball. -/
theorem fixedMollifierKernel_zero_of_not_mem_unitBall {n : ℕ} {y : Domain n}
    (hy : y ∉ Metric.ball (0 : Domain n) 1) : fixedMollifierKernel n y = 0 := by
  by_contra hzero
  exact hy (fixedMollifierKernel_tsupport_subset_unitBall n
    (subset_tsupport _ (Function.mem_support.mpr hzero)))

private theorem weightedZeroExtension_eq_original {n q : ℕ}
    (u : Domain n → Ambient q) (h : PositiveRadius) (hh : h.val ≤ 1 / 4)
    {x : Domain n} (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    EqOn (fun y => fixedMollifierKernel n y •
      unitBallZeroExtension u (x - h.val • y))
      (fun y => fixedMollifierKernel n y • u (x - h.val • y))
      (Metric.ball (0 : Domain n) 1) := by
  intro y hy
  change fixedMollifierKernel n y • unitBallZeroExtension u (x - h.val • y) =
    fixedMollifierKernel n y • u (x - h.val • y)
  rw [unitBallZeroExtension, Set.indicator_of_mem
    (mollification_sampling_mem_unitBall h hh hx hy)]

/-- The literal source integrand is integrable on the unit ball at interior points. -/
theorem sourceMollification_integrableOn {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4) (x : Domain n)
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    IntegrableOn (fun y => fixedMollifierKernel n y • u (x - h.val • y))
      (Metric.ball (0 : Domain n) 1) := by
  exact (fixedMollifierKernel_smul_zeroExtension_integrable u hu h x).integrableOn.congr_fun
    (weightedZeroExtension_eq_original u h hh hx) measurableSet_ball

/-- The literal source integral agrees with the smooth zero-extension convolution. -/
theorem sourceMollification_eq_zeroExtended {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4) (x : Domain n)
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    (∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y)) =
      zeroExtendedMollification u hu h x := by
  calc
    (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)) =
        ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • unitBallZeroExtension u (x - h.val • y) :=
      (setIntegral_congr_fun measurableSet_ball
        (weightedZeroExtension_eq_original u h hh hx)).symm
    _ = ∫ y, fixedMollifierKernel n y •
          unitBallZeroExtension u (x - h.val • y) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [fixedMollifierKernel_zero_of_not_mem_unitBall hy, zero_smul]
    _ = zeroExtendedMollification u hu h x :=
      fixedMollifierKernel_integral_zeroExtension_eq u hu h x

end
end HarmonicMaps

end
