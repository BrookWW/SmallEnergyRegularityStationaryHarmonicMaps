module

public import HarmonicMaps.Analysis.SobolevMollificationGradient
public import HarmonicMaps.Analysis.L2TranslationContinuity
public import HarmonicMaps.Analysis.MollificationJensen
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# L2 convergence of the fixed kernel averages

Jensen's inequality and Fubini reduce the square error to averaged translation
errors. Strong continuity of L2 translations and dominated convergence give
the limit for every positive scale tending to zero.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ContDiff ENNReal Topology Convolution

namespace HarmonicMaps

noncomputable section

/-- The probability average at a positive scale is the scaled convolution. -/
theorem fixedKernelAverage_eq_scaledConvolution {n q : ℕ}
    (F : Domain n → Ambient q) (h : PositiveRadius) (x : Domain n) :
    (∫ y, fixedMollifierKernel n y • F (x - h.val • y)) =
      ∫ z, scaledMollifierKernel n h z • F (x - z) := by
  have heq (y : Domain n) : fixedMollifierKernel n y • F (x - h.val • y) =
      (h.val ^ n) • (scaledMollifierKernel n h (h.val • y) • F (x - h.val • y)) := by
    rw [scaledMollifierKernel_smul, smul_smul, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n h.property.ne'), one_mul]
  calc
    (∫ y, fixedMollifierKernel n y • F (x - h.val • y)) =
        ∫ y, (h.val ^ n) • (scaledMollifierKernel n h (h.val • y) •
          F (x - h.val • y)) := integral_congr_ae (Eventually.of_forall heq)
    _ = (h.val ^ n) • ∫ y, scaledMollifierKernel n h (h.val • y) •
        F (x - h.val • y) := integral_smul _ _
    _ = (h.val ^ n) • ((h.val ^ n)⁻¹ •
        ∫ z, scaledMollifierKernel n h z • F (x - z)) := by
      rw [Measure.integral_comp_smul_of_nonneg volume
        (fun z => scaledMollifierKernel n h z • F (x - z)) h.val
        (hR := h.property.le), finrank_euclideanSpace_fin]
    _ = ∫ z, scaledMollifierKernel n h z • F (x - z) := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero n h.property.ne'), one_smul]

theorem fixedKernelAverage_contDiff {n q : ℕ} {F : Domain n → Ambient q}
    (hF : Integrable F volume) (h : PositiveRadius) :
    ContDiff ℝ ∞ (fun x => ∫ y, fixedMollifierKernel n y • F (x - h.val • y)) := by
  simp_rw [fixedKernelAverage_eq_scaledConvolution F h]
  exact (scaledMollifierKernel_hasCompactSupport n h).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMollifierKernel_contDiff n h)
    hF.locallyIntegrable

private theorem integral_norm_sq_eq_toReal_eLpNorm_sq {n q : ℕ}
    {F : Domain n → Ambient q} (hF : MemLp F 2 volume) :
    (∫ x, ‖F x‖ ^ 2) = (eLpNorm F 2 volume).toReal ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
    (hF.aestronglyMeasurable.norm.pow 2)]
  rw [← ENNReal.toReal_pow]
  congr 1
  rw [← ENNReal.rpow_natCast]
  convert (eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := volume)
    (p := (2 : NNReal)) (by norm_num)).symm using 1
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  norm_cast
  all_goals norm_num

private theorem norm_sub_sq_le_two {q : ℕ} (v w : Ambient q) :
    ‖v - w‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have hn := norm_sub_le v w
  have hnn := norm_nonneg (v - w)
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  nlinarith only [hn, hnn, hv, hw, sq_nonneg (‖v‖ - ‖w‖)]

private theorem weighted_translationError_integrable {n q : ℕ}
    {F : Domain n → Ambient q} (hF : Integrable F volume)
    (hF2 : MemLp F 2 volume) (h : PositiveRadius) (x : Domain n) :
    Integrable (fun y => fixedMollifierKernel n y *
      ‖F (x - h.val • y) - F x‖ ^ 2) volume := by
  have hsq := hF2.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hdom : Integrable (fun y => 2 * (fixedMollifierKernel n y *
      ‖F (x - h.val • y)‖ ^ 2 + fixedMollifierKernel n y * ‖F x‖ ^ 2)) volume :=
    ((weighted_shift_integrable hsq h x).add
      ((fixedMollifierKernel_integrable n).mul_const (‖F x‖ ^ 2))).const_mul 2
  have hshift := (hF.comp_sub_left x).comp_smul h.property.ne'
  have hm : AEStronglyMeasurable (fun y => fixedMollifierKernel n y *
      ‖F (x - h.val • y) - F x‖ ^ 2) volume :=
    (fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable.mul
      ((hshift.aestronglyMeasurable.sub aestronglyMeasurable_const).norm.pow 2)
  apply hdom.mono' hm
  exact Eventually.of_forall fun y => by
    rw [Real.norm_of_nonneg (mul_nonneg (fixedMollifierKernel_nonneg n y) (sq_nonneg _))]
    calc
      fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 ≤
          fixedMollifierKernel n y * (2 * (‖F (x - h.val • y)‖ ^ 2 + ‖F x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (norm_sub_sq_le_two _ _) (fixedMollifierKernel_nonneg n y)
      _ = 2 * (fixedMollifierKernel n y * ‖F (x - h.val • y)‖ ^ 2 +
          fixedMollifierKernel n y * ‖F x‖ ^ 2) := by ring

private theorem weighted_translationError_joint_integrable {n q : ℕ}
    {F : Domain n → Ambient q} (hF : MemLp F 2 volume) (h : PositiveRadius) :
    Integrable (fun p : Domain n × Domain n => fixedMollifierKernel n p.2 *
      ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2) (volume.prod volume) := by
  have hsq := hF.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hprod : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖F p.1‖ ^ 2) (volume.prod volume) := by
    simpa only [mul_comm] using hsq.mul_prod (fixedMollifierKernel_integrable n)
  have hdom := ((weighted_shift_joint_integrable hsq h).add hprod).const_mul 2
  have hshift : QuasiMeasurePreserving
      (fun p : Domain n × Domain n => p.1 - h.val • p.2)
      (volume.prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
    exact Eventually.of_forall fun y =>
      (measurePreserving_sub_right volume (h.val • y)).quasiMeasurePreserving
  have hm : AEStronglyMeasurable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2)
      (volume.prod volume) :=
    ((fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable.comp_snd).mul
      (((hF.aestronglyMeasurable.comp_quasiMeasurePreserving hshift).sub
        hF.aestronglyMeasurable.comp_fst).norm.pow 2)
  apply hdom.mono' hm
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (mul_nonneg (fixedMollifierKernel_nonneg n p.2) (sq_nonneg _))]
    calc
      fixedMollifierKernel n p.2 * ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2 ≤
          fixedMollifierKernel n p.2 * (2 * (‖F (p.1 - h.val • p.2)‖ ^ 2 + ‖F p.1‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (norm_sub_sq_le_two _ _) (fixedMollifierKernel_nonneg n p.2)
      _ = 2 * (fixedMollifierKernel n p.2 * ‖F (p.1 - h.val • p.2)‖ ^ 2 +
          fixedMollifierKernel n p.2 * ‖F p.1‖ ^ 2) := by ring

private theorem fixedKernelAverage_error_jensen {n q : ℕ}
    {F : Domain n → Ambient q} (hF : Integrable F volume)
    (hF2 : MemLp F 2 volume) (h : PositiveRadius) (x : Domain n) :
    ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2 ≤
      ∫ y, fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 := by
  have hweight : Integrable (fun y => fixedMollifierKernel n y •
      (F (x - h.val • y) - F x)) volume := by
    exact ((weighted_shift_integrable hF h x).sub
      ((fixedMollifierKernel_integrable n).smul_const (F x))).congr
      (Eventually.of_forall fun y => by simp only [Pi.sub_apply, smul_sub])
  have hj := fixedMollifierProbability_norm_sq_integral_le hweight
    (weighted_translationError_integrable hF hF2 h x)
  simpa only [smul_sub, integral_sub (weighted_shift_integrable hF h x)
    ((fixedMollifierKernel_integrable n).smul_const (F x)), integral_smul_const,
    fixedMollifierKernel_integral, one_smul] using hj

/-- Global L2 membership of the actual fixed-kernel average. -/
theorem fixedKernelAverage_memLp {n q : ℕ} {F : Domain n → Ambient q}
    (hF : Integrable F volume) (hF2 : MemLp F 2 volume) (h : PositiveRadius) :
    MemLp (fun x => ∫ y, fixedMollifierKernel n y • F (x - h.val • y)) 2 volume := by
  have hJoint := weighted_translationError_joint_integrable hF2 h
  have hm := ((fixedKernelAverage_contDiff hF h).continuous.aestronglyMeasurable.sub
    hF2.aestronglyMeasurable)
  have herror : Integrable (fun x =>
      ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2) volume := by
    apply hJoint.integral_prod_left.mono' (hm.norm.pow 2)
    exact Eventually.of_forall fun x => by
      change ‖‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2‖ ≤ _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact fixedKernelAverage_error_jensen hF hF2 h x
  have herrorLp := (memLp_two_iff_integrable_sq_norm hm).mpr herror
  have hsum := herrorLp.add hF2
  simpa only [Pi.add_apply, Pi.sub_apply, sub_add_cancel] using hsum

private theorem fixedKernelAverage_integral_error_sq_le {n q : ℕ}
    {F : Domain n → Ambient q} (hF : Integrable F volume)
    (hF2 : MemLp F 2 volume) (h : PositiveRadius) :
    (∫ x, ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2) ≤
      ∫ y, fixedMollifierKernel n y * ∫ x, ‖F (x - h.val • y) - F x‖ ^ 2 := by
  have hJoint := weighted_translationError_joint_integrable hF2 h
  calc
    (∫ x, ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2) ≤
        ∫ x, ∫ y, fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 :=
      integral_mono (((fixedKernelAverage_memLp hF hF2 h).sub hF2).integrable_norm_pow
        (by decide : (2 : ℕ) ≠ 0)) hJoint.integral_prod_left
        (fun x => fixedKernelAverage_error_jensen hF hF2 h x)
    _ = ∫ y, ∫ x, fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 :=
      integral_integral_swap hJoint
    _ = ∫ y, fixedMollifierKernel n y * ∫ x, ‖F (x - h.val • y) - F x‖ ^ 2 := by
      simp only [integral_const_mul]

private theorem integral_translationError_sq_le {n q : ℕ} {F : Domain n → Ambient q}
    (hF : MemLp F 2 volume) (v : Domain n) :
    (∫ x, ‖F (x - v) - F x‖ ^ 2) ≤ 4 * ∫ x, ‖F x‖ ^ 2 := by
  have hsq := hF.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hshift : MemLp (fun x => F (x - v)) 2 volume :=
    hF.comp_measurePreserving (measurePreserving_sub_right volume v)
  calc
    (∫ x, ‖F (x - v) - F x‖ ^ 2) ≤
        ∫ x, 2 * (‖F (x - v)‖ ^ 2 + ‖F x‖ ^ 2) :=
      integral_mono ((hshift.sub hF).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
        (((hsq.comp_sub_right v).add hsq).const_mul 2) (fun x => norm_sub_sq_le_two _ _)
    _ = 4 * ∫ x, ‖F x‖ ^ 2 := by
      rw [integral_const_mul, integral_add (hsq.comp_sub_right v) hsq]
      rw [show (∫ x, ‖F (x - v)‖ ^ 2) = ∫ x, ‖F x‖ ^ 2 from
        integral_sub_right_eq_self (fun x => ‖F x‖ ^ 2) v]
      ring

private theorem tendsto_integral_translationError_sq {n q : ℕ}
    {F : Domain n → Ambient q} (hF : MemLp F 2 volume) :
    Tendsto (fun v : Domain n => ∫ x, ‖F (x - v) - F x‖ ^ 2) (𝓝 0) (𝓝 0) := by
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
    (tendsto_eLpNorm_translation_sub hF)
  have ht2 := ht.pow 2
  simp only [Function.comp_apply, ENNReal.toReal_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0)] at ht2
  apply ht2.congr'
  exact Eventually.of_forall fun v => by
    have hdiff : MemLp (fun x => F (x - v) - F x) 2 volume :=
      (hF.comp_measurePreserving (measurePreserving_sub_right volume v)).sub hF
    exact (integral_norm_sq_eq_toReal_eLpNorm_sq hdiff).symm

private theorem tendsto_integral_weighted_translationError_sq {n q : ℕ}
    {F : Domain n → Ambient q} (hF : MemLp F 2 volume) :
    Tendsto (fun h : PositiveRadius => ∫ y, fixedMollifierKernel n y *
      ∫ x, ‖F (x - h.val • y) - F x‖ ^ 2)
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := by
  have hh : Tendsto (fun h : PositiveRadius => h.val)
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := tendsto_comap
  have hm (h : PositiveRadius) : AEStronglyMeasurable (fun y =>
      fixedMollifierKernel n y * ∫ x, ‖F (x - h.val • y) - F x‖ ^ 2) volume := by
    simpa only [integral_const_mul] using
      (weighted_translationError_joint_integrable hF h).integral_prod_right.aestronglyMeasurable
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ)))
    (F := fun h y => fixedMollifierKernel n y * ∫ x, ‖F (x - h.val • y) - F x‖ ^ 2)
    (f := fun _ => (0 : ℝ))
    (fun y => fixedMollifierKernel n y * (4 * ∫ x, ‖F x‖ ^ 2))
    (Eventually.of_forall hm) ?_
    ((fixedMollifierKernel_integrable n).mul_const (4 * ∫ x, ‖F x‖ ^ 2)) ?_
  · simpa only [integral_zero] using hd
  · exact Eventually.of_forall fun h => Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (mul_nonneg (fixedMollifierKernel_nonneg n y)
        (integral_nonneg fun _ => sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (integral_translationError_sq_le hF _)
        (fixedMollifierKernel_nonneg n y)
  · exact Eventually.of_forall fun y => by
      have hv : Tendsto (fun h : PositiveRadius => h.val • y)
          (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := by
        simpa only [zero_smul] using hh.smul_const y
      simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
        ((tendsto_integral_translationError_sq hF).comp hv)

/-- The actual fixed-kernel averages converge in global L2 as the positive scale tends to zero. -/
theorem tendsto_eLpNorm_fixedKernelAverage_sub {n q : ℕ}
    {F : Domain n → Ambient q} (hF : Integrable F volume) (hF2 : MemLp F 2 volume) :
    Tendsto (fun h : PositiveRadius => eLpNorm
      (fun x => (∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x) 2 volume)
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := by
  have hsq : Tendsto (fun h : PositiveRadius => ∫ x,
      ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2)
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_integral_weighted_translationError_sq hF2)
      (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun h => fixedKernelAverage_integral_error_sq_le hF hF2 h)
  have hnorm := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  simpa only [Real.sqrt_zero, ENNReal.ofReal_zero] using hnorm.congr'
    (Eventually.of_forall fun h => by
      have herrorLp : MemLp (fun x =>
          (∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x) 2 volume :=
        (fixedKernelAverage_memLp hF hF2 h).sub hF2
      simp only [Function.comp_apply]
      rw [integral_norm_sq_eq_toReal_eLpNorm_sq herrorLp,
        Real.sqrt_sq (ENNReal.toReal_nonneg), ENNReal.ofReal_toReal herrorLp.eLpNorm_ne_top])

end
end HarmonicMaps

end
