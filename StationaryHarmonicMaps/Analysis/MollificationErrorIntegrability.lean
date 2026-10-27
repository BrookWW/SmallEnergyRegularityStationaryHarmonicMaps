module

public import HarmonicMaps.Analysis.MollificationL2Convergence

/-! # Actual Jensen and Fubini bounds for restricted mollification errors -/

public section

open HarmonicMaps MeasureTheory MeasureTheory.Measure Filter Set

namespace StationaryHarmonicMaps.Analysis

private theorem norm_sub_sq_le_two {q : ℕ} (v w : Ambient q) :
    ‖v - w‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have hn := norm_sub_le v w
  nlinarith only [hn, norm_nonneg (v - w), norm_nonneg v, norm_nonneg w,
    sq_nonneg (‖v‖ - ‖w‖)]

private theorem weighted_error_integrable {n q : ℕ} {F : Domain n → Ambient q}
    (hF : Integrable F volume) (hF2 : MemLp F 2 volume) (h : PositiveRadius) (x : Domain n) :
    Integrable (fun y => fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2) volume := by
  have hsq := hF2.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hdom : Integrable (fun y => 2 * (fixedMollifierKernel n y *
      ‖F (x - h.val • y)‖ ^ 2 + fixedMollifierKernel n y * ‖F x‖ ^ 2)) volume := by
    simpa only [smul_eq_mul, Pi.add_apply] using ((weighted_shift_integrable hsq h x).add
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
      _ ≤ fixedMollifierKernel n y * (2 * (‖F (x - h.val • y)‖ ^ 2 + ‖F x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (norm_sub_sq_le_two _ _) (fixedMollifierKernel_nonneg n y)
      _ = _ := by ring

private theorem weighted_error_joint_integrable {n q : ℕ} {F : Domain n → Ambient q}
    (hF2 : MemLp F 2 volume) (h : PositiveRadius) :
    Integrable (fun p : Domain n × Domain n => fixedMollifierKernel n p.2 *
      ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2) (volume.prod volume) := by
  have hsq := hF2.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hprod : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖F p.1‖ ^ 2) (volume.prod volume) := by
    simpa only [mul_comm] using hsq.mul_prod (fixedMollifierKernel_integrable n)
  have hdom : Integrable (fun p : Domain n × Domain n => 2 *
      (fixedMollifierKernel n p.2 * ‖F (p.1 - h.val • p.2)‖ ^ 2 +
        fixedMollifierKernel n p.2 * ‖F p.1‖ ^ 2)) (volume.prod volume) :=
    ((weighted_shift_joint_integrable hsq h).add hprod).const_mul 2
  have hshift : QuasiMeasurePreserving (fun p : Domain n × Domain n => p.1 - h.val • p.2)
      (volume.prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
    exact Eventually.of_forall fun y =>
      (measurePreserving_sub_right volume (h.val • y)).quasiMeasurePreserving
  have hm : AEStronglyMeasurable (fun p : Domain n × Domain n => fixedMollifierKernel n p.2 *
      ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2) (volume.prod volume) :=
    ((fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable.comp_snd).mul
      (((hF2.aestronglyMeasurable.comp_quasiMeasurePreserving hshift).sub
        hF2.aestronglyMeasurable.comp_fst).norm.pow 2)
  apply hdom.mono' hm
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (mul_nonneg (fixedMollifierKernel_nonneg n p.2) (sq_nonneg _))]
    calc
      _ ≤ fixedMollifierKernel n p.2 * (2 * (‖F (p.1 - h.val • p.2)‖ ^ 2 + ‖F p.1‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (norm_sub_sq_le_two _ _) (fixedMollifierKernel_nonneg n p.2)
      _ = _ := by ring

private theorem kernel_error_jensen {n q : ℕ} {F : Domain n → Ambient q}
    (hF : Integrable F volume) (hF2 : MemLp F 2 volume) (h : PositiveRadius) (x : Domain n) :
    ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2 ≤
      ∫ y, fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 := by
  have hweight : Integrable (fun y => fixedMollifierKernel n y •
      (F (x - h.val • y) - F x)) volume := by
    exact ((weighted_shift_integrable hF h x).sub
      ((fixedMollifierKernel_integrable n).smul_const (F x))).congr
        (Eventually.of_forall fun y => by simp only [Pi.sub_apply, smul_sub])
  have H := fixedMollifierProbability_norm_sq_integral_le hweight
    (weighted_error_integrable hF hF2 h x)
  simpa only [smul_sub, integral_sub (weighted_shift_integrable hF h x)
    ((fixedMollifierKernel_integrable n).smul_const (F x)), integral_smul_const,
    fixedMollifierKernel_integral, one_smul] using H

/-- The restricted error and its actual translation-error majorant are integrable and satisfy Jensen. -/
theorem fixed_kernel_average_restricted_error_sq_le {n q : ℕ} {F : Domain n → Ambient q}
    (hF : Integrable F volume) (hF2 : MemLp F 2 volume) (h : PositiveRadius)
    (S : Set (Domain n)) :
    Integrable (fun y => fixedMollifierKernel n y *
      ∫ x in S, ‖F (x - h.val • y) - F x‖ ^ 2) volume ∧
    (∫ x in S, ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2) ≤
      ∫ y, fixedMollifierKernel n y * ∫ x in S, ‖F (x - h.val • y) - F x‖ ^ 2 := by
  have hJ := weighted_error_joint_integrable hF2 h
  have hJS : Integrable (fun p : Domain n × Domain n => fixedMollifierKernel n p.2 *
      ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2) ((volume.restrict S).prod volume) := by
    have H := hJ.integrableOn (s := S ×ˢ (univ : Set (Domain n)))
    change Integrable _ ((volume.prod volume).restrict (S ×ˢ (univ : Set (Domain n)))) at H
    rw [← Measure.prod_restrict] at H
    simpa only [Measure.restrict_univ] using H
  refine ⟨?_, ?_⟩
  · simpa only [integral_const_mul] using hJS.integral_prod_right
  · calc
      _ ≤ ∫ x in S, ∫ y, fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 :=
        integral_mono ((((fixedKernelAverage_memLp hF hF2 h).sub hF2).integrable_norm_pow
          (by decide : (2 : ℕ) ≠ 0)).integrableOn) hJS.integral_prod_left
            (fun x => kernel_error_jensen hF hF2 h x)
      _ = ∫ y, ∫ x in S, fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 :=
        integral_integral_swap hJS
      _ = _ := by simp only [integral_const_mul]

end StationaryHarmonicMaps.Analysis

end
