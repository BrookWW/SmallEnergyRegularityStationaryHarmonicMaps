module

public import HarmonicMaps.Analysis.MollificationL2Convergence
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds

/-!
# Full critical Morrey bounds for actual positive-kernel convolutions

The actual normalized smooth kernel averages the same global L2 columns.
Jensen and genuine Fubini reduce every ball energy to the original energy
on translated balls. The original complete critical supremum therefore
bounds the complete supremum of the same convolution, with factor one.
-/

public section

open HarmonicMaps MeasureTheory MeasureTheory.Measure Filter Set
open scoped ContDiff Topology ENNReal Convolution

namespace StationaryHarmonicMaps.Analysis

private theorem fixed_weighted_integrable_of_memLp {n m : ℕ}
    {F : Domain n → Ambient m} (hF : MemLp F 2 volume)
    (h : PositiveRadius) (x : Domain n) :
    Integrable (fun y => fixedMollifierKernel n y • F (x-h.val • y)) volume := by
  have hscaled : Integrable (fun z => scaledMollifierKernel n h z • F (x-z)) volume :=
    ((scaledMollifierKernel_hasCompactSupport n h).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMollifierKernel_contDiff n h).continuous
      (hF.locallyIntegrable (by norm_num)) x).integrable
  have hchange := Integrable.smul (h.val ^ n) (hscaled.comp_smul h.property.ne')
  apply hchange.congr
  exact Eventually.of_forall fun y => by
    change (h.val ^ n) • (scaledMollifierKernel n h (h.val • y) • F (x-h.val • y)) =
      fixedMollifierKernel n y • F (x-h.val • y)
    rw [scaledMollifierKernel_smul, smul_smul, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n h.property.ne'), one_mul]

private theorem fixed_average_jensen_of_memLp {n m : ℕ}
    {F : Domain n → Ambient m} (hF : MemLp F 2 volume)
    (h : PositiveRadius) (x : Domain n) :
    ‖∫ y, fixedMollifierKernel n y • F (x-h.val • y)‖ ^ 2 ≤
      ∫ y, fixedMollifierKernel n y * ‖F (x-h.val • y)‖ ^ 2 :=
  fixedMollifierProbability_norm_sq_integral_le
    (fixed_weighted_integrable_of_memLp hF h x)
    (weighted_shift_integrable (hF.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) h x)

/-- Actual global L2 data alone give a genuine smooth global L2 scaled convolution. -/
theorem scaledMollifier_convolution_contDiff_memLp {n m : ℕ}
    (F : Domain n → Ambient m) (hF : MemLp F 2 volume) (h : PositiveRadius) :
    ContDiff ℝ ∞ (fun x => ∫ z, scaledMollifierKernel n h z • F (x-z)) ∧
      MemLp (fun x => ∫ z, scaledMollifierKernel n h z • F (x-z)) 2 volume := by
  have hCD : ContDiff ℝ ∞ (fun x => ∫ z, scaledMollifierKernel n h z • F (x-z)) :=
    (scaledMollifierKernel_hasCompactSupport n h).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMollifierKernel_contDiff n h)
      (hF.locallyIntegrable (by norm_num))
  let M := fun x => ∫ y, fixedMollifierKernel n y • F (x-h.val • y)
  have heq : M = (fun x => ∫ z, scaledMollifierKernel n h z • F (x-z)) :=
    funext (fixedKernelAverage_eq_scaledConvolution F h)
  have hM : ContDiff ℝ ∞ M := by rw [heq];exact hCD
  have hJoint := weighted_shift_joint_integrable
    (hF.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) h
  have hMI : Integrable (fun x => ‖M x‖ ^ 2) volume := by
    apply hJoint.integral_prod_left.mono' (hM.continuous.aestronglyMeasurable.norm.pow 2)
    exact Eventually.of_forall fun x => by
      change ‖‖M x‖ ^ 2‖ ≤ ∫ y, fixedMollifierKernel n y * ‖F (x-h.val • y)‖ ^ 2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact fixed_average_jensen_of_memLp hF h x
  have hML := (memLp_two_iff_integrable_sq_norm hM.continuous.aestronglyMeasurable).mpr hMI
  rw [heq] at hML
  exact ⟨hCD,hML⟩

private theorem integral_ball_translate {n : ℕ}
    (g : Domain n → ℝ) (a v : Domain n) (r : ℝ) :
    (∫ x in Metric.ball a r, g (x-v)) = ∫ x in Metric.ball (a-v) r, g x := by
  have hpre : (fun x : Domain n => x-v) ⁻¹' Metric.ball (a-v) r = Metric.ball a r := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_sub_right]
  have H := (measurePreserving_sub_right volume v).setIntegral_preimage_emb
    (Homeomorph.subRight v).measurableEmbedding g (Metric.ball (a-v) r)
  rw [hpre] at H
  exact H

private theorem fixed_average_hs_jensen {n m : ℕ}
    (F : Domain n → Gradient n m) (hF : ∀ i, MemLp (fun x => F x i) 2 volume)
    (h : PositiveRadius) (x : Domain n) :
    hsNormSq (fun i => ∫ y, fixedMollifierKernel n y • F (x-h.val • y) i) ≤
      ∫ y, fixedMollifierKernel n y * hsNormSq (F (x-h.val • y)) := by
  calc
    _ ≤ ∑ i : Fin n, ∫ y, fixedMollifierKernel n y * ‖F (x-h.val • y) i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => fixed_average_jensen_of_memLp (hF i) h x
    _ = ∫ y, ∑ i : Fin n, fixedMollifierKernel n y * ‖F (x-h.val • y) i‖ ^ 2 :=
      (integral_finsetSum _ (fun i _ => weighted_shift_integrable
        ((hF i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) h x)).symm
    _ = _ := by simp only [hsNormSq, Finset.mul_sum]

private theorem fixed_average_hs_ball_le {n m : ℕ}
    (F : Domain n → Gradient n m) (hF : ∀ i, MemLp (fun x => F x i) 2 volume)
    (h : PositiveRadius) {M : ℝ} (hM : 0 ≤ M)
    (hcritical : criticalGradientMorreySquare F univ ≤ ENNReal.ofReal M)
    (a : Domain n) {r : ℝ} (hr : 0 < r) :
    (∫ x in Metric.ball a r,
      hsNormSq (fun i => ∫ y, fixedMollifierKernel n y • F (x-h.val • y) i)) ≤
      M * r ^ ((n : ℝ)-2) := by
  let G := fun x i => ∫ y, fixedMollifierKernel n y • F (x-h.val • y) i
  have hG (i : Fin n) : MemLp (fun x => G x i) 2 volume := by
    change MemLp (fun x => ∫ y, fixedMollifierKernel n y • F (x-h.val • y) i) 2 volume
    exact MemLp.ae_eq (Eventually.of_forall fun x =>
      (fixedKernelAverage_eq_scaledConvolution (fun y => F y i) h x).symm)
      (scaledMollifier_convolution_contDiff_memLp (fun x => F x i) (hF i) h).2
  have hJoint := weighted_shift_joint_integrable (integrable_hsNormSq_of_columns F hF) h
  have hJS : Integrable (fun p : Domain n × Domain n => fixedMollifierKernel n p.2 *
      hsNormSq (F (p.1-h.val • p.2))) ((volume.restrict (Metric.ball a r)).prod volume) := by
    have H := hJoint.integrableOn (s := Metric.ball a r ×ˢ (univ : Set (Domain n)))
    change Integrable _ ((volume.prod volume).restrict (Metric.ball a r ×ˢ (univ : Set (Domain n)))) at H
    rw [← Measure.prod_restrict] at H
    simpa only [Measure.restrict_univ] using H
  have hMajorant : Integrable (fun y => fixedMollifierKernel n y *
      ∫ x in Metric.ball a r, hsNormSq (F (x-h.val • y))) volume := by
    simpa only [integral_const_mul] using hJS.integral_prod_right
  have hball (y : Domain n) : (∫ x in Metric.ball a r, hsNormSq (F (x-h.val • y))) ≤
      M * r ^ ((n : ℝ)-2) := by
    rw [integral_ball_translate (fun x => hsNormSq (F x)) a (h.val • y) r]
    exact integral_hsNormSq_le_of_criticalMorrey F (mem_univ _) hr hM
      (subset_inter (Subset.refl _) (subset_univ _)) (fun i => (hF i).restrict _) hcritical
  calc
    _ ≤ ∫ x in Metric.ball a r, ∫ y, fixedMollifierKernel n y * hsNormSq (F (x-h.val • y)) :=
      integral_mono (integrable_hsNormSq_of_columns G hG).integrableOn hJS.integral_prod_left
        (fun x => fixed_average_hs_jensen F hF h x)
    _ = ∫ y, fixedMollifierKernel n y * ∫ x in Metric.ball a r, hsNormSq (F (x-h.val • y)) := by
      rw [integral_integral_swap hJS]
      simp only [integral_const_mul]
    _ ≤ ∫ y, fixedMollifierKernel n y * (M * r ^ ((n : ℝ)-2)) :=
      integral_mono hMajorant ((fixedMollifierKernel_integrable n).mul_const _)
        (fun y => mul_le_mul_of_nonneg_left (hball y) (fixedMollifierKernel_nonneg n y))
    _ = _ := by rw [integral_mul_const, fixedMollifierKernel_integral, one_mul]

/-- Positive normalized convolution preserves the literal complete global critical Morrey square with factor one. -/
theorem criticalGradientMorreySquare_scaledMollifier_convolution_le {n m : ℕ}
    (F : Domain n → Gradient n m) (hF : ∀ i, MemLp (fun x => F x i) 2 volume)
    (h : PositiveRadius) {K : ℝ}
    (hcritical : criticalGradientMorreySquare F univ ≤ ENNReal.ofReal K) :
    criticalGradientMorreySquare
      (fun x i => ∫ z, scaledMollifierKernel n h z • F (x-z) i) univ ≤ ENNReal.ofReal K := by
  let M := max K 0
  have hM : 0 ≤ M := le_max_right _ _
  have hcriticalM : criticalGradientMorreySquare F univ ≤ ENNReal.ofReal M :=
    hcritical.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  let G := fun x i => ∫ z, scaledMollifierKernel n h z • F (x-z) i
  have hG (i : Fin n) : MemLp (fun x => G x i) 2 volume :=
    (scaledMollifier_convolution_contDiff_memLp (fun x => F x i) (hF i) h).2
  have hball (a : Domain n) (r : PositiveRadius) :
      (∫ x in Metric.ball a r.val, hsNormSq (G x)) ≤ M * r.val ^ ((n : ℝ)-2) := by
    have H := fixed_average_hs_ball_le F hF h hM hcriticalM a r.property
    have heq (x : Domain n) (i : Fin n) :
        (∫ y, fixedMollifierKernel n y • F (x-h.val • y) i) =
          ∫ z, scaledMollifierKernel n h z • F (x-z) i :=
      fixedKernelAverage_eq_scaledConvolution (fun y => F y i) h x
    simp_rw [heq] at H
    exact H
  have htoReal (r : PositiveRadius) :
      r.val ^ (2-(n : ℤ)) * r.val ^ ((n : ℝ)-2) = 1 := by
    rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
      ← Real.rpow_add r.property]
    norm_num
  unfold criticalGradientMorreySquare
  refine iSup_le fun a => iSup_le fun r => ?_
  change ENNReal.ofReal (r.val ^ (2-(n : ℤ))) *
    dirichletEnergy G (Metric.ball a.val r.val ∩ univ) ≤ ENNReal.ofReal K
  rw [inter_univ, dirichletEnergy_eq_ofReal_integral
    (integrable_hsNormSq_of_columns G hG).integrableOn,
    ← ENNReal.ofReal_mul (zpow_nonneg r.property.le _)]
  calc
    _ ≤ ENNReal.ofReal (r.val ^ (2-(n : ℤ)) * (M * r.val ^ ((n : ℝ)-2))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hball a.val r)
        (zpow_nonneg r.property.le _))
    _ = ENNReal.ofReal M := by
      congr 1
      rw [mul_left_comm, htoReal, mul_one]
    _ = ENNReal.ofReal K := by simp only [M, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]

end StationaryHarmonicMaps.Analysis

end
