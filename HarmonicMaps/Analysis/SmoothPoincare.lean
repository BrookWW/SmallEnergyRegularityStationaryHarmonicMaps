module

public import HarmonicMaps.Analysis.BallVariance
public import HarmonicMaps.Analysis.BallSegmentEnergy
public import HarmonicMaps.Analysis.BallAffineEnergy

/-!
# Smooth Poincare estimate on a Euclidean ball

The proof combines the variance identity, the fundamental theorem along
segments, and the two affine changes of variables on the parameter halves.
Smoothness and square-integrability are required only on the source ball.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The vector-valued smooth Poincare estimate with the source HS constant.
The classical derivative is used only on the open ball, where local smoothness
certifies differentiability. Function and derivative L2 data are ball-local. -/
theorem smoothPoincare_ball {n q : ℕ} (a : Domain n) {r : ℝ} (hr : 0 < r)
    {f : Domain n → Ambient q}
    (hsmooth : ContDiffOn ℝ ∞ f (Metric.ball a r))
    (hf : MemLp f 2 (volume.restrict (Metric.ball a r)))
    (hDf : ∀ i : Fin n, MemLp (fun x =>
      fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (volume.restrict (Metric.ball a r))) :
    (∫ x in Metric.ball a r, ‖f x - ⨍ y in Metric.ball a r, f y‖ ^ 2) ≤
      (2 : ℝ) ^ (n + 1) * r ^ 2 * ∫ x in Metric.ball a r,
        hsNormSq (fun i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  classical
  let B := Metric.ball a r
  let G : Domain n → ℝ := fun x =>
    hsNormSq (fun i => fderiv ℝ f x (EuclideanSpace.single i 1))
  let g : Domain n → ℝ := B.indicator G
  let μ := volume.restrict B
  have hGcont : ContinuousOn G B := continuousOn_hsNormSq_fderiv hsmooth
  have hgm : Measurable g := by
    exact hGcont.measurable_piecewise continuousOn_const measurableSet_ball
  have hGi : Integrable G μ := integrable_hsNormSq_of_memLp_columns hDf
  have hgi : Integrable g μ := hGi.congr (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (indicator_of_mem hx G).symm)
  have hgn : ∀ x ∈ B, 0 ≤ g x := by
    intro x hx
    simpa only [g, indicator_of_mem hx] using hsNormSq_nonneg
      (fun i => fderiv ℝ f x (EuclideanSpace.single i 1))
  have hAffine := ball_affine_integrable_and_integral_le hgm hgn hgi
  have hSegmentInt := ball_affine_segmentIntegral_integrable hgm hgn hgi
  have hDiffInt := integrable_sq_norm_sub_prod_ball a hf
  have hPairBound :
      (∫ p : Domain n × Domain n, ‖f p.1 - f p.2‖ ^ 2 ∂μ.prod μ) ≤
        4 * r ^ 2 * ∫ p : Domain n × Domain n,
          (∫ t in Icc (0 : ℝ) 1, g ((1 - t) • p.1 + t • p.2)) ∂μ.prod μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hDiffInt (hSegmentInt.const_mul _)
    change ∀ᵐ p ∂(volume.restrict B).prod (volume.restrict B), _
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)] with p hp
    have hEq : (∫ t in Icc (0 : ℝ) 1, g ((1 - t) • p.1 + t • p.2)) =
        ∫ t in Icc (0 : ℝ) 1, G ((1 - t) • p.1 + t • p.2) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact indicator_of_mem (segmentPoint_mem_ball hp.1 hp.2 ht) G
    rw [hEq]
    exact ball_segment_energy_bound_Icc hsmooth hp.1 hp.2 hr
  have hDoubleBound : (∫ x in B, ∫ y in B, ‖f x - f y‖ ^ 2) ≤
      4 * r ^ 2 * ((2 : ℝ) ^ n * volume.real B * ∫ z in B, G z) := by
    rw [integral_prod _ hDiffInt, integral_prod _ hSegmentInt] at hPairBound
    have hEstimate := mul_le_mul_of_nonneg_left hAffine.2
      (by positivity : 0 ≤ 4 * r ^ 2)
    rw [ball_setIntegral_indicator a r G] at hEstimate
    exact hPairBound.trans hEstimate
  have hmass : 0 < volume.real B :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume a hr).ne' measure_ball_ne_top
  rw [integral_sq_norm_sub_average_ball_eq_doubleIntegral a hr hf]
  calc
    (1 / (2 * volume.real B)) * (∫ x in B, ∫ y in B, ‖f x - f y‖ ^ 2) ≤
        (1 / (2 * volume.real B)) *
          (4 * r ^ 2 * ((2 : ℝ) ^ n * volume.real B * ∫ z in B, G z)) :=
      mul_le_mul_of_nonneg_left hDoubleBound (by positivity)
    _ = (2 : ℝ) ^ (n + 1) * r ^ 2 * ∫ z in B, G z := by
      rw [pow_succ]
      field_simp
      ring

end HarmonicMaps
