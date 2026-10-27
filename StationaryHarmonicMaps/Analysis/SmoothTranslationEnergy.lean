module

public import StationaryHarmonicMaps.Analysis.TranslationLocalization
public import HarmonicMaps.Analysis.BallSegmentEnergy
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual interior L2 translation energy for smooth maps -/

public section

open HarmonicMaps MeasureTheory Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The actual segment energy and translation invariance give the sharp L2 displacement factor. -/
theorem smooth_integral_translation_sub_sq_le {n q : ℕ}
    (f : Domain n → Ambient q) (hf : ContDiff ℝ ∞ f) (a : Domain n)
    {r R : ℝ} (_hr : 0 < r) (hrR : r < R) (h : Domain n) (hh : ‖h‖ ≤ R - r)
    (hDf : ∀ i : Fin n, MemLp
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2
        (volume.restrict (Metric.ball a R))) :
    (∫ x in Metric.ball a r, ‖f (x + h) - f x‖ ^ 2) ≤
      ‖h‖ ^ 2 * ∫ x in Metric.ball a R,
        hsNormSq (fun i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  classical
  let G : Domain n → ℝ := fun x =>
    hsNormSq (fun i => fderiv ℝ f x (EuclideanSpace.single i 1))
  have hGcont : Continuous G := by
    unfold G hsNormSq
    exact continuous_finsetSum _ fun i _ =>
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2
  have hGI : IntegrableOn G (Metric.ball a R) volume :=
    integrable_hsNormSq_of_memLp_columns hDf
  have hGn (x : Domain n) : 0 ≤ G x := hsNormSq_nonneg _
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖t • h‖ ≤ R - r := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg h) ht.2).trans hh
  have hJ : Integrable (fun p : Domain n × ℝ => G (p.1 + p.2 • h))
      ((volume.restrict (Metric.ball a r)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous (fun p : Domain n × ℝ => G (p.1 + p.2 • h)) :=
      hGcont.comp (by fun_prop)
    exact (hc.continuousOn.integrableOn_compact
      ((isCompact_closedBall a r).prod isCompact_Icc)).mono_set
        (Set.prod_mono Metric.ball_subset_closedBall (Subset.refl _))
  have hslice (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ x in Metric.ball a r, G (x + t • h)) ≤ ∫ x in Metric.ball a R, G x := by
    let g : Domain n → ℝ := (Metric.ball a R).indicator G
    have hgi : Integrable g volume := hGI.integrable_indicator measurableSet_ball
    have hgn (x : Domain n) : 0 ≤ g x := by
      by_cases hx : x ∈ Metric.ball a R
      · change 0 ≤ (Metric.ball a R).indicator G x
        rw [indicator_of_mem hx G]
        exact hGn x
      · simp only [g, indicator_of_notMem hx, le_refl]
    have heq : (∫ x in Metric.ball a r, G (x + t • h)) =
        ∫ x in Metric.ball a r, g (x + t • h) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact (indicator_of_mem (add_mem_ball_of_norm_le_margin hx (hpath t ht)) G).symm
    calc
      _ = ∫ x in Metric.ball a r, g (x + t • h) := heq
      _ ≤ ∫ x, g (x + t • h) :=
        setIntegral_le_integral (hgi.comp_add_right _) (Filter.Eventually.of_forall fun x => hgn _)
      _ = ∫ x, g x := integral_add_right_eq_self g _
      _ = _ := integral_indicator measurableSet_ball
  have htotal : (∫ x in Metric.ball a r, ∫ t in Icc (0 : ℝ) 1, G (x + t • h)) ≤
      ∫ x in Metric.ball a R, G x := by
    calc
      _ = ∫ t in Icc (0 : ℝ) 1, ∫ x in Metric.ball a r, G (x + t • h) :=
        integral_integral_swap hJ
      _ ≤ ∫ _t in Icc (0 : ℝ) 1, ∫ x in Metric.ball a R, G x :=
        setIntegral_mono_on hJ.integral_prod_right (integrable_const _) measurableSet_Icc hslice
      _ = _ := by simp [integral_const, measureReal_def, Real.volume_Icc]
  have hpoint (x : Domain n) (hx : x ∈ Metric.ball a r) :
      ‖f (x + h) - f x‖ ^ 2 ≤ ‖h‖ ^ 2 * ∫ t in Icc (0 : ℝ) 1, G (x + t • h) := by
    have H := segment_energy_bound hf.contDiffOn (Metric.ball_subset_ball hrR.le hx)
      (add_mem_ball_of_norm_le_margin hx hh)
    have hseg (t : ℝ) : (1 - t) • x + t • (x + h) = x + t • h := by
      simp only [sub_smul, one_smul, smul_add]
      abel
    rw [show (x + h) - x = h by abel, norm_sub_rev] at H
    simpa only [hseg, intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc] using H
  have hdiffI : IntegrableOn (fun x => ‖f (x + h) - f x‖ ^ 2) (Metric.ball a r) volume :=
    (((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous).norm.pow 2
      |>.continuousOn.integrableOn_compact (isCompact_closedBall a r)).mono_set
        Metric.ball_subset_closedBall
  calc
    _ ≤ ∫ x in Metric.ball a r, ‖h‖ ^ 2 * ∫ t in Icc (0 : ℝ) 1, G (x + t • h) :=
      setIntegral_mono_on hdiffI (hJ.integral_prod_left.const_mul _) measurableSet_ball hpoint
    _ = ‖h‖ ^ 2 * ∫ x in Metric.ball a r, ∫ t in Icc (0 : ℝ) 1, G (x + t • h) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (sq_nonneg _)

end StationaryHarmonicMaps.Analysis

end
