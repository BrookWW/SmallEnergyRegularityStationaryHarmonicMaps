module

public import StationaryHarmonicMaps.Analysis.SegmentL1
public import HarmonicMaps.Analysis.BallAffineEnergy
public import Mathlib.MeasureTheory.Integral.Average

/-! # The L1 Poincare estimate on a Euclidean ball

The mean oscillation is bounded by the double integral of endpoint
differences. Segment integration and the two affine changes of variables
give a bound by the L1 integral of the actual derivative columns.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped BigOperators ContDiff

namespace StationaryHarmonicMaps

section FiniteMeasure

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure X} [IsFiniteMeasure μ]

/-- The pointwise difference from a mean is bounded by mean endpoint differences. -/
theorem norm_sub_average_le_integral_norm_sub (f : X → E) (hf : Integrable f μ)
    (hμ : μ ≠ 0) (x : X) :
    ‖f x - (⨍ y, f y ∂μ)‖ ≤ (μ.real univ)⁻¹ * ∫ y, ‖f x - f y‖ ∂μ := by
  letI : NeZero μ := ⟨hμ⟩
  have hconstant : (μ.real univ)⁻¹ • (∫ _y, f x ∂μ) = f x := by
    rw [← average_eq, average_const]
  have hrepr : (μ.real univ)⁻¹ • (∫ y, f x - f y ∂μ) =
      f x - (⨍ y, f y ∂μ) := by
    rw [integral_sub (integrable_const _) hf, smul_sub, hconstant, ← average_eq]
  have hinv : 0 ≤ (μ.real univ)⁻¹ :=
    inv_nonneg.mpr (show 0 ≤ μ.real univ from ENNReal.toReal_nonneg)
  rw [← hrepr, norm_smul, Real.norm_of_nonneg hinv]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- Finite-measure L1 mean oscillation is controlled by the literal double integral. -/
theorem integral_norm_sub_average_le_double_integral (f : X → E)
    (hf : Integrable f μ) (hμ : μ ≠ 0) :
    (∫ x, ‖f x - (⨍ y, f y ∂μ)‖ ∂μ) ≤
      (μ.real univ)⁻¹ * ∫ x, ∫ y, ‖f x - f y‖ ∂μ ∂μ := by
  have hpair : Integrable (fun p : X × X => ‖f p.1 - f p.2‖) (μ.prod μ) :=
    ((hf.comp_fst μ).sub (hf.comp_snd μ)).norm
  have hcenter : Integrable (fun x => ‖f x - (⨍ y, f y ∂μ)‖) μ :=
    (hf.sub (integrable_const _)).norm
  rw [← integral_const_mul]
  exact integral_mono hcenter (hpair.integral_prod_left.const_mul _)
    (fun x => norm_sub_average_le_integral_norm_sub f hf hμ x)

end FiniteMeasure

/-- A C1 map with L1 derivative columns satisfies the ball L1 Poincare bound. -/
theorem smooth_poincare_l1_ball {n q : ℕ} (a : Domain n) {r : ℝ} (hr : 0 < r)
    {f : Domain n → Ambient q}
    (hsmooth : ContDiffOn ℝ 1 f (Metric.ball a r))
    (hf : IntegrableOn f (Metric.ball a r))
    (hDf : ∀ i : Fin n, IntegrableOn
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) (Metric.ball a r)) :
    (∫ x in Metric.ball a r, ‖f x - (⨍ y in Metric.ball a r, f y)‖) ≤
      (2 : ℝ) ^ (n + 1) * r * ∫ x in Metric.ball a r,
        ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ := by
  classical
  let B : Set (Domain n) := Metric.ball a r
  let μ : Measure (Domain n) := volume.restrict B
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let G : Domain n → ℝ := fun x =>
    ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖
  let g : Domain n → ℝ := B.indicator G
  have hGcont : ContinuousOn G B :=
    continuousOn_finsetSum Finset.univ (fun i _ =>
      ((hsmooth.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).clm_apply
        continuousOn_const).norm)
  have hgm : Measurable g :=
    hGcont.measurable_piecewise continuousOn_const measurableSet_ball
  have hGi : Integrable G μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hDf i).norm)
  have hgi : Integrable g μ := hGi.congr (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (indicator_of_mem hx G).symm)
  have hgn : ∀ x ∈ B, 0 ≤ g x := by
    intro x hx
    rw [show g x = G x from indicator_of_mem hx G]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hAffine := ball_affine_integrable_and_integral_le hgm hgn hgi
  have hSegmentInt := ball_affine_segmentIntegral_integrable hgm hgn hgi
  have hpair : Integrable (fun p : Domain n × Domain n => ‖f p.1 - f p.2‖)
      (μ.prod μ) := ((hf.comp_fst μ).sub (hf.comp_snd μ)).norm
  have hPairBound : (∫ p : Domain n × Domain n, ‖f p.1 - f p.2‖ ∂μ.prod μ) ≤
      2 * r * ∫ p : Domain n × Domain n,
        (∫ t in Icc (0 : ℝ) 1, g ((1 - t) • p.1 + t • p.2)) ∂μ.prod μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hpair (hSegmentInt.const_mul _)
    change ∀ᵐ p ∂(volume.restrict B).prod (volume.restrict B), _
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)] with p hp
    have hEq := ball_affine_segmentIntegral_indicator hp.1 hp.2 G
    rw [show g = B.indicator G from rfl, hEq]
    exact ball_segment_norm_le_integral_column_norm hsmooth hp.1 hp.2 hr
  have hDouble : (∫ x in B, ∫ y in B, ‖f x - f y‖) ≤
      2 * r * ((2 : ℝ) ^ n * volume.real B * ∫ z in B, G z) := by
    rw [integral_prod _ hpair, integral_prod _ hSegmentInt] at hPairBound
    have hEstimate := mul_le_mul_of_nonneg_left hAffine.2
      (by positivity : 0 ≤ 2 * r)
    rw [ball_setIntegral_indicator a r G] at hEstimate
    exact hPairBound.trans hEstimate
  have hmass : 0 < volume.real B :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume a hr).ne' measure_ball_ne_top
  have hμ : μ ≠ 0 := by
    intro hz
    have heval := congrArg (fun ν : Measure (Domain n) => ν univ) hz
    have hpos := (Metric.measure_ball_pos volume a hr).ne'
    apply hpos
    simpa only [μ, B, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using heval
  have hmean := integral_norm_sub_average_le_double_integral f hf hμ
  change (∫ x in B, ‖f x - (⨍ y in B, f y)‖) ≤ _ at hmean
  have hmean' : (∫ x in B, ‖f x - (⨍ y in B, f y)‖) ≤
      (volume.real B)⁻¹ * ∫ x in B, ∫ y in B, ‖f x - f y‖ := by
    simpa only [μ, Measure.restrict_apply_univ, measureReal_def] using hmean
  calc
    _ ≤ (volume.real B)⁻¹ * (2 * r *
        ((2 : ℝ) ^ n * volume.real B * ∫ z in B, G z)) :=
      hmean'.trans (mul_le_mul_of_nonneg_left hDouble (inv_nonneg.mpr hmass.le))
    _ = (2 : ℝ) ^ (n + 1) * r * ∫ z in B, G z := by
      rw [pow_succ]
      field_simp

end StationaryHarmonicMaps

end
