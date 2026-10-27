module

public import HarmonicMaps.Analysis.BallAverageDifferentiation

/-!
# Differentiation of actual means on arbitrary strict interior balls

Outer-ball integrability suffices: the outer-ball indicator is globally
integrable and agrees with the original map on every sufficiently small
ball centered in the strict interior ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual open-ball means differentiate an outer-ball L1 map on every strict inner ball. -/
theorem integrableOn_ae_tendsto_ballAverage_interior {n q : ℕ}
    (f : Domain n → Ambient q) (a : Domain n) {R s : ℝ}
    (_hR : 0 < R) (hs : s < R)
    (hf : IntegrableOn f (Metric.ball a R) volume) :
    ∀ᵐ x ∂volume.restrict (Metric.ball a s),
      Tendsto (fun r : ℝ => (volume (Metric.ball x r)).toReal⁻¹ •
        (∫ y in Metric.ball x r, f y)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  classical
  let B : Set (Domain n) := Metric.ball a R
  let g : Domain n → Ambient q := B.indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_ball
  have hnative := IsUnifLocDoublingMeasure.ae_tendsto_average volume hg.locallyIntegrable 1
  filter_upwards [hnative.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_ball] with x hx hxin
  have hxB : x ∈ B := Metric.ball_subset_ball hs.le hxin
  have hcenter : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), x ∈ Metric.closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [mem_closedBall, dist_self, one_mul] using hr.le
  have hlimit := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hcenter
  have heq : (fun r : ℝ => (volume (Metric.ball x r)).toReal⁻¹ •
      (∫ y in Metric.ball x r, f y)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => ⨍ y in Metric.closedBall x r, g y) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr hs))] with r hr hrsmall
    change r < R - s at hrsmall
    have hsub : Metric.ball x r ⊆ B := by
      intro y hy
      have h := dist_triangle y x a
      have hyx : dist y x < r := hy
      have hxa : dist x a < s := hxin
      change dist y a < R
      linarith
    change (volume.real (Metric.ball x r))⁻¹ • _ = _
    rw [← setAverage_eq]
    rw [← setAverage_congr (HarmonicMaps.ball_ae_eq_closedBall x hr)]
    apply setAverage_congr_fun measurableSet_ball
    exact Filter.Eventually.of_forall fun y hy => (indicator_of_mem (hsub hy) f).symm
  have hgx : g x = f x := indicator_of_mem hxB f
  rw [hgx] at hlimit
  exact hlimit.congr' heq.symm

end StationaryHarmonicMaps.Analysis

end
