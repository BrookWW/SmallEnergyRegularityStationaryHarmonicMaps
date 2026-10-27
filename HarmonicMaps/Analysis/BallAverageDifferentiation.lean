module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Average

/-! # Differentiation of literal Euclidean open-ball means

Compact localization supplies the global integrable input of the native
closed-ball differentiation theorem. Null spheres identify its means with
the original open-ball Bochner integrals, including in dimension zero.
-/

public section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace HarmonicMaps

/-- Open and closed Euclidean balls agree almost everywhere at positive radius. -/
theorem ball_ae_eq_closedBall {n : ℕ} (x : Domain n) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  rw [ae_eq_set]
  constructor
  · rw [sdiff_eq_empty.mpr Metric.ball_subset_closedBall, measure_empty]
  · rw [Metric.closedBall_sdiff_ball]
    exact MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume x hr.ne'

/-- Local Euclidean integrability gives differentiation of the actual open-ball means. -/
theorem locallyIntegrableOn_ae_tendsto_ballAverage {n q : ℕ}
    (f : Domain n → Ambient q)
    (hf : LocallyIntegrableOn f (Metric.ball (0 : Domain n) 1) volume) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (1 / 2)),
      Tendsto (fun r : ℝ => (volume (Metric.ball x r)).toReal⁻¹ •
        (∫ y in Metric.ball x r, f y)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  classical
  let K : Set (Domain n) := Metric.closedBall 0 (3 / 4)
  let g : Domain n → Ambient q := K.indicator f
  have hKsub : K ⊆ Metric.ball (0 : Domain n) 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hfi : IntegrableOn f K volume :=
    hf.integrableOn_compact_subset hKsub (isCompact_closedBall _ _)
  have hgi : Integrable g volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr hfi
  have hn := IsUnifLocDoublingMeasure.ae_tendsto_average volume hgi.locallyIntegrable 1
  filter_upwards [hn.filter_mono (ae_mono (Measure.restrict_le_self)),
    ae_restrict_mem measurableSet_ball] with x hx hxin
  have hxK : x ∈ K := by
    change dist x 0 ≤ (3 / 4 : ℝ)
    have hxhalf : dist x 0 < (1 / 2 : ℝ) := hxin
    linarith only [hxhalf]
  have hcenter : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), x ∈ Metric.closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [mem_Ioi] at hr
    simpa only [mem_closedBall, dist_self, one_mul] using hr.le
  have hnative := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hcenter
  have heq : (fun r : ℝ => (volume (Metric.ball x r)).toReal⁻¹ •
      (∫ y in Metric.ball x r, f y)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => ⨍ y in Metric.closedBall x r, g y) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with r hr hrsmall
    have hrpos : 0 < r := hr
    change r < 1 / 4 at hrsmall
    have hballK : Metric.ball x r ⊆ K := by
      intro y hy
      have hxy : dist y x < r := hy
      have hxhalf : dist x 0 < (1 / 2 : ℝ) := hxin
      change dist y 0 ≤ (3 / 4 : ℝ)
      exact le_of_lt (lt_of_le_of_lt (dist_triangle y x 0) (by linarith only [hxy, hxhalf, hrsmall]))
    change (volume.real (Metric.ball x r))⁻¹ • _ = _
    rw [← setAverage_eq]
    rw [← setAverage_congr (ball_ae_eq_closedBall x hrpos)]
    apply setAverage_congr_fun measurableSet_ball
    exact Filter.Eventually.of_forall fun y hy => (indicator_of_mem (hballK hy) f).symm
  have hgx : g x = f x := indicator_of_mem hxK f
  rw [hgx] at hnative
  exact hnative.congr' heq.symm

end HarmonicMaps
