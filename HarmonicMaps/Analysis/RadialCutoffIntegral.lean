module

public import HarmonicMaps.Analysis.RadialCutoffProfile
public import HarmonicMaps.Analysis.BallPolarIntegralNormalization
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Convergence of shrinking radial cutoff integrals

The integral limit uses dominated convergence with an actual L1 density.
The only exceptional sphere has zero volume in positive dimension.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace HarmonicMaps

/-- The literal cutoff tends to the open-ball indicator away from the boundary. -/
theorem tendsto_radialCutoff_mul_indicator {n : ℕ} (t : PositiveRadius)
    (a x : Domain n) (hx : ‖x - a‖ ≠ t.val) (c : ℝ) :
    Tendsto (fun δ : ℝ => (1 - Real.smoothTransition ((‖x - a‖ - t.val) / δ)) * c)
      (𝓝[>] (0 : ℝ)) (𝓝 ((Metric.ball a t.val).indicator (fun _ => c) x)) := by
  by_cases hxt : ‖x - a‖ < t.val
  · rw [indicator_of_mem (show x ∈ Metric.ball a t.val by simpa only [Metric.mem_ball,
      dist_eq_norm_sub] using hxt)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxt.le) hδ.le), sub_zero, one_mul]
  · have htx : t.val < ‖x - a‖ := lt_of_le_of_ne (le_of_not_gt hxt) (Ne.symm hx)
    rw [indicator_of_notMem (show x ∉ Metric.ball a t.val by simpa only [Metric.mem_ball,
      dist_eq_norm_sub] using hxt)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < ‖x - a‖ - t.val from
        nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr htx)))] with δ hδ hsmall
    rw [Real.smoothTransition.one_of_one_le, sub_self, zero_mul]
    exact (le_div_iff₀ hδ).mpr (by simpa only [one_mul] using hsmall.le)

/-- Shrinking smooth radial cutoffs converge in the actual ball integral for
every L1 density. The endpoint sphere is removed by its proved null measure. -/
theorem tendsto_integral_radialCutoff {n : ℕ} (hn : 0 < n)
    (t : PositiveRadius) {a : Domain n} {R : ℝ} (htR : t.val < R)
    {f : Domain n → ℝ} (hf : IntegrableOn f (Metric.ball a R) volume) :
    Tendsto (fun δ : ℝ => ∫ x in Metric.ball a R,
      (1 - Real.smoothTransition ((‖x - a‖ - t.val) / δ)) * f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in Metric.ball a t.val, f x)) := by
  have hmeas : ∀ δ : ℝ, AEStronglyMeasurable (fun x : Domain n =>
      (1 - Real.smoothTransition ((‖x - a‖ - t.val) / δ)) * f x)
      (volume.restrict (Metric.ball a R)) := by
    intro δ
    exact (by fun_prop : Continuous (fun x : Domain n =>
      1 - Real.smoothTransition ((‖x - a‖ - t.val) / δ))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable
  have hbound : ∀ δ : ℝ, ∀ x : Domain n,
      ‖(1 - Real.smoothTransition ((‖x - a‖ - t.val) / δ)) * f x‖ ≤ ‖f x‖ := by
    intro δ x
    rw [norm_mul, Real.norm_eq_abs]
    have h0 := Real.smoothTransition.nonneg ((‖x - a‖ - t.val) / δ)
    have h1 := Real.smoothTransition.le_one ((‖x - a‖ - t.val) / δ)
    rw [abs_of_nonneg (sub_nonneg.mpr h1)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [h0])
  have hae : ∀ᵐ x ∂volume.restrict (Metric.ball a R), ‖x - a‖ ≠ t.val := by
    have hnull := (measure_eq_zero_iff_ae_notMem.mp (volume_sphere_eq_zero hn a t.val))
    filter_upwards [ae_restrict_of_ae hnull] with x hx
    simpa only [Metric.mem_sphere, dist_eq_norm_sub] using hx
  have hlim := tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun δ => Filter.Eventually.of_forall (hbound δ))
    hf.norm (hae.mono fun x hx => tendsto_radialCutoff_mul_indicator t a x hx (f x))
  have hind : (fun x => (Metric.ball a t.val).indicator (fun _ => f x) x) =
      (Metric.ball a t.val).indicator f := by
    funext x
    by_cases hx : x ∈ Metric.ball a t.val <;> simp only [indicator, hx]
  rw [hind, setIntegral_indicator Metric.isOpen_ball.measurableSet,
    inter_eq_right.mpr (Metric.ball_subset_ball htR.le)] at hlim
  exact hlim

end HarmonicMaps
