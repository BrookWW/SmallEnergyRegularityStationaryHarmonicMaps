module

public import HarmonicMaps.Analysis.RadialCutoffDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Derivative-weighted radial cutoff limits

A genuine one-sided Lebesgue point controls the error through its mean
absolute oscillation. The cutoff derivative has signed mass minus one.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace HarmonicMaps

/-- A universal bound reduces the derivative-weighted cutoff error to the
one-sided mean absolute oscillation of the actual density. -/
theorem radialCutoffProfile_derivative_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t δ : PositiveRadius) (w : ℝ → ℝ),
      IntervalIntegrable w volume t.val (t.val + δ.val) →
      |(∫ r in t.val..(t.val + δ.val), deriv (radialCutoffProfile t δ) r * w r) + w t.val| ≤
        C * (δ.val⁻¹ * ∫ r in t.val..(t.val + δ.val), |w r - w t.val|) := by
  obtain ⟨C, hC, hbound⟩ := radialCutoffProfile_deriv_bound
  refine ⟨C, hC, fun t δ w hw => ?_⟩
  have hc : Continuous (deriv (radialCutoffProfile t δ)) :=
    (radialCutoffProfile_contDiff t δ).continuous_deriv (by norm_num)
  have hk := hc.intervalIntegrable (μ := volume) t.val (t.val + δ.val)
  have hdiff : IntervalIntegrable (fun r => w r - w t.val) volume t.val (t.val + δ.val) :=
    hw.sub intervalIntegrable_const
  have heq : (∫ r in t.val..(t.val + δ.val),
      deriv (radialCutoffProfile t δ) r * (w r - w t.val)) =
      (∫ r in t.val..(t.val + δ.val), deriv (radialCutoffProfile t δ) r * w r) + w t.val := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hw.continuousOn_mul hc.continuousOn)
      (hk.mul_const (w t.val)), intervalIntegral.integral_mul_const,
      radialCutoffProfile_integral_deriv]
    ring
  rw [← heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ r in t.val..(t.val + δ.val), (C / δ.val) * |w r - w t.val| := by
      apply intervalIntegral.norm_integral_le_of_norm_le (le_add_of_nonneg_right δ.property.le)
      · exact Filter.Eventually.of_forall fun r _ => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hbound t δ r) (abs_nonneg _)
      · exact hdiff.abs.const_mul (C / δ.val)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- At a one-sided Lebesgue point, every positive shrinking width gives the
correct signed derivative-weighted limit. The premise is mean oscillation,
not the weighted cutoff limit. -/
theorem tendsto_radialCutoff_derivative_of_lebesguePoint
    {ι : Type*} {l : Filter ι} (t : PositiveRadius) (δ : ι → PositiveRadius)
    (hδ : Tendsto (fun i => (δ i).val) l (𝓝 (0 : ℝ)))
    {w : ℝ → ℝ} {R : ℝ} (htR : t.val < R)
    (hw : IntegrableOn w (Ioo 0 R) volume)
    (hlebesgue : Tendsto (fun ε : ℝ => ε⁻¹ *
      ∫ r in t.val..(t.val + ε), |w r - w t.val|) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun i => ∫ r in t.val..(t.val + (δ i).val),
      deriv (radialCutoffProfile t (δ i)) r * w r) l (𝓝 (-w t.val)) := by
  obtain ⟨C, hC, hbound⟩ := radialCutoffProfile_derivative_error_bound
  have hδright : Tendsto (fun i => (δ i).val) l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ, Filter.Eventually.of_forall fun i => (δ i).property⟩
  have hsmall : ∀ᶠ i in l, (δ i).val < R - t.val :=
    hδ (Iio_mem_nhds (sub_pos.mpr htR))
  have herr := (hlebesgue.comp hδright).const_mul C
  have habs : Tendsto (fun i =>
      |(∫ r in t.val..(t.val + (δ i).val), deriv (radialCutoffProfile t (δ i)) r * w r) + w t.val|)
      l (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) _
      (by simpa only [mul_zero] using herr)
    filter_upwards [hsmall] with i hi
    apply hbound
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (le_add_of_nonneg_right (δ i).property.le)).mpr
    exact hw.mono_set (fun r hr => ⟨t.property.trans hr.1, by linarith only [hr.2, hi]⟩)
  have hsum : Tendsto (fun i =>
      (∫ r in t.val..(t.val + (δ i).val), deriv (radialCutoffProfile t (δ i)) r * w r) + w t.val)
      l (𝓝 0) := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  simpa only [add_sub_cancel_right, zero_sub] using hsum.sub_const (w t.val)

end HarmonicMaps
