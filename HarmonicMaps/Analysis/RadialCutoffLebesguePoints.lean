module

public import HarmonicMaps.Analysis.RadialCutoffLebesgue
import Mathlib.MeasureTheory.Covering.OneDim

/-!
# Almost-everywhere one-sided Lebesgue points

Actual L1 membership supplies the mean-oscillation hypothesis used by the
shrinking cutoff derivative limit. No pointwise limit is assumed here.
-/

public section

open MeasureTheory Set Filter IsUnifLocDoublingMeasure
open scoped Topology

namespace HarmonicMaps

/-- Global L1 densities have right-sided Lebesgue points almost everywhere. -/
theorem ae_tendsto_right_mean_oscillation {w : ℝ → ℝ} (hw : Integrable w volume) :
    ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => ε⁻¹ *
      ∫ r in t..(t + ε), |w r - w t|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [(vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average_norm_sub
    hw.locallyIntegrable] with t ht
  have hshift : Tendsto (fun ε : ℝ => t + ε) (𝓝[>] (0 : ℝ)) (𝓝[>] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [add_zero] using
        (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun ε : ℝ => t + ε) (𝓝[>] (0 : ℝ)) (𝓝 (t + 0)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact lt_add_of_pos_right t hε
  have hav := (ht.comp (Real.tendsto_Icc_vitaliFamily_right t)).comp hshift
  apply hav.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_def]
  rw [setAverage_eq, Real.volume_real_Icc_of_le (le_add_of_nonneg_right hε.le),
    add_sub_cancel_left, smul_eq_mul, intervalIntegral.integral_of_le
      (le_add_of_nonneg_right hε.le), integral_Icc_eq_integral_Ioc]
  simp only [Real.norm_eq_abs]

/-- L1 membership on the actual radius interval supplies interior right-sided
Lebesgue points, without requiring any off-interval regularity. -/
theorem ae_tendsto_right_mean_oscillation_on {w : ℝ → ℝ} {R : ℝ}
    (hw : IntegrableOn w (Ioo 0 R) volume) :
    ∀ᵐ t : ℝ, t ∈ Ioo 0 R → Tendsto (fun ε : ℝ => ε⁻¹ *
      ∫ r in t..(t + ε), |w r - w t|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hg : Integrable ((Ioo 0 R).indicator w) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hw
  filter_upwards [ae_tendsto_right_mean_oscillation hg] with t ht
  intro htR
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < R - t from
      nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr htR.2)))] with ε hε hsmall
  apply congrArg (fun z : ℝ => ε⁻¹ * z)
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hε.le),
    intervalIntegral.integral_of_le (le_add_of_nonneg_right hε.le)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  dsimp only
  have hrR : r ∈ Ioo (0 : ℝ) R := ⟨htR.1.trans hr.1, by linarith only [hr.2, hsmall]⟩
  rw [indicator_of_mem hrR, indicator_of_mem htR]

/-- The signed cutoff derivative limit follows for almost every radius from
the actual L1 density, for every family of positive widths tending to zero. -/
theorem ae_tendsto_radialCutoff_derivative {w : ℝ → ℝ} {R : ℝ}
    (hw : IntegrableOn w (Ioo 0 R) volume) :
    ∀ᵐ t : ℝ, ∀ ht : t ∈ Ioo 0 R,
      ∀ {ι : Type*} {l : Filter ι} (δ : ι → PositiveRadius),
      Tendsto (fun i => (δ i).val) l (𝓝 (0 : ℝ)) →
      Tendsto (fun i => ∫ r in t..(t + (δ i).val),
        deriv (radialCutoffProfile ⟨t, ht.1⟩ (δ i)) r * w r) l (𝓝 (-w t)) := by
  filter_upwards [ae_tendsto_right_mean_oscillation_on hw] with t ht
  intro htR ι l δ hδ
  exact tendsto_radialCutoff_derivative_of_lebesguePoint ⟨t, htR.1⟩ δ hδ htR.2 hw (ht htR)

end HarmonicMaps
