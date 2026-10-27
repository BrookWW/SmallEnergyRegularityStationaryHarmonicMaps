module

public import StationaryHarmonicMaps.Analysis.GrandLevelIntegralLimits

/-!
# Actual two-ended L1 limits for one supplied integer good family

The original cap and tail bounds of the same family consume the proved
original grand-integral limits at all negative and positive integer
scales. The original functions are integrable before their norm
integrals are converted from extended values to real values.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem real_L1_limit_of_extended_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : ℕ → X → ℝ) (hI : ∀ k,Integrable (v k) μ)
    (hT : Tendsto (fun k=>∫⁻ x,ENNReal.ofReal |v k x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k=>∫ x,|v k x| ∂μ) atTop (𝓝 (0 : ℝ)) := by
  have hReal (k : ℕ) : (∫⁻ x,ENNReal.ofReal |v k x| ∂μ).toReal=(∫ x,|v k x| ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hI k).abs (Eventually.of_forall fun _=>abs_nonneg _)]
    exact ENNReal.toReal_ofReal (integral_nonneg fun _=>abs_nonneg _)
  have H := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
  change Tendsto (fun k=>(∫⁻ x,ENNReal.ofReal |v k x| ∂μ).toReal) atTop (𝓝 (0 : ℝ)) at H
  simpa only [hReal] using H

/-- Actual integrability and original dyadic cap/tail estimates give the same integer family's genuine negative-end and positive-end strong L1 limits. -/
theorem dyadic_good_family_strong_L1_limits {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (J : X → ℝ≥0∞) (hJ : Measurable J) (hFinite : (∫⁻ x,J x ∂μ)≠∞)
    (f : X → ℝ) (hf : Integrable f μ) (G : ℤ → X → ℝ) (hG : ∀ j,Integrable (G j) μ)
    (A : ℝ)
    (hCap : ∀ j,∀ᵐ x ∂μ,ENNReal.ofReal |G j x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal ((2 : ℝ)^j)))
    (hError : ∀ j,∀ᵐ x ∂μ,ENNReal.ofReal |f x-G j x|≤ENNReal.ofReal (2*A)*
      ({y | ENNReal.ofReal ((2 : ℝ)^j)<J y}.indicator J x)) :
    Tendsto (fun N : ℕ=>∫ x,|G (-(N : ℤ)) x| ∂μ) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun N : ℕ=>∫ x,|f x-G ((N : ℤ)+1) x| ∂μ) atTop (𝓝 (0 : ℝ)) := by
  classical
  have hLowLevels : Tendsto (fun N : ℕ=>(2 : ℝ)^(-(N : ℤ))) atTop (𝓝 (0 : ℝ)) := by
    have hEq : (fun N : ℕ=>(2 : ℝ)^(-(N : ℤ)))=(fun N=>(1/2 : ℝ)^N) := by
      funext N
      rw [zpow_neg,zpow_natCast,← inv_pow]
      norm_num
    rw [hEq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hHighLevels : Tendsto (fun N : ℕ=>(2 : ℝ)^((N : ℤ)+1)) atTop atTop := by
    have hEq : (fun N : ℕ=>(2 : ℝ)^((N : ℤ)+1))=(fun N=>(2 : ℝ)^N*2) := by
      funext N
      rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_natCast,zpow_one]
    rw [hEq]
    exact Filter.Tendsto.atTop_mul_const (by norm_num) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2))
  constructor
  · apply real_L1_limit_of_extended_zero μ (fun N : ℕ=>G (-(N : ℤ))) (fun N=>hG (-(N : ℤ)))
    have hLevel := tendsto_lintegral_min_ofReal_zero μ J hJ hFinite _ hLowLevels
    have hUpper : Tendsto (fun N : ℕ=>ENNReal.ofReal A*∫⁻ x,min (J x) (ENNReal.ofReal ((2 : ℝ)^(-(N : ℤ)))) ∂μ)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hLevel (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _=>zero_le)
    intro N
    exact (lintegral_mono_ae (hCap (-(N : ℤ)))).trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
  · apply real_L1_limit_of_extended_zero μ (fun N : ℕ=>fun x=>f x-G ((N : ℤ)+1) x) (fun N=>hf.sub (hG ((N : ℤ)+1)))
    have hLevel := tendsto_lintegral_upper_level_tail_zero μ J hJ hFinite _ hHighLevels
    have hUpper : Tendsto (fun N : ℕ=>ENNReal.ofReal (2*A)*∫⁻ x,
        if ENNReal.ofReal ((2 : ℝ)^((N : ℤ)+1))<J x then J x else 0 ∂μ) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hLevel (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _=>zero_le)
    intro N
    exact (lintegral_mono_ae (hError ((N : ℤ)+1))).trans_eq (by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [indicator_apply,mem_setOf_eq])

end StationaryHarmonicMaps.Analysis

end
