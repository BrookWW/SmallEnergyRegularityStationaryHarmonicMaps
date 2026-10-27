module

public import HarmonicMaps.Analysis.RadialCutoffLebesguePoints

/-!
# Weighted cutoff limits on the full radius interval

Derivative support reduces the full radius integral to its shrinking
transition interval. Actual L1 membership supplies integrability and the
almost-everywhere limit with coefficient minus one.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace HarmonicMaps

/-- The derivative-weighted radius integrand is genuinely integrable. -/
theorem integrableOn_radialCutoff_derivative_mul (t δ : PositiveRadius)
    {w : ℝ → ℝ} {R : ℝ} (hw : IntegrableOn w (Ioo 0 R) volume) :
    IntegrableOn (fun r => deriv (radialCutoffProfile t δ) r * w r) (Ioo 0 R) volume := by
  have hc : Continuous (deriv (radialCutoffProfile t δ)) :=
    (radialCutoffProfile_contDiff t δ).continuous_deriv (by norm_num)
  exact IntegrableOn.continuousOn_mul_of_subset hc.continuousOn hw
    isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self

/-- Support identifies the full radius integral with its transition integral. -/
theorem integral_radialCutoff_derivative_eq_transition (t δ : PositiveRadius)
    (w : ℝ → ℝ) {R : ℝ} (hR : t.val + δ.val < R) :
    (∫ r in Ioo (0 : ℝ) R, deriv (radialCutoffProfile t δ) r * w r) =
      ∫ r in t.val..(t.val + δ.val), deriv (radialCutoffProfile t δ) r * w r := by
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right δ.property.le),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
  · intro r hr
    exact ⟨t.property.trans_le hr.1, hr.2.trans_lt hR⟩
  · intro r hr
    rw [radialCutoffProfile_deriv_eq_zero t δ hr.2, zero_mul]

/-- The full derivative-weighted integral tends to minus the density at
almost every radius; the Lebesgue-point premise is derived from L1. -/
theorem ae_tendsto_integral_radialCutoff_derivative {w : ℝ → ℝ} {R : ℝ}
    (hw : IntegrableOn w (Ioo 0 R) volume) :
    ∀ᵐ t : ℝ, ∀ ht : t ∈ Ioo 0 R,
      ∀ {ι : Type*} {l : Filter ι} (δ : ι → PositiveRadius),
      Tendsto (fun i => (δ i).val) l (𝓝 (0 : ℝ)) →
      Tendsto (fun i => ∫ r in Ioo (0 : ℝ) R,
        deriv (radialCutoffProfile ⟨t, ht.1⟩ (δ i)) r * w r) l (𝓝 (-w t)) := by
  filter_upwards [ae_tendsto_radialCutoff_derivative hw] with t ht
  intro htR ι l δ hδ
  apply (ht htR δ hδ).congr'
  have hsmall : ∀ᶠ i in l, (δ i).val < R - t := hδ (Iio_mem_nhds (sub_pos.mpr htR.2))
  filter_upwards [hsmall] with i hi
  exact (integral_radialCutoff_derivative_eq_transition ⟨t, htR.1⟩ (δ i) w
    (by dsimp only; linarith only [hi])).symm

/-- The radius factor in radial stationarity yields the exact limit -t*g(t). -/
theorem ae_tendsto_integral_radius_mul_radialCutoff_derivative {g : ℝ → ℝ} {R : ℝ}
    (hg : IntegrableOn g (Ioo 0 R) volume) :
    ∀ᵐ t : ℝ, ∀ ht : t ∈ Ioo 0 R,
      ∀ {ι : Type*} {l : Filter ι} (δ : ι → PositiveRadius),
      Tendsto (fun i => (δ i).val) l (𝓝 (0 : ℝ)) →
      Tendsto (fun i => ∫ r in Ioo (0 : ℝ) R,
        r * deriv (radialCutoffProfile ⟨t, ht.1⟩ (δ i)) r * g r) l (𝓝 (-t * g t)) := by
  have hw : IntegrableOn (fun r => r * g r) (Ioo 0 R) volume :=
    IntegrableOn.continuousOn_mul_of_subset continuous_id.continuousOn hg
      isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self
  filter_upwards [ae_tendsto_integral_radialCutoff_derivative hw] with t ht
  intro htR ι l δ hδ
  simpa only [mul_left_comm, ← mul_assoc, neg_mul] using ht htR δ hδ

end HarmonicMaps
