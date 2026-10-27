module

public import HarmonicMaps.Analysis.RadialCutoffProfile
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Support and mass of radial cutoff derivatives

The derivative is supported in the shrinking transition interval and has
integral minus one, with the sign used in radial stationarity.
-/

public section

open MeasureTheory Set
open scoped Topology ContDiff

namespace HarmonicMaps

/-- The derivative vanishes outside the closed transition interval. -/
theorem radialCutoffProfile_deriv_eq_zero (t δ : PositiveRadius) {r : ℝ}
    (hr : r ∉ Icc t.val (t.val + δ.val)) : deriv (radialCutoffProfile t δ) r = 0 := by
  rw [radialCutoffProfile_deriv, smoothTransition_deriv_eq_zero, neg_zero, zero_div]
  intro harg
  apply hr
  constructor
  · apply sub_nonneg.mp
    simpa only [zero_mul] using (le_div_iff₀ δ.property).mp harg.1
  · have hh := (div_le_one δ.property).mp harg.2
    linarith only [hh]

/-- Closed support of the actual derivative lies in its shrinking interval. -/
theorem radialCutoffProfile_deriv_tsupport_subset (t δ : PositiveRadius) :
    tsupport (deriv (radialCutoffProfile t δ)) ⊆ Icc t.val (t.val + δ.val) := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  by_contra h
  exact hr (radialCutoffProfile_deriv_eq_zero t δ h)

/-- The signed derivative mass of the cutoff is exactly minus one. -/
theorem radialCutoffProfile_integral_deriv (t δ : PositiveRadius) :
    (∫ r in t.val..(t.val + δ.val), deriv (radialCutoffProfile t δ) r) = -1 := by
  have hd := (radialCutoffProfile_contDiff t δ).differentiable (by norm_num)
  have hi : IntervalIntegrable (deriv (radialCutoffProfile t δ)) volume t.val (t.val + δ.val) :=
    ((radialCutoffProfile_contDiff t δ).continuous_deriv (by norm_num)).intervalIntegrable _ _
  rw [intervalIntegral.integral_deriv_eq_sub (fun _ _ => hd _) hi,
    radialCutoffProfile_eq_zero t δ le_rfl, radialCutoffProfile_eq_one t δ le_rfl]
  norm_num

/-- The derivative has the sign of a decreasing cutoff. -/
theorem radialCutoffProfile_deriv_nonpos (t δ : PositiveRadius) (r : ℝ) :
    deriv (radialCutoffProfile t δ) r ≤ 0 := by
  rw [radialCutoffProfile_deriv]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Real.smoothTransition.monotone.deriv_nonneg)) δ.property.le

end HarmonicMaps
