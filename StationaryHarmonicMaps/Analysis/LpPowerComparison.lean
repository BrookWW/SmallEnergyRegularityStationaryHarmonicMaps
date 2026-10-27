module

public import StationaryHarmonicMaps.Analysis.LpL1Bound

/-! # Forward finite-measure comparison of actual norm-power integrals -/

public section

open MeasureTheory

namespace StationaryHarmonicMaps.Analysis

/-- A larger real Lp exponent controls every smaller positive power with its actual measure factor. -/
theorem integral_norm_rpow_le_of_exponent_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ]
    (f : X → E) {r p : ℝ} (hr : 0 < r) (hrp : r ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫ x, ‖f x‖ ^ r ∂μ) ≤ (μ.real Set.univ) ^ (1 - r / p) *
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (r / p) := by
  have hp : 0 < p := hr.trans_le hrp
  have hroot := integral_norm_rpow_root_le_of_exponent_le f hr hrp hf
  have hIr : 0 ≤ ∫ x, ‖f x‖ ^ r ∂μ :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) r
  have hIp : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) p
  have hμ : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
  have H := Real.rpow_le_rpow (Real.rpow_nonneg hIr _) hroot hr.le
  simp only [one_div] at H
  rw [Real.rpow_inv_rpow hIr hr.ne',
    Real.mul_rpow (Real.rpow_nonneg hIp _) (Real.rpow_nonneg hμ _),
    ← Real.rpow_mul hIp, ← Real.rpow_mul hμ] at H
  have hpower : p⁻¹ * r = r / p := by ring
  have hmass : (r⁻¹ - p⁻¹) * r = 1 - r / p := by
    field_simp [hr.ne', hp.ne']
  rw [hpower, hmass] at H
  simpa only [mul_comm] using H

end StationaryHarmonicMaps.Analysis

end
