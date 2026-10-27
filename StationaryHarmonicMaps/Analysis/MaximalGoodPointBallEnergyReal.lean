module

public import StationaryHarmonicMaps.Analysis.MaximalGoodPointBallEnergy

/-!
# Actual real ball energy at a nearby maximal good point

The original nonnegative integrable density supplies its actual ordinary
ball integral. The proved extended estimate transfers through genuine
finite ball volume and actual integral/lintegral equality. Dividing by
the positive original ball volume yields the same real average bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A nonnegative original integrable real density gives both ordinary query-ball energy and its genuine average from the supplied nearby maximal good point. -/
theorem ball_integral_average_le_of_dyadic_maximal_goodpoint {n : ℕ}
    (d : Domain n → ℝ) (hd : Integrable d volume) (hd0 : ∀ᵐ z ∂volume,0≤d z)
    (a y : Domain n) (r R : ℝ) (hr : 0<r) (hy : dist y a≤20*r) (hR : r≤R)
    (L : ℝ) (hL : 0≤L)
    (hGood : dyadicBallMaximal (fun z=>ENNReal.ofReal (d z)) y≤ENNReal.ofReal L) :
    (∫ z in Metric.ball a R,d z)≤(64 : ℝ)^n*L*volume.real (Metric.ball a R) ∧
      (volume.real (Metric.ball a R))⁻¹*(∫ z in Metric.ball a R,d z)≤(64 : ℝ)^n*L := by
  have hR0 : 0<R := hr.trans_le hR
  have hC : 0≤(64 : ℝ)^n := pow_nonneg (by norm_num) n
  have hVolume : 0<volume.real (Metric.ball a R) := HolderToCK.ball_volume_real_pos a hR0
  have H := (ball_lintegral_le_of_dyadic_maximal_goodpoint (fun z=>ENNReal.ofReal (d z))
    a y r R hr hy hR (ENNReal.ofReal L) hGood).1
  rw [← ofReal_integral_eq_lintegral_ofReal hd.integrableOn (ae_restrict_of_ae hd0),
    ← ENNReal.ofReal_toReal (measure_ball_ne_top : volume (Metric.ball a R)≠∞),
    ← ENNReal.ofReal_mul hC,← ENNReal.ofReal_mul (mul_nonneg hC hL)] at H
  have hEnergy : (∫ z in Metric.ball a R,d z)≤(64 : ℝ)^n*L*volume.real (Metric.ball a R) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hC hL) hVolume.le)).mp H
  refine ⟨hEnergy,?_⟩
  calc
    _ ≤ (volume.real (Metric.ball a R))⁻¹*((64 : ℝ)^n*L*volume.real (Metric.ball a R)) :=
      mul_le_mul_of_nonneg_left hEnergy (inv_nonneg.mpr hVolume.le)
    _ = ((64 : ℝ)^n*L)*((volume.real (Metric.ball a R))⁻¹*volume.real (Metric.ball a R)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hVolume.ne',mul_one]

end StationaryHarmonicMaps.Analysis

end
