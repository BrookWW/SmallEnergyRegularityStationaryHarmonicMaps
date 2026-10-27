module

public import StationaryHarmonicMaps.Analysis.SobolevLpOscillation

/-! # Actual mean oscillation from a centered energy average -/

public section

open HarmonicMaps MeasureTheory

namespace StationaryHarmonicMaps.Analysis

/-- An actual bound on the ball's average HS energy gives a linear-radius oscillation bound. -/
theorem meanOscillation_le_of_integral_energy_average {n q : ℕ}
    (x : Domain n) {r L : ℝ} (hr : 0 < r)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain x r) u Du)
    (henergy : (∫ y in Metric.ball x r, hsNormSq (Du y)) ≤
      L * volume.real (Metric.ball x r)) :
    (⨍ y in Metric.ball x r, ‖u y - (⨍ z in Metric.ball x r, u z)‖) ≤
      ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * Real.sqrt L * r := by
  have hmass : 0 < volume.real (Metric.ball x r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_ne_top
  have hmean : (⨍ y in Metric.ball x r, hsNormSq (Du y)) ≤ L := by
    rw [setAverage_eq, smul_eq_mul, mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hmass).mpr henergy
  have hsquare (y : Domain n) : (Real.sqrt (hsNormSq (Du y))) ^ (2 : ℝ) = hsNormSq (Du y) := by
    rw [Real.rpow_two, Real.sq_sqrt (hsNormSq_nonneg _)]
  have hroot : (⨍ y in Metric.ball x r, (Real.sqrt (hsNormSq (Du y))) ^ (2 : ℝ)) ^
      (1 / (2 : ℝ)) ≤ Real.sqrt L := by
    simp only [hsquare]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hmean
  calc
    _ ≤ ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * r *
        (⨍ y in Metric.ball x r, (Real.sqrt (hsNormSq (Du y))) ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) :=
      sobolev_ballAverage_oscillation_le_lp_hs x hr (by norm_num) (by norm_num) hu
    _ ≤ ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * r * Real.sqrt L :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by ring

end StationaryHarmonicMaps.Analysis

end
