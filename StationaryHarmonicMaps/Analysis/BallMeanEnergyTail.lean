module

public import StationaryHarmonicMaps.Analysis.MeanOscillationFromAverageEnergy
public import StationaryHarmonicMaps.Analysis.MeanOscillation
public import HarmonicMaps.SobolevRestriction

/-!
# Actual ball-mean tails under bounded centered energy averages

The point is a Lebesgue point of the same original map. Linear-radius mean
oscillation gives the genuine mean limit and identifies it with that value.
No continuity representative or regularity conclusion is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual bounded average energy controls the original value at a Lebesgue point. -/
theorem ballMean_value_tail_of_energy_average {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (x : Domain n) {r₀ L : ℝ} (hr₀ : 0 < r₀)
    (hclosed : Metric.closedBall x r₀ ⊆ Ω.val)
    (hLebesgue : Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, u y)
      (𝓝[>] (0 : ℝ)) (𝓝 (u x)))
    (henergy : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫ y in Metric.ball x r, hsNormSq (Du y)) ≤ L * volume.real (Metric.ball x r)) :
    ‖(⨍ y in Metric.ball x r₀, u y) - u x‖ ≤
      ((2 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ))) *
        Real.sqrt L * r₀ := by
  let D : ℝ := (2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)
  have hK : 0 ≤ D * Real.sqrt L := mul_nonneg (by dsimp only [D]; positivity) (Real.sqrt_nonneg _)
  letI : IsFiniteMeasure (volume.restrict (ballDomain x r₀).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hW := hu.memW12_ball hclosed
  have hI : IntegrableOn u (Metric.ball x r₀) volume := hW.2.1.integrable (by norm_num)
  have hosc : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (⨍ y in Metric.ball x r, ‖u y - (⨍ z in Metric.ball x r, u z)‖) ≤
        (D * Real.sqrt L) * r ^ (1 : ℝ) := by
    intro r hr hcap
    have hsmall := hu.memW12_ball
      ((Metric.closedBall_subset_closedBall hcap).trans hclosed)
    simpa only [Real.rpow_one] using
      meanOscillation_le_of_integral_energy_average x hr hsmall (henergy r hr hcap)
  obtain ⟨w, hw, _⟩ := existsUnique_ballAverage_limit_of_meanOscillation_radius u x
    (by norm_num : (0 : ℝ) < 1) hK hr₀ hI hosc
  have hwx : w = u x := tendsto_nhds_unique hw.1 hLebesgue
  have hbound := hw.2 r₀ hr₀ le_rfl
  rw [hwx, Real.rpow_one, Real.rpow_one] at hbound
  have hcoef : ((2 : ℝ) ^ n * (D * Real.sqrt L)) * r₀ / (1 - 1 / 2) =
      ((2 : ℝ) ^ (n + 1) * D) * Real.sqrt L * r₀ := by
    rw [pow_succ]
    ring
  exact hbound.trans_eq hcoef

end StationaryHarmonicMaps.Analysis

end
