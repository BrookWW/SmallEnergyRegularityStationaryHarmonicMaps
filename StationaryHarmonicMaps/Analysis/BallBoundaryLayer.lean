module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Actual small-volume boundary layers of the unit ball -/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem unit_ball_boundary_volume {n : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    volume.real (Metric.ball (0 : Domain n) 1 \ Metric.ball (0 : Domain n) r) =
      volume.real (Metric.ball (0 : Domain n) 1) -
        r ^ n * volume.real (Metric.ball (0 : Domain n) 1) := by
  rw [measureReal_sdiff (Metric.ball_subset_ball hr1.le) measurableSet_ball measure_ball_ne_top]
  congr 1
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume (0 : Domain n) hr,
    ENNReal.toReal_mul, finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
  rfl

/-- A genuine strictly interior radius makes the actual boundary-layer real volume arbitrarily small. -/
theorem exists_inner_unitBall_boundary_volume_lt (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      volume.real (Metric.ball (0 : Domain n) 1 \ Metric.ball (0 : Domain n) r) < ε := by
  let r : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 2)
  have hpos (k : ℕ) : 0 < r k := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have H : 1 / ((k : ℝ) + 2) < 1 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
    dsimp only [r]
    linarith
  have hlt (k : ℕ) : r k < 1 := by
    dsimp only [r]
    have H : 0 < 1 / ((k : ℝ) + 2) := by positivity
    linarith
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    have H := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    convert H using 1
    funext k
    congr 1
    push_cast
    ring
  have hr : Tendsto r atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  have hvolume : Tendsto (fun k => volume.real
      (Metric.ball (0 : Domain n) 1 \ Metric.ball (0 : Domain n) (r k))) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds (x := volume.real (Metric.ball (0 : Domain n) 1))).sub
      ((hr.pow n).mul_const (volume.real (Metric.ball (0 : Domain n) 1)))
    simpa only [unit_ball_boundary_volume (hpos _) (hlt _), one_pow, one_mul, sub_self] using H
  obtain ⟨k, hk⟩ := (hvolume.eventually_lt_const hε).exists
  exact ⟨r k, hpos k, hlt k, hk⟩

/-- Every nonnegative actual coefficient admits a uniformly small weighted boundary layer. -/
theorem exists_inner_unitBall_scaled_boundary_lt (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      C * volume.real (Metric.ball (0 : Domain n) 1 \ Metric.ball (0 : Domain n) r) < ε := by
  obtain ⟨r, hr, hr1, hvol⟩ := exists_inner_unitBall_boundary_volume_lt n
    (ε / (C + 1)) (div_pos hε (by positivity))
  refine ⟨r, hr, hr1, ?_⟩
  calc
    _ ≤ (C + 1) * volume.real (Metric.ball (0 : Domain n) 1 \ Metric.ball (0 : Domain n) r) :=
      mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
    _ < ε := by
      simpa only [mul_comm] using (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hvol

end StationaryHarmonicMaps.Analysis

end
