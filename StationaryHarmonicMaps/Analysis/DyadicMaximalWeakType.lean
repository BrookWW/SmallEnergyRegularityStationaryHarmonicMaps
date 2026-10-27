module

public import StationaryHarmonicMaps.Analysis.DyadicBallMaximal

/-!
# Actual Vitali bounds for finite dyadic maximal windows

Every selected finite-window scale has its genuine radius cap 2^N.
The original ball average supplies the real level hypothesis of the
proved Vitali estimate. Splitting the original density at a positive
level gives the actual truncated-tail weak bound needed for strong Lp.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem mul_volume_le_of_average_ge {n : ℕ}
    (f : Domain n → ℝ≥0∞) (x : Domain n) (r : PositiveRadius) {L : ℝ≥0∞}
    (hL : L ≤ centeredBallAverageENN f x r) :
    L*volume (Metric.ball x r.val) ≤ ∫⁻ y in Metric.ball x r.val, f y := by
  calc
    _ = volume (Metric.ball x r.val)*L := mul_comm _ _
    _ ≤ volume (Metric.ball x r.val)*
        ((volume (Metric.ball x r.val))⁻¹ * ∫⁻ y in Metric.ball x r.val, f y) :=
      mul_le_mul_of_nonneg_left hL zero_le
    _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel
      (Metric.measure_ball_pos volume x r.property).ne' measure_ball_ne_top,one_mul]

/-- The actual finite window has the genuine centered weak (1,1) bound, uniformly in its two-sided scale cutoff. -/
theorem dyadicBallMaximalWindow_weak_one {n : ℕ}
    (f : Domain n → ℝ≥0∞) (N : ℕ) (level : ℝ) (hlevel : 0 < level) :
    volume {x | ENNReal.ofReal level < dyadicBallMaximalWindow f N x} ≤
      ENNReal.ofReal ((5 : ℝ)^n/level) * ∫⁻ y, f y := by
  apply centered_ball_superlevel_measure_le f _ ((2 : ℝ)^(N : ℤ)) level hlevel
  intro x hx
  change ENNReal.ofReal level < (Finset.Icc (-(N : ℤ)) (N : ℤ)).sup
    (fun j => centeredBallAverageENN f x ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩) at hx
  obtain ⟨j,hj,havg⟩ := Finset.lt_sup_iff.mp hx
  refine ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j,
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ)≤2) (Finset.mem_Icc.mp hj).2,?_⟩
  exact mul_volume_le_of_average_ge f x ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩ havg.le

private theorem truncated_ball_level {n : ℕ}
    (f : Domain n → ℝ≥0∞) (x : Domain n) (r : PositiveRadius)
    (level : ℝ) (hlevel : 0 < level)
    (havg : ENNReal.ofReal (2*level) < centeredBallAverageENN f x r) :
    ENNReal.ofReal level * volume (Metric.ball x r.val) ≤
      ∫⁻ y in Metric.ball x r.val, if ENNReal.ofReal level < f y then f y else 0 := by
  classical
  let L := ENNReal.ofReal level
  let g := fun y => if L < f y then f y else 0
  have hpoint (y : Domain n) : f y ≤ L+g y := by
    dsimp only [g]
    by_cases hy : L < f y
    · rw [if_pos hy]
      exact le_add_of_nonneg_left zero_le
    · rw [if_neg hy,add_zero]
      exact le_of_not_gt hy
  have hI : (∫⁻ y in Metric.ball x r.val, f y) ≤
      L*volume (Metric.ball x r.val) + ∫⁻ y in Metric.ball x r.val, g y := by
    calc
      _ ≤ ∫⁻ y in Metric.ball x r.val, L+g y := lintegral_mono hpoint
      _ = _ := by
        rw [lintegral_add_left measurable_const g,lintegral_const]
        simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter]
  have H := (mul_volume_le_of_average_ge f x r havg.le).trans hI
  rw [show 2*level=level+level by ring,ENNReal.ofReal_add hlevel.le hlevel.le,add_mul] at H
  have hfinite : L*volume (Metric.ball x r.val) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr measure_ball_ne_top)).ne
  exact ENNReal.le_of_add_le_add_left hfinite H

/-- Large original finite-window averages are controlled by the actual original density truncated above half the level. -/
theorem dyadicBallMaximalWindow_truncated_weak_one {n : ℕ}
    (f : Domain n → ℝ≥0∞) (N : ℕ) (level : ℝ) (hlevel : 0 < level) :
    volume {x | ENNReal.ofReal (2*level) < dyadicBallMaximalWindow f N x} ≤
      ENNReal.ofReal ((5 : ℝ)^n/level) *
        ∫⁻ y, if ENNReal.ofReal level < f y then f y else 0 := by
  classical
  let g := fun y => if ENNReal.ofReal level < f y then f y else 0
  apply centered_ball_superlevel_measure_le g _ ((2 : ℝ)^(N : ℤ)) level hlevel
  intro x hx
  change ENNReal.ofReal (2*level) < (Finset.Icc (-(N : ℤ)) (N : ℤ)).sup
    (fun j => centeredBallAverageENN f x ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩) at hx
  obtain ⟨j,hj,havg⟩ := Finset.lt_sup_iff.mp hx
  refine ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j,
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ)≤2) (Finset.mem_Icc.mp hj).2,?_⟩
  exact truncated_ball_level f x ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩ level hlevel havg

end StationaryHarmonicMaps.Analysis

end
