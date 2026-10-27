module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation
public import StationaryHarmonicMaps.Analysis.BallMeanDyadic
public import HolderToCK.Foundation.BallVolume

/-! # Quantitative dyadic means from the actual critical Morrey energy -/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps.Analysis

/-- Sixteenth-radius neighborhoods of the seven-eighths ball lie strictly inside the unit ball. -/
theorem closedBall_sixteenth_subset_unit {n : ℕ} {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ)) :
    Metric.closedBall x (1 / 16 : ℝ) ⊆ Metric.ball (0 : Domain n) 1 := by
  intro y hy
  have hyx : dist y x ≤ (1 / 16 : ℝ) := hy
  have hx0 : dist x 0 < (7 / 8 : ℝ) := hx
  change dist y 0 < 1
  exact lt_of_le_of_lt (dist_triangle y x 0) (by linarith only [hyx, hx0])

/-- The actual means grow at most linearly in the number of dyadic scales. -/
theorem exists_dyadic_mean_bound_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤
        ENNReal.ofReal (η ^ 2) →
      ∀ x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ), ∀ m : ℕ,
        ‖(⨍ y in Metric.ball x ((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ m), u y) -
          (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ≤ C * η * ((m : ℝ) + 1) := by
  obtain ⟨B, hB, hosc⟩ := contained_ball_meanOscillation_le_of_criticalMorrey_bound n hn
  let H : ℝ := (2 : ℝ) ^ n * B
  let J : ℝ := (16 : ℝ) ^ n * B
  let C : ℝ := 1 + H + J
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q u Du η hu hη hcritical x hx m
  letI : IsFiniteMeasure (volume.restrict (ballDomain (0 : Domain n) 1).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have huI : IntegrableOn u (Metric.ball (0 : Domain n) 1) volume :=
    hu.2.1.integrable (by norm_num)
  have hosc' (y : Domain n) (r : ℝ) (hr : 0 < r)
      (hsub : Metric.ball y r ⊆ Metric.ball (0 : Domain n) 1) :
      (⨍ z in Metric.ball y r, ‖u z - (⨍ w in Metric.ball y r, u w)‖) ≤ B * η := by
    simpa only [Real.sqrt_sq hη] using
      hosc q 0 1 (η ^ 2) u Du (by norm_num) hu (sq_nonneg η) hcritical y r hr hsub
  have hsub : Metric.ball x (1 / 16 : ℝ) ⊆ Metric.ball (0 : Domain n) 1 :=
    Metric.ball_subset_closedBall.trans (closedBall_sixteenth_subset_unit hx)
  have hhead := ballMean_dyadic_difference_bound u x (by norm_num : (0 : ℝ) < 1 / 16)
    (huI.mono_set hsub) (fun r hr hcap => hosc' x r hr
      ((Metric.ball_subset_ball hcap).trans hsub)) m
  have hmass : volume.real (Metric.ball (0 : Domain n) 1) ≤
      (16 : ℝ) ^ n * volume.real (Metric.ball x (1 / 16 : ℝ)) := by
    rw [HolderToCK.ball_volume_real 0 (by norm_num : (0 : ℝ) < 1),
      HolderToCK.ball_volume_real x (by norm_num : (0 : ℝ) < 1 / 16)]
    rw [one_pow, one_mul, ← mul_assoc, ← mul_pow]
    norm_num
  have hbase := norm_setAverage_sub_le_mul_meanOscillation u
    (Metric.measure_ball_pos volume x (by norm_num : (0 : ℝ) < 1 / 16)).ne'
    measure_ball_ne_top measure_ball_ne_top hsub huI hmass
  have hbase' : ‖(⨍ y in Metric.ball x (1 / 16 : ℝ), u y) -
      (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ≤ J * η := by
    exact (hbase.trans (mul_le_mul_of_nonneg_left (hosc' 0 1 (by norm_num) (Subset.refl _))
      (by positivity))).trans_eq (by dsimp only [J]; ring)
  have hscalar : (m : ℝ) * H + J ≤ C * ((m : ℝ) + 1) := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hJm := mul_nonneg hJ hm
    dsimp only [C]
    nlinarith only [hm, hH, hJm]
  calc
    _ ≤ ‖(⨍ y in Metric.ball x ((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ m), u y) -
        (⨍ y in Metric.ball x (1 / 16 : ℝ), u y)‖ +
        ‖(⨍ y in Metric.ball x (1 / 16 : ℝ), u y) -
          (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (m : ℝ) * (2 : ℝ) ^ n * (B * η) + J * η := add_le_add hhead hbase'
    _ = ((m : ℝ) * H + J) * η := by dsimp only [H]; ring
    _ ≤ (C * ((m : ℝ) + 1)) * η := mul_le_mul_of_nonneg_right hscalar hη
    _ = _ := by ring

end StationaryHarmonicMaps.Analysis

end
