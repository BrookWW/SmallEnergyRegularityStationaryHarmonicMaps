module

public import StationaryHarmonicMaps.Analysis.MeanOscillation
public import HarmonicMaps.Sobolev

/-! # Actual ball means at dyadic radii under uniform mean oscillation -/

public section

open HarmonicMaps MeasureTheory

namespace StationaryHarmonicMaps.Analysis

/-- Each dyadic step costs the same actual mean-oscillation constant. -/
theorem ballMean_dyadic_difference_bound {n q : ℕ}
    (u : Domain n → Ambient q) (x : Domain n) {r₀ B : ℝ} (hr₀ : 0 < r₀)
    (hu : IntegrableOn u (Metric.ball x r₀) volume)
    (hosc : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (⨍ y in Metric.ball x r, ‖u y - (⨍ z in Metric.ball x r, u z)‖) ≤ B) :
    ∀ m : ℕ, ‖(⨍ y in Metric.ball x (r₀ * (1 / 2 : ℝ) ^ m), u y) -
      (⨍ y in Metric.ball x r₀, u y)‖ ≤ (m : ℝ) * (2 : ℝ) ^ n * B := by
  intro m
  induction m with
  | zero => simp only [pow_zero, mul_one, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ m ih =>
      let r := r₀ * (1 / 2 : ℝ) ^ m
      have hr : 0 < r := mul_pos hr₀ (pow_pos (by norm_num) m)
      have hrr₀ : r ≤ r₀ := mul_le_of_le_one_right hr₀.le
        (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
      have hnext : r₀ * (1 / 2 : ℝ) ^ (m + 1) = r / 2 := by dsimp only [r]; rw [pow_succ]; ring
      have hstep := norm_ballAverage_sub_le_meanOscillation u (half_pos hr) hr
        (Metric.ball_subset_ball (by linarith only [hr] : r / 2 ≤ r))
        (show r ≤ 2 * (r / 2) by linarith)
        (hu.mono_set (Metric.ball_subset_ball hrr₀))
      have hbound : ‖(⨍ y in Metric.ball x (r / 2), u y) -
          (⨍ y in Metric.ball x r, u y)‖ ≤ (2 : ℝ) ^ n * B :=
        hstep.trans (mul_le_mul_of_nonneg_left (hosc r hr hrr₀) (by positivity))
      rw [hnext]
      calc
        _ ≤ ‖(⨍ y in Metric.ball x (r / 2), u y) - (⨍ y in Metric.ball x r, u y)‖ +
            ‖(⨍ y in Metric.ball x r, u y) - (⨍ y in Metric.ball x r₀, u y)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (2 : ℝ) ^ n * B + (m : ℝ) * (2 : ℝ) ^ n * B := add_le_add hbound ih
        _ = _ := by push_cast; ring

end StationaryHarmonicMaps.Analysis

end
