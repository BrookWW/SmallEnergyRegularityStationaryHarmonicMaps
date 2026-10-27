module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Exact Euclidean ball volumes and radius ratios -/

public section

open HarmonicMaps MeasureTheory

namespace HolderToCK

theorem ball_volume_real {n : ℕ} (a : Domain n) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball a r) =
      r ^ n * volume.real (Metric.ball (0 : Domain n) 1) := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume a hr, ENNReal.toReal_mul]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
  rfl

theorem ball_volume_real_pos {n : ℕ} (a : Domain n) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (Metric.ball a r) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume a hr).ne' measure_ball_ne_top

theorem ball_volume_ratio_half {n : ℕ} (a : Domain n) {R θ : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) :
    volume.real (Metric.ball a (θ * R)) *
      (volume.real (Metric.ball (0 : Domain n) (R / 2)))⁻¹ =
      (2 : ℝ) ^ n * θ ^ n := by
  have hV := (ball_volume_real_pos (0 : Domain n) (by norm_num : (0 : ℝ) < 1)).ne'
  rw [ball_volume_real a (mul_pos hθ hR),
    ball_volume_real (0 : Domain n) (half_pos hR), mul_pow, div_pow]
  field_simp [pow_ne_zero n hR.ne', hV]

end HolderToCK
end
