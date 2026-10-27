module

public import HolderToCK.Foundation.HolderBounds
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # The fixed radii of the higher derivative induction

Index k denotes derivative order k+1, so the literal radius is the manuscript's
s_(k+1). Each positive margin is chosen before the map and the small parameter.
-/

public section

open HarmonicMaps Set Filter
open scoped Topology

namespace HolderToCK

@[expose] noncomputable def nestedRadius (k : ℕ) : ℝ :=
  1 / 2 + (1 / 8) * (2 : ℝ) ^ (-(k : ℝ))

theorem nestedRadius_zero : nestedRadius 0 = 5 / 8 := by
  norm_num [nestedRadius]

theorem nestedRadius_eq_geometric (k : ℕ) :
    nestedRadius k = 1 / 2 + (1 / 8) * (1 / 2 : ℝ) ^ k := by
  rw [nestedRadius, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
  norm_num

theorem half_lt_nestedRadius (k : ℕ) : 1 / 2 < nestedRadius k := by
  have hp : 0 < (2 : ℝ) ^ (-(k : ℝ)) := Real.rpow_pos_of_pos zero_lt_two _
  dsimp only [nestedRadius]
  exact lt_add_of_pos_right _ (mul_pos (by norm_num) hp)

theorem nestedRadius_pos (k : ℕ) : 0 < nestedRadius k :=
  (by norm_num : (0 : ℝ) < 1 / 2).trans (half_lt_nestedRadius k)

theorem nestedRadius_le_fiveEighths (k : ℕ) : nestedRadius k ≤ 5 / 8 := by
  have hp : (2 : ℝ) ^ (-(k : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg k))
  dsimp only [nestedRadius]
  linarith only [mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1 / 8)]

theorem nestedRadius_succ (k : ℕ) :
    nestedRadius (k + 1) = 1 / 2 + (nestedRadius k - 1 / 2) / 2 := by
  rw [nestedRadius_eq_geometric, nestedRadius_eq_geometric, pow_succ]
  ring

theorem nestedRadius_gap (k : ℕ) :
    nestedRadius k - nestedRadius (k + 1) = (1 / 16) * (2 : ℝ) ^ (-(k : ℝ)) := by
  rw [nestedRadius_succ, nestedRadius]
  ring

theorem nestedRadius_gap_pos (k : ℕ) : 0 < nestedRadius k - nestedRadius (k + 1) := by
  rw [nestedRadius_gap]
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos zero_lt_two _)

theorem nestedRadius_succ_lt (k : ℕ) : nestedRadius (k + 1) < nestedRadius k :=
  sub_pos.mp (nestedRadius_gap_pos k)

theorem nestedRadius_tendsto : Tendsto nestedRadius atTop (𝓝 (1 / 2)) := by
  have ht : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h : Tendsto (fun k : ℕ => 1 / 2 + (1 / 8) * (1 / 2 : ℝ) ^ k)
      atTop (𝓝 (1 / 2 + (1 / 8 : ℝ) * 0)) :=
    tendsto_const_nhds.add (ht.const_mul (1 / 8 : ℝ))
  simpa only [mul_zero, add_zero, ← nestedRadius_eq_geometric] using h

theorem halfBall_subset_nestedBall {n : ℕ} (k : ℕ) :
    Metric.ball (0 : Domain n) (1 / 2) ⊆ Metric.ball (0 : Domain n) (nestedRadius k) :=
  Metric.ball_subset_ball (half_lt_nestedRadius k).le

theorem nestedBall_succ_subset {n : ℕ} (k : ℕ) :
    Metric.ball (0 : Domain n) (nestedRadius (k + 1)) ⊆
      Metric.ball (0 : Domain n) (nestedRadius k) :=
  Metric.ball_subset_ball (nestedRadius_succ_lt k).le

end HolderToCK
end
