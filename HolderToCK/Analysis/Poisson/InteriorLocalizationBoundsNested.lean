/- Copyright (c) 2026. All rights reserved. -/
module

public import HolderToCK.Analysis.Poisson.InteriorLocalizationBounds

/-! # Uniform localization between nested balls

Radius `(t-s)/2` balls centered in the inner ball lie in the outer ball.
Local estimates control pairs below `(t-s)/8`; the derivative supremum
controls the remaining pairs with the same Holder exponent.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

theorem nested_center_ball_subset {n : ℕ} {s t : ℝ} (hst : s < t)
    {x : Domain n} (hx : x ∈ Metric.ball (0 : Domain n) s) :
    Metric.ball x ((t - s) / 2) ⊆ Metric.ball (0 : Domain n) t := by
  intro y hy
  have hxy : dist y x < (t - s) / 2 := Metric.mem_ball.mp hy
  have hx0 : dist x (0 : Domain n) < s := Metric.mem_ball.mp hx
  apply Metric.mem_ball.mpr
  have hdist := dist_triangle y x (0 : Domain n)
  linarith only [hdist, hxy, hx0, hst]

theorem nested_holderBoundOn_of_local_and_sup {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {g : Domain n → E} {s t γ A B : ℝ}
    (hst : s < t) (hγ : 0 ≤ γ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlocal : ∀ x ∈ Metric.ball (0 : Domain n) s,
      HolderBoundOn (Metric.ball x ((t - s) / 4)) g γ A)
    (hsup : ∀ x ∈ Metric.ball (0 : Domain n) s, ‖g x‖ ≤ B) :
    HolderBoundOn (Metric.ball (0 : Domain n) s) g γ
      (A + 2 * B / Real.rpow ((t - s) / 8) γ) := by
  have hgap : 0 < (t - s) / 8 := by linarith only [hst]
  have hquarter : 0 < (t - s) / 4 := by linarith only [hst]
  have hpow : 0 < Real.rpow ((t - s) / 8) γ := Real.rpow_pos_of_pos hgap γ
  have hfarcoef : 0 ≤ 2 * B / Real.rpow ((t - s) / 8) γ :=
    div_nonneg (mul_nonneg (by norm_num) hB) hpow.le
  intro x hx y hy
  by_cases hclose : dist x y < (t - s) / 8
  · have hyx : y ∈ Metric.ball x ((t - s) / 4) := by
      apply Metric.mem_ball.mpr
      rw [dist_comm]
      linarith only [hclose, hgap]
    exact (hlocal x hx x (Metric.mem_ball_self hquarter) y hyx).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hfarcoef)
        (Real.rpow_nonneg dist_nonneg γ))
  · have hdist : (t - s) / 8 ≤ dist x y := le_of_not_gt hclose
    have hpowl : Real.rpow ((t - s) / 8) γ ≤ Real.rpow (dist x y) γ :=
      Real.rpow_le_rpow hgap.le hdist hγ
    calc
      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hsup x hx) (hsup y hy)
      _ = (2 * B / Real.rpow ((t - s) / 8) γ) * Real.rpow ((t - s) / 8) γ := by
        rw [div_mul_cancel₀ _ hpow.ne']
        ring
      _ ≤ (2 * B / Real.rpow ((t - s) / 8) γ) * Real.rpow (dist x y) γ :=
        mul_le_mul_of_nonneg_left hpowl hfarcoef
      _ ≤ (A + 2 * B / Real.rpow ((t - s) / 8) γ) * Real.rpow (dist x y) γ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA)
          (Real.rpow_nonneg dist_nonneg γ)

end HolderToCK
end
