module

public import HolderToCK.Analysis.Poisson.PotentialBounds
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Translation estimates for the Hessian kernel -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

@[expose] noncomputable def hessianKernelTranslationConstant (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) + 5) * (euclideanSphereArea n)⁻¹ * (2 : ℝ) ^ ((n : ℝ) + 1)

theorem hessianKernelExpression_differentiableAt {n : ℕ} (i j : Fin n)
    (z : Domain n) (hz : z ≠ 0) : DifferentiableAt ℝ (hessianKernelExpression i j) z := by
  have hd (p : ℝ) : DifferentiableAt ℝ (fun w : Domain n => ‖w‖ ^ p) z :=
    (norm_rpow_hasFDerivAt_of_ne_zero p z hz).differentiableAt
  exact (((hd _).const_mul (if i = j then 1 else 0)).sub
      ((((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).differentiableAt).const_mul
        (n : ℝ)).mul
        (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).differentiableAt |>.mul
          (hd _))).const_mul _

theorem hessianKernelExpression_shift_difference_bound {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (x y z : Domain n) (hfar : 2 * dist x y ≤ ‖x - z‖) :
    |hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)| ≤
      hessianKernelTranslationConstant n * dist x y * ‖x - z‖ ^ (-(n : ℝ) - 1) := by
  by_cases hxy : x = y
  · subst y
    rw [sub_self, abs_zero, dist_self, mul_zero, zero_mul]
  · let a : Domain n := x - z
    let b : Domain n := y - z
    have hd : 0 < dist x y := dist_pos.mpr hxy
    have ha : 0 < ‖a‖ := lt_of_lt_of_le (mul_pos zero_lt_two hd) hfar
    have hab : dist a b = dist x y := by
      rw [dist_eq_norm, dist_eq_norm]
      dsimp only [a, b]
      congr 1
      abel
    have hw (w : Domain n) (hw : w ∈ Metric.closedBall a (‖a‖ / 2)) :
        ‖a‖ / 2 ≤ ‖w‖ := by
      have hdist : ‖a - w‖ ≤ ‖a‖ / 2 := by
        rw [norm_sub_rev, ← dist_eq_norm]
        exact hw
      linarith only [norm_sub_norm_le a w, hdist]
    have hw0 (w : Domain n) (hws : w ∈ Metric.closedBall a (‖a‖ / 2)) : w ≠ 0 :=
      norm_pos_iff.mp ((half_pos ha).trans_le (hw w hws))
    have hC : 0 ≤ (n : ℝ) * ((n : ℝ) + 5) * (euclideanSphereArea n)⁻¹ :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by positivity))
        (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)
    have hBound (w : Domain n) (hws : w ∈ Metric.closedBall a (‖a‖ / 2)) :
        ‖fderiv ℝ (hessianKernelExpression i j) w‖ ≤
        ((n : ℝ) * ((n : ℝ) + 5) * (euclideanSphereArea n)⁻¹) *
          (‖a‖ / 2) ^ (-(n : ℝ) - 1) := by
      exact (hessianKernelExpression_fderiv_bound hn i j w (hw0 w hws)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (half_pos ha)
          (hw w hws) (by linarith only [Nat.cast_nonneg (α := ℝ) n])) hC)
    have hba : b ∈ Metric.closedBall a (‖a‖ / 2) := by
      rw [Metric.mem_closedBall, dist_comm, hab]
      linarith only [hfar]
    have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun w hws => hessianKernelExpression_differentiableAt i j w (hw0 w hws)) hBound
      (convex_closedBall a (‖a‖ / 2))
      (Metric.mem_closedBall_self (half_pos ha).le) hba
    have hnorm : ‖b - a‖ = dist x y := by
      rw [← dist_eq_norm, dist_comm b a, hab]
    rw [Real.norm_eq_abs, abs_sub_comm, hnorm] at hm
    have hp : (‖a‖ / 2) ^ (-(n : ℝ) - 1) =
        ‖a‖ ^ (-(n : ℝ) - 1) * (2 : ℝ) ^ ((n : ℝ) + 1) := by
      rw [Real.div_rpow (norm_nonneg a) (by norm_num)]
      have htwo : (2 : ℝ) ^ (-(n : ℝ) - 1) =
          ((2 : ℝ) ^ ((n : ℝ) + 1))⁻¹ := by
        rw [show -(n : ℝ) - 1 = -((n : ℝ) + 1) by ring,
          Real.rpow_neg (by norm_num)]
      rw [htwo, div_inv_eq_mul]
    change |hessianKernelExpression i j a - hessianKernelExpression i j b| ≤ _
    calc
      _ ≤ _ := hm
      _ = _ := by rw [hp, hessianKernelTranslationConstant]; ring

end HolderToCK
end
