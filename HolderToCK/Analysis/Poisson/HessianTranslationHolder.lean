module

public import HolderToCK.Analysis.Poisson.HessianTranslationCancellation

/-! # The full exponent Holder estimate for the potential Hessian -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

@[expose] noncomputable def potentialHessianHolderConstant (n : ℕ) (η : ℝ) : ℝ :=
  1 / (n : ℝ) + ((n : ℝ) + 1) * ((2 : ℝ) ^ η + (3 : ℝ) ^ η) / η +
    hessianFarHolderConstant n η + ((n : ℝ) + 1) * Real.log 3

theorem potentialHessianHolderConstant_nonneg {n : ℕ} (hn : 0 < n) {η : ℝ}
    (hη : 0 < η) (hη1 : η < 1) : 0 ≤ potentialHessianHolderConstant n η := by
  have hnear : 0 ≤ ((n : ℝ) + 1) * ((2 : ℝ) ^ η + (3 : ℝ) ^ η) / η :=
    div_nonneg (mul_nonneg (by positivity)
      (add_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _))) hη.le
  have hfar : 0 ≤ hessianFarHolderConstant n η :=
    div_nonneg (mul_nonneg (mul_nonneg (hessianKernelTranslationConstant_nonneg hn)
      (euclideanSphereArea_pos hn).le) (Real.rpow_nonneg (by norm_num) _)) (sub_pos.mpr hη1).le
  have hlog : 0 ≤ ((n : ℝ) + 1) * Real.log 3 :=
    mul_nonneg (by positivity) (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
  exact add_nonneg (add_nonneg (add_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n)) hnear) hfar) hlog

theorem potentialHessianExpression_cancelled_translation_decomposition {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x y : Domain n) (hxy : x ≠ y) :
    potentialHessianExpression i j g x - potentialHessianExpression i j g y =
      (((if i = j then 1 else 0) / (n : ℝ)) • (g x - g y) +
        ((∫ z in Metric.ball x (2 * dist x y),
          hessianKernelExpression i j (x - z) • (g z - g x)) -
        ∫ z in Metric.ball x (2 * dist x y),
          hessianKernelExpression i j (y - z) • (g z - g y))) +
      (∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        (hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) •
          (g z - g x)) +
      (∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
        hessianKernelExpression i j (y - z)) • (g x - g y) := by
  rw [potentialHessianExpression_translation_decomposition hn i j hη hH hHolder hcg x y hxy,
    hessianKernelDifference_exterior_cancellation hn i j x y hxy]
  simp only [smul_sub]
  abel

theorem potentialHessianExpression_translation_difference_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g)
    (x y : Domain n) (hxy : x ≠ y) :
    ‖potentialHessianExpression i j g x - potentialHessianExpression i j g y‖ ≤
      potentialHessianHolderConstant n η * H * dist x y ^ η := by
  let N₁ : E := ∫ z in Metric.ball x (2 * dist x y),
    hessianKernelExpression i j (x - z) • (g z - g x)
  let N₂ : E := ∫ z in Metric.ball x (2 * dist x y),
    hessianKernelExpression i j (y - z) • (g z - g y)
  let W : E := ∫ z in (Metric.ball x (2 * dist x y))ᶜ,
    (hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) • (g z - g x)
  let C : ℝ := ∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
    hessianKernelExpression i j (y - z)
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hgd : ‖g x - g y‖ ≤ H * dist x y ^ η := by
    simpa only [Real.rpow_eq_pow] using hHolder x (mem_univ _) y (mem_univ _)
  have hdiagCoeff : 0 ≤ 1 / (n : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg n)
  have hdiagAbs : ‖((if i = j then 1 else 0) / (n : ℝ))‖ ≤ 1 / (n : ℝ) := by
    by_cases hij : i = j
    · rw [if_pos hij, Real.norm_of_nonneg hdiagCoeff]
    · rw [if_neg hij, zero_div, norm_zero]
      exact hdiagCoeff
  have hD : ‖((if i = j then 1 else 0) / (n : ℝ)) • (g x - g y)‖ ≤
      (1 / (n : ℝ)) * H * dist x y ^ η := by
    rw [norm_smul]
    exact ((mul_le_mul_of_nonneg_right hdiagAbs (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hgd hdiagCoeff)).trans_eq (mul_assoc _ _ _).symm
  have hN₁ : ‖N₁‖ ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ η / η) * H * dist x y ^ η := by
    calc
      _ ≤ ((n : ℝ) + 1) * H * (2 * dist x y) ^ η / η :=
        (norm_integral_le_integral_norm _).trans
          (hessianKernelExpression_shiftedHolderDifference_integral_norm_bound hn i j hη hH
            (mul_pos zero_lt_two hd) hHolder x)
      _ = _ := by rw [Real.mul_rpow zero_lt_two.le hd.le]; ring
  have hN₂ : ‖N₂‖ ≤ (((n : ℝ) + 1) * (3 : ℝ) ^ η / η) * H * dist x y ^ η := by
    calc
      _ ≤ ((n : ℝ) + 1) * H * (3 * dist x y) ^ η / η :=
        hessianKernelExpression_commonNear_integral_bound hn i j hη hH hHolder x y hxy
      _ = _ := by rw [Real.mul_rpow (by norm_num) hd.le]; ring
  have hW : ‖W‖ ≤ hessianFarHolderConstant n η * H * dist x y ^ η :=
    hessianKernelDifference_holderFar_integral_bound hn i j hη hη1 hH hHolder x y hxy
  have hC : ‖C • (g x - g y)‖ ≤ (((n : ℝ) + 1) * Real.log 3) * H * dist x y ^ η := by
    rw [norm_smul, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right
      (hessianKernelExpression_commonAnnulus_integral_bound hn i j x y hxy) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hgd (mul_nonneg (by positivity)
          (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le))).trans_eq (mul_assoc _ _ _).symm
  rw [potentialHessianExpression_cancelled_translation_decomposition hn i j hη hH hHolder hcg x y hxy]
  change ‖((((if i = j then 1 else 0) / (n : ℝ)) • (g x - g y) + (N₁ - N₂)) + W) +
    C • (g x - g y)‖ ≤ _
  calc
    _ ≤ ((‖((if i = j then 1 else 0) / (n : ℝ)) • (g x - g y)‖ + (‖N₁‖ + ‖N₂‖)) + ‖W‖) +
        ‖C • (g x - g y)‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))) le_rfl)) le_rfl)
    _ ≤ (((1 / (n : ℝ)) * H * dist x y ^ η +
        ((((n : ℝ) + 1) * (2 : ℝ) ^ η / η) * H * dist x y ^ η +
          (((n : ℝ) + 1) * (3 : ℝ) ^ η / η) * H * dist x y ^ η)) +
        hessianFarHolderConstant n η * H * dist x y ^ η) +
        (((n : ℝ) + 1) * Real.log 3) * H * dist x y ^ η :=
      add_le_add (add_le_add (add_le_add hD (add_le_add hN₁ hN₂)) hW) hC
    _ = _ := by rw [potentialHessianHolderConstant]; ring

theorem potentialHessianExpression_holderBound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g) :
    HolderBoundOn univ (potentialHessianExpression i j g) η
      (potentialHessianHolderConstant n η * H) := by
  intro x _ y _
  rw [Real.rpow_eq_pow]
  by_cases hxy : x = y
  · subst y
    rw [sub_self, norm_zero, dist_self, Real.zero_rpow hη.ne', mul_zero]
  · exact potentialHessianExpression_translation_difference_bound hn i j hη hη1 hH hHolder hcg x y hxy

end HolderToCK
end
