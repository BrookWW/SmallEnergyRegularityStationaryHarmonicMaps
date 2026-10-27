module

public import HarmonicMaps.Energy

/-! # Actual HS-square bound for the cutoff weak gradient -/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

private theorem norm_add_sq_le_two {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a + b)) (norm_add_le a b) 2
  nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]

/-- The actual displayed cutoff columns retain the full HS square and both Leibniz terms. -/
theorem cutoff_gradient_hsNormSq_le {n q : ℕ}
    (v : Gradient n q) (a : Ambient q) (s : ℝ) (d : Fin n → ℝ) {A B : ℝ}
    (hs : |s| ≤ A) (hd : ∀ i, |d i| ≤ B) :
    hsNormSq (fun i => s • v i + d i • a) ≤
      2 * A ^ 2 * hsNormSq v + (2 * (n : ℝ) * B ^ 2) * ‖a‖ ^ 2 := by
  have hs2 : |s| ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg s) hs 2
  have hd2 (i : Fin n) : |d i| ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hd i) 2
  have hpoint (i : Fin n) : ‖s • v i + d i • a‖ ^ 2 ≤
      2 * A ^ 2 * ‖v i‖ ^ 2 + 2 * B ^ 2 * ‖a‖ ^ 2 := by
    calc
      _ ≤ 2 * ‖s • v i‖ ^ 2 + 2 * ‖d i • a‖ ^ 2 := norm_add_sq_le_two _ _
      _ = 2 * (|s| ^ 2 * ‖v i‖ ^ 2) + 2 * (|d i| ^ 2 * ‖a‖ ^ 2) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow]
      _ ≤ 2 * (A ^ 2 * ‖v i‖ ^ 2) + 2 * (B ^ 2 * ‖a‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs2 (sq_nonneg _))
          (by norm_num)) (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hd2 i) (sq_nonneg _)) (by norm_num))
      _ = _ := by ring
  calc
    _ ≤ ∑ i : Fin n, (2 * A ^ 2 * ‖v i‖ ^ 2 + 2 * B ^ 2 * ‖a‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsNormSq]
      ring

end StationaryHarmonicMaps.Analysis

end
