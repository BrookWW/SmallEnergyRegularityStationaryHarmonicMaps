module

public import StationaryHarmonicMaps.Analysis.SobolevLpOscillation

/-! # Actual weighted column sums and Hilbert--Schmidt bounds -/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

/-- A uniform real coefficient bound controls the actual vector sum. -/
theorem norm_sum_smul_le_sum_column_norm {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Fin n → ℝ) (v : Fin n → E) {B : ℝ} (hb : ∀ i, |d i| ≤ B) :
    ‖∑ i : Fin n, d i • v i‖ ≤ B * ∑ i : Fin n, ‖v i‖ := by
  calc
    _ ≤ ∑ i : Fin n, ‖d i • v i‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |d i| * ‖v i‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin n, B * ‖v i‖ := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The weighted sum is bounded by the true HS column norm. -/
theorem norm_sum_smul_le_hs {n q : ℕ} (d : Fin n → ℝ) (v : Gradient n q)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, |d i| ≤ B) :
    ‖∑ i : Fin n, d i • v i‖ ≤ B * Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq v) := by
  exact ((norm_sum_smul_le_sum_column_norm d v hb).trans
    (mul_le_mul_of_nonneg_left (sum_column_norm_le_sqrt_dimension_mul_hs v) hB)).trans_eq
      (mul_assoc _ _ _).symm

/-- Weighted operator images use actual columnwise operator bounds and the full HS norm. -/
theorem norm_sum_smul_apply_le_hs {n m q : ℕ}
    (d : Fin n → ℝ) (T : Fin n → Ambient q →L[ℝ] Ambient q)
    (v : Gradient n m) (a : Ambient q) {B L : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hb : ∀ i, |d i| ≤ B)
    (hT : ∀ i, ‖T i‖ ≤ L * ‖v i‖) :
    ‖∑ i : Fin n, d i • T i a‖ ≤
      B * L * Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq v) * ‖a‖ := by
  have hsum : (∑ i : Fin n, ‖T i a‖) ≤ L * (∑ i : Fin n, ‖v i‖) * ‖a‖ := by
    calc
      _ ≤ ∑ i : Fin n, (L * ‖v i‖) * ‖a‖ := Finset.sum_le_sum
        (fun i _ => ((T i).le_opNorm a).trans
          (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg a)))
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  calc
    _ ≤ B * ∑ i : Fin n, ‖T i a‖ := norm_sum_smul_le_sum_column_norm d _ hb
    _ ≤ B * (L * (∑ i : Fin n, ‖v i‖) * ‖a‖) := mul_le_mul_of_nonneg_left hsum hB
    _ ≤ B * (L * (Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq v)) * ‖a‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (sum_column_norm_le_sqrt_dimension_mul_hs v) hL) (norm_nonneg a)) hB
    _ = _ := by ring

end StationaryHarmonicMaps.Analysis

end
