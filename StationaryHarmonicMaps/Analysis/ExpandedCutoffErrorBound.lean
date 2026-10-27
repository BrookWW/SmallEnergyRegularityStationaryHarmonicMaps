module

public import StationaryHarmonicMaps.Analysis.OrthogonalOperatorBounds
public import StationaryHarmonicMaps.Analysis.WeightedColumnBounds

/-!
# A pointwise bound for all four actual cutoff error terms

Orthogonality supplies the inverse-frame contraction. The continuous linear
coefficient decoder supplies both operator bounds. The resulting estimate
uses true HS column norms and retains the factor two in the gradient term.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

/-- All four expanded error terms have the actual HS product bound. -/
theorem expanded_cutoff_error_norm_le_hs {n m q : ℕ}
    (P : Ambient q →L[ℝ] Ambient q) (hP : star P * P = 1)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (dp z : Gradient n m) (v : Gradient n q) (a : Ambient q)
    (d : Fin n → ℝ) (lap : ℝ) {B K : ℝ}
    (hB : 0 ≤ B) (hb : ∀ i, |d i| ≤ B) (hLap : |lap| ≤ K) :
    ‖(∑ i : Fin n, d i • star (R (dp i)) a) +
      (2 : ℝ) • (∑ i : Fin n, d i • star P (v i)) + lap • star P a +
      ∑ i : Fin n, d i • R (z i) (star P a)‖ ≤
    B * Real.sqrt (n : ℝ) *
      (‖R‖ * Real.sqrt (hsNormSq dp) * ‖a‖ +
        2 * Real.sqrt (hsNormSq v) + ‖R‖ * Real.sqrt (hsNormSq z) * ‖a‖) + K * ‖a‖ := by
  have hR : 0 ≤ ‖R‖ := norm_nonneg R
  have hK : 0 ≤ K := (abs_nonneg lap).trans hLap
  have hstarNorm (T : Ambient q →L[ℝ] Ambient q) : ‖star T‖ = ‖T‖ :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).norm_map T
  have hfirst := norm_sum_smul_apply_le_hs d (fun i => star (R (dp i))) dp a hB hR hb
    (fun i => (hstarNorm (R (dp i))).le.trans (R.le_opNorm _))
  have hPsum : (∑ i : Fin n, ‖star P (v i)‖) ≤ ∑ i : Fin n, ‖v i‖ :=
    Finset.sum_le_sum (fun i _ => norm_star_apply_orthogonal_le P hP (v i))
  have hsum : ‖∑ i : Fin n, d i • star P (v i)‖ ≤
      B * Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq v) := by
    calc
      _ ≤ B * ∑ i : Fin n, ‖star P (v i)‖ := norm_sum_smul_le_sum_column_norm d _ hb
      _ ≤ B * ∑ i : Fin n, ‖v i‖ := mul_le_mul_of_nonneg_left hPsum hB
      _ ≤ B * (Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq v)) :=
        mul_le_mul_of_nonneg_left (sum_column_norm_le_sqrt_dimension_mul_hs v) hB
      _ = _ := (mul_assoc _ _ _).symm
  have hsecond : ‖(2 : ℝ) • (∑ i : Fin n, d i • star P (v i))‖ ≤
      2 * (B * Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq v)) := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hthird : ‖lap • star P a‖ ≤ K * ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hLap (norm_star_apply_orthogonal_le P hP a) (norm_nonneg _) hK
  have hfourth : ‖∑ i : Fin n, d i • R (z i) (star P a)‖ ≤
      B * ‖R‖ * Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq z) * ‖a‖ :=
    (norm_sum_smul_apply_le_hs d (fun i => R (z i)) z (star P a) hB hR hb
      (fun i => R.le_opNorm _)).trans
        (mul_le_mul_of_nonneg_left (norm_star_apply_orthogonal_le P hP a) (by positivity))
  calc
    _ ≤ ‖(∑ i : Fin n, d i • star (R (dp i)) a) +
          (2 : ℝ) • (∑ i : Fin n, d i • star P (v i)) + lap • star P a‖ +
        ‖∑ i : Fin n, d i • R (z i) (star P a)‖ := norm_add_le _ _
    _ ≤ (‖(∑ i : Fin n, d i • star (R (dp i)) a) +
          (2 : ℝ) • (∑ i : Fin n, d i • star P (v i))‖ + ‖lap • star P a‖) +
        ‖∑ i : Fin n, d i • R (z i) (star P a)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖∑ i : Fin n, d i • star (R (dp i)) a‖ +
          ‖(2 : ℝ) • (∑ i : Fin n, d i • star P (v i))‖) + ‖lap • star P a‖) +
        ‖∑ i : Fin n, d i • R (z i) (star P a)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ (B * ‖R‖ * Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq dp) * ‖a‖ +
          2 * (B * Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq v)) + K * ‖a‖) +
        B * ‖R‖ * Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq z) * ‖a‖ :=
      add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
    _ = _ := by ring

end StationaryHarmonicMaps.Analysis

end
