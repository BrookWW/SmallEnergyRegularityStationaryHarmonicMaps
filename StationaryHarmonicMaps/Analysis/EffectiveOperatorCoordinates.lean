module

public import StationaryHarmonicMaps.Analysis.EffectiveMatrixCoefficientBounds

/-! Numerical norm bounds for the actual encoder and decoder maps. -/

public section
open HarmonicMaps
namespace StationaryHarmonicMaps.Analysis

/-- Decoding full Hilbert--Schmidt coordinates does not increase the norm. -/
theorem operator_coordinate_decoder_norm_le_one (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z,E (R z)=z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) :
    ‖R‖ ≤ 1 := by
  apply R.opNorm_le_bound (by norm_num)
  intro z
  calc
    ‖R z‖ ≤ Real.sqrt (hsNormSq (fun j => R z (EuclideanSpace.single j 1))) :=
      HolderToCK.norm_linearMap_le_sqrt_hsNormSq (R z)
    _ = ‖z‖ := by
      rw [hsNormSq, ← hE (R z), hER, Real.sqrt_sq (norm_nonneg z)]
    _ = 1 * ‖z‖ := (one_mul _).symm

/-- Encoding operator coefficients has the explicit dimension bound `q + 1`. -/
theorem operator_coordinate_encoder_norm_le_dim_add_one (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) :
    ‖E‖ ≤ (q : ℝ) + 1 := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hCoeff : (q : ℝ) ≤ ((q : ℝ) + 1) ^ 2 := by nlinarith
  apply E.opNorm_le_bound (by positivity)
  intro T
  have hSq : ‖E T‖ ^ 2 ≤ (((q : ℝ) + 1) * ‖T‖) ^ 2 := by
    calc
      _ = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2 := hE T
      _ ≤ (q : ℝ) * ‖T‖ ^ 2 := operator_column_sq_sum_le_dim_mul_opNorm_sq T
      _ ≤ ((q : ℝ) + 1) ^ 2 * ‖T‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCoeff (sq_nonneg ‖T‖)
      _ = _ := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hSq

end StationaryHarmonicMaps.Analysis
end
