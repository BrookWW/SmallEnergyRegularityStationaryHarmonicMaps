module

public import StationaryHarmonicMaps.Analysis.SkewMorreyCommutator
public import StationaryHarmonicMaps.Analysis.OperatorHSCoefficientBounds
public import HolderToCK.Analysis.GradientLinearAlgebra
public import StationaryHarmonicMaps.Geometry.SkewLogarithmicAlternation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit norms of the full matrix coefficient maps

The genuine Hilbert--Schmidt coefficient identity bounds the decoder by one
and the encoder by the ambient dimension plus one. These bounds control the
literal transported matrix commutator in every finite dimension.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

/-- Decoding full Hilbert--Schmidt coordinates does not increase the norm. -/
theorem operator_decoder_norm_le_one (q : ℕ)
    (e : Ambient (q*q) ≃L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖e.symm T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) :
    ‖e.toContinuousLinearMap‖ ≤ 1 := by
  apply e.toContinuousLinearMap.opNorm_le_bound (by norm_num)
  intro z
  calc
    ‖e z‖ ≤ Real.sqrt (hsNormSq (fun j => e z (EuclideanSpace.single j 1))) :=
      HolderToCK.norm_linearMap_le_sqrt_hsNormSq (e z)
    _ = ‖z‖ := by
      rw [hsNormSq, ← hE (e z), e.symm_apply_apply, Real.sqrt_sq (norm_nonneg z)]
    _ = 1 * ‖z‖ := (one_mul _).symm

/-- Encoding operator coefficients has the explicit dimension bound `q + 1`. -/
theorem operator_encoder_norm_le_dim_add_one (q : ℕ)
    (e : Ambient (q*q) ≃L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖e.symm T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) :
    ‖e.symm.toContinuousLinearMap‖ ≤ (q : ℝ) + 1 := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hCoeff : (q : ℝ) ≤ ((q : ℝ) + 1) ^ 2 := by nlinarith
  apply e.symm.toContinuousLinearMap.opNorm_le_bound (by positivity)
  intro T
  have hSq : ‖e.symm T‖ ^ 2 ≤ (((q : ℝ) + 1) * ‖T‖) ^ 2 := by
    calc
      _ = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2 := hE T
      _ ≤ (q : ℝ) * ‖T‖ ^ 2 := operator_column_sq_sum_le_dim_mul_opNorm_sq T
      _ ≤ ((q : ℝ) + 1) ^ 2 * ‖T‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCoeff (sq_nonneg ‖T‖)
      _ = _ := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hSq

/-- The actual full-coordinate matrix commutator has a numerical operator bound. -/
theorem morreyMatrixCommutator_norm_le (q : ℕ)
    (e : Ambient (q*q) ≃L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖e.symm T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) :
    ‖morreyMatrixCommutator q e‖ ≤ 2 * ((q : ℝ) + 1) := by
  have hq : 0 ≤ (q : ℝ) + 1 := by positivity
  have hDecode (z : Ambient (q*q)) : ‖e z‖ ≤ ‖z‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, one_mul] using
      e.toContinuousLinearMap.le_of_opNorm_le (operator_decoder_norm_le_one q e hE) z
  have hEncode (T : Ambient q →L[ℝ] Ambient q) :
      ‖e.symm T‖ ≤ ((q : ℝ) + 1) * ‖T‖ :=
    e.symm.toContinuousLinearMap.le_of_opNorm_le (operator_encoder_norm_le_dim_add_one q e hE) T
  apply (morreyMatrixCommutator q e).opNorm_le_bound₂ (by positivity)
  intro z w
  rw [morreyMatrixCommutator_apply]
  calc
    ‖e.symm (e z * e w - e w * e z)‖ ≤
        ((q : ℝ) + 1) * ‖e z * e w - e w * e z‖ := hEncode _
    _ ≤ ((q : ℝ) + 1) * (‖e z * e w‖ + ‖e w * e z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hq
    _ ≤ ((q : ℝ) + 1) * (‖e z‖ * ‖e w‖ + ‖e w‖ * ‖e z‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) hq
    _ ≤ ((q : ℝ) + 1) * (‖z‖ * ‖w‖ + ‖w‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul (hDecode z) (hDecode w) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (hDecode w) (hDecode z) (norm_nonneg _) (norm_nonneg _))) hq
    _ = 2 * ((q : ℝ) + 1) * ‖z‖ * ‖w‖ := by ring

/-- The actual alternating logarithmic product has a dimension-only norm bound
in every pair of inverse full Hilbert--Schmidt coordinate maps. -/
theorem skewLogarithmicAlternation_norm_le (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z)=z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) :
    ‖Geometry.skewLogarithmicAlternation E R‖ ≤ (q : ℝ)+1 := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hQ : 0 ≤ (q : ℝ)+1 := by positivity
  have hStar (T : Ambient q →L[ℝ] Ambient q) : ‖star T‖=‖T‖ := by
    change ‖ContinuousLinearMap.adjoint T‖=‖T‖
    exact ContinuousLinearMap.adjoint.norm_map T
  have hDecode (z : Ambient (q*q)) : ‖R z‖ ≤ ‖z‖ := by
    calc
      _ ≤ Real.sqrt (hsNormSq (fun j => R z (EuclideanSpace.single j 1))) :=
        HolderToCK.norm_linearMap_le_sqrt_hsNormSq (R z)
      _ = ‖z‖ := by
        rw [hsNormSq, ← hE (R z), hER z, Real.sqrt_sq (norm_nonneg z)]
  have hEncode (T : Ambient q →L[ℝ] Ambient q) :
      ‖E T‖ ≤ ((q : ℝ)+1)*‖T‖ := by
    have hCoeff : (q : ℝ) ≤ ((q : ℝ)+1)^2 := by nlinarith
    have hSq : ‖E T‖^2 ≤ (((q : ℝ)+1)*‖T‖)^2 := by
      calc
        _ = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖^2 := hE T
        _ ≤ (q : ℝ)*‖T‖^2 := operator_column_sq_sum_le_dim_mul_opNorm_sq T
        _ ≤ ((q : ℝ)+1)^2*‖T‖^2 :=
          mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _)
        _ = _ := (mul_pow _ _ _).symm
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hQ (norm_nonneg _))).mp hSq
  apply (Geometry.skewLogarithmicAlternation E R).opNorm_le_bound₂ hQ
  intro z w
  rw [Geometry.skewLogarithmicAlternation_apply]
  calc
    _ ≤ ((q : ℝ)+1)*‖(1/2 : ℝ) • (star (R z)*R w-star (R w)*R z)‖ := hEncode _
    _ = ((q : ℝ)+1)*((1/2 : ℝ)*‖star (R z)*R w-star (R w)*R z‖) := by
      rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤1/2)]
    _ ≤ ((q : ℝ)+1)*((1/2 : ℝ)*(‖star (R z)*R w‖+‖star (R w)*R z‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sub_le _ _)
        (by norm_num)) hQ
    _ ≤ ((q : ℝ)+1)*((1/2 : ℝ)*(‖R z‖*‖R w‖+‖R w‖*‖R z‖)) := by
      apply mul_le_mul_of_nonneg_left _ hQ
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [hStar] using add_le_add (norm_mul_le (star (R z)) (R w))
        (norm_mul_le (star (R w)) (R z))
    _ ≤ ((q : ℝ)+1)*((1/2 : ℝ)*(‖z‖*‖w‖+‖w‖*‖z‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul (hDecode z) (hDecode w) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (hDecode w) (hDecode z) (norm_nonneg _) (norm_nonneg _)))
        (by norm_num)) hQ
    _ = ((q : ℝ)+1)*‖z‖*‖w‖ := by ring

end StationaryHarmonicMaps.Analysis

end
