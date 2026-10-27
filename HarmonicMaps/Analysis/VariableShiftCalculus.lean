module

public import HarmonicMaps.Analysis.VariableShiftBasic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Differential of a variable translation

The differential of `x ↦ x - s x • y` is the identity minus a rank-one map.
Its matrix in the standard Euclidean basis has determinant `1 - Ds x y`.
-/

public section

open scoped ContDiff

namespace HarmonicMaps

variable {n : ℕ} {s : Domain n → ℝ} {x : Domain n}

/-- A smooth radius gives a globally smooth variable translation. -/
theorem contDiff_variableShift (hs : ContDiff ℝ ∞ s) (y : Domain n) :
    ContDiff ℝ ∞ (variableShift s y) :=
  contDiff_id.sub (hs.smul_const y)

/-- The actual differential of the variable translation. -/
theorem hasFDerivAt_variableShift (hs : DifferentiableAt ℝ s x) (y : Domain n) :
    HasFDerivAt (variableShift s y)
      (ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y) x :=
  (hasFDerivAt_id x).sub (hs.hasFDerivAt.smul_const y)

theorem fderiv_variableShift (hs : DifferentiableAt ℝ s x) (y : Domain n) :
    fderiv ℝ (variableShift s y) x =
      ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y :=
  (hasFDerivAt_variableShift hs y).fderiv

/-- Evaluation of a scalar linear map in the standard Euclidean basis. -/
theorem scalarLinearMap_eq_sum_coordinates (a : Domain n →L[ℝ] ℝ) (y : Domain n) :
    a y = ∑ j : Fin n, a (EuclideanSpace.single j 1) * y j := by
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The rank-one determinant formula for the standard Euclidean matrix. -/
theorem det_id_sub_smulRight (a : Domain n →L[ℝ] ℝ) (y : Domain n) :
    Matrix.det (fun i j : Fin n =>
      ((ContinuousLinearMap.id ℝ (Domain n) - a.smulRight y)
        (EuclideanSpace.single j 1)) i) = 1 - a y := by
  classical
  have hmatrix : (fun i j : Fin n =>
      ((ContinuousLinearMap.id ℝ (Domain n) - a.smulRight y)
        (EuclideanSpace.single j 1)) i) =
      (1 : Matrix (Fin n) (Fin n) ℝ) +
        Matrix.replicateCol Unit (fun i => -y i) *
        Matrix.replicateRow Unit (fun j => a (EuclideanSpace.single j 1)) := by
    ext i j
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.sub_apply, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
      Finset.univ_unique, Finset.sum_singleton]
    split_ifs <;> ring
  rw [hmatrix, Matrix.det_one_add_replicateCol_mul_replicateRow]
  rw [scalarLinearMap_eq_sum_coordinates]
  simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The Jacobian determinant uses the derivative in the standard Euclidean basis. -/
theorem det_fderiv_variableShift (hs : DifferentiableAt ℝ s x) (y : Domain n) :
    Matrix.det (fun i j : Fin n =>
      (fderiv ℝ (variableShift s y) x (EuclideanSpace.single j 1)) i) =
      1 - fderiv ℝ s x y := by
  rw [fderiv_variableShift hs y]
  exact det_id_sub_smulRight (fderiv ℝ s x) y

/-- The derivative norm bound associated with the source Lipschitz constant. -/
theorem norm_fderiv_variableShift_le {L : ℝ} (hs : DifferentiableAt ℝ s x)
    (hDs : ∀ z, ‖fderiv ℝ s z‖ ≤ L) (y : Domain n)
    (hy : y ∈ Metric.ball 0 1) :
    ‖fderiv ℝ (variableShift s y) x‖ ≤ 1 + L := by
  have hyNorm : ‖y‖ ≤ 1 := le_of_lt
    (by simpa only [Metric.mem_ball, dist_zero_right] using hy)
  have hRank : ‖(fderiv ℝ s x).smulRight y‖ ≤ L := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      ‖fderiv ℝ s x‖ * ‖y‖ ≤ ‖fderiv ℝ s x‖ * 1 :=
        mul_le_mul_of_nonneg_left hyNorm (norm_nonneg _)
      _ = ‖fderiv ℝ s x‖ := mul_one _
      _ ≤ L := hDs x
  rw [fderiv_variableShift hs y]
  exact (norm_sub_le _ _).trans
    (add_le_add ContinuousLinearMap.norm_id_le hRank)

/-- The Jacobian is bounded below by `1 - L` on the unit directions. -/
theorem variableShift_det_lower_bound {L : ℝ} (hs : DifferentiableAt ℝ s x)
    (hDs : ∀ z, ‖fderiv ℝ s z‖ ≤ L) (y : Domain n)
    (hy : y ∈ Metric.ball 0 1) :
    1 - L ≤ Matrix.det (fun i j : Fin n =>
      (fderiv ℝ (variableShift s y) x (EuclideanSpace.single j 1)) i) := by
  have hyNorm : ‖y‖ ≤ 1 := le_of_lt
    (by simpa only [Metric.mem_ball, dist_zero_right] using hy)
  have hScalar : fderiv ℝ s x y ≤ L := by
    calc
      fderiv ℝ s x y ≤ |fderiv ℝ s x y| := le_abs_self _
      _ = ‖fderiv ℝ s x y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ s x‖ := (fderiv ℝ s x).unit_le_opNorm y hyNorm
      _ ≤ L := hDs x
  rw [det_fderiv_variableShift hs y]
  exact sub_le_sub_left hScalar 1

/-- The source bound `L ≤ 1/4` makes the Jacobian strictly positive. -/
theorem variableShift_det_pos {L : ℝ} (hs : DifferentiableAt ℝ s x)
    (hDs : ∀ z, ‖fderiv ℝ s z‖ ≤ L) (hL : L ≤ 1 / 4) (y : Domain n)
    (hy : y ∈ Metric.ball 0 1) :
    0 < Matrix.det (fun i j : Fin n =>
      (fderiv ℝ (variableShift s y) x (EuclideanSpace.single j 1)) i) := by
  have hPositive : 0 < 1 - L := by linarith only [hL]
  exact hPositive.trans_le (variableShift_det_lower_bound hs hDs y hy)

end HarmonicMaps
