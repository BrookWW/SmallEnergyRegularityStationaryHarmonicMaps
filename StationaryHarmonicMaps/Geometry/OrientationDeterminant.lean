module

public import StationaryHarmonicMaps.Analysis.SobolevOrthogonalFrame
public import StationaryHarmonicMaps.Analysis.ZeroEnergyRepresentative
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinants of actual orthogonal operators

The determinant is the finite polynomial in the real operator entries.
It is smooth, unchanged by the real adjoint, and equals one or minus one
for an orthogonal operator.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps

/-- The actual determinant is smooth on the complete operator carrier, including dimension zero. -/
theorem contDiff_operator_det (q : ℕ) :
    ContDiff ℝ ∞ (fun T : Ambient q →L[ℝ] Ambient q => T.det) := by
  let b := (EuclideanSpace.basisFun (Fin q) ℝ).toBasis
  have hdet (T : Ambient q →L[ℝ] Ambient q) : T.det =
      (LinearMap.toMatrix b b T.toLinearMap).det :=
    (LinearMap.det_toMatrix b T.toLinearMap).symm
  have hc (i j : Fin q) : ContDiff ℝ ∞ (fun T : Ambient q →L[ℝ] Ambient q =>
      LinearMap.toMatrix b b T.toLinearMap i j) := by
    have H : ContDiff ℝ ∞ (fun T : Ambient q →L[ℝ] Ambient q =>
        (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) i) (T (EuclideanSpace.single j 1))) :=
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) i).contDiff.comp
        (contDiff_id.clm_apply contDiff_const)
    simpa only [LinearMap.toMatrix_apply, b, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, ContinuousLinearMap.coe_coe, PiLp.proj_apply] using H
  simp_rw [hdet, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  exact contDiff_const.mul (contDiff_prod fun j _ => hc (σ j) j)

/-- The real adjoint leaves the actual finite-dimensional determinant unchanged. -/
theorem operator_det_star {q : ℕ} (P : Ambient q →L[ℝ] Ambient q) :
    (star P).det = P.det := by
  let b := EuclideanSpace.basisFun (Fin q) ℝ
  change LinearMap.det (ContinuousLinearMap.adjoint P).toLinearMap = LinearMap.det P.toLinearMap
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
    ← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.toMatrix_adjoint b b,
    Matrix.det_conjTranspose, star_trivial]

/-- Every actual orthogonal operator has determinant one or minus one. -/
theorem operator_det_eq_one_or_neg_one {q : ℕ} (P : Ambient q →L[ℝ] Ambient q)
    (hP : star P * P = 1) : P.det = 1 ∨ P.det = -1 := by
  have H := congrArg (fun T : Ambient q →L[ℝ] Ambient q => T.det) hP
  change LinearMap.det ((star P).toLinearMap * P.toLinearMap) = LinearMap.det 1 at H
  rw [map_mul, map_one] at H
  change (star P).det * P.det = 1 at H
  rw [operator_det_star] at H
  have hz : (P.det - 1) * (P.det + 1) = 0 := by nlinarith only [H]
  rcases mul_eq_zero.mp hz with hz | hz
  · left; linarith only [hz]
  · right; linarith only [hz]


end StationaryHarmonicMaps

end
