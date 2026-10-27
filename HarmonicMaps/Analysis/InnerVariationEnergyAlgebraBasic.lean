module

public import HarmonicMaps.Analysis.InnerVariationGeometry
public import HarmonicMaps.Energy
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Differential algebra for inner-variation energy

The actual operator perturbation is invertible throughout its norm-small
parameter interval. The inverse and determinant have their exact first
variations at zero. No inverse operator is defined by the project.
-/

public section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace HarmonicMaps

/-- A norm-small perturbation of the identity is an actual unit. -/
theorem innerVariation_operator_isUnit {n : ℕ} (B : Domain n →L[ℝ] Domain n)
    {t : ℝ} (ht : |t| * ‖B‖ < 1) : IsUnit (1 + t • B) := by
  have hb : ‖-(t • B)‖ < 1 := by simpa only [norm_neg, norm_smul, Real.norm_eq_abs] using ht
  rw [← sub_neg_eq_add]
  exact isUnit_one_sub_of_norm_lt_one hb

/-- On the small parameter interval, Mathlib's ring inverse satisfies both
actual operator inverse equations. -/
theorem innerVariation_operator_inverse_equations {n : ℕ}
    (B : Domain n →L[ℝ] Domain n) {t : ℝ} (ht : |t| * ‖B‖ < 1) :
    (1 + t • B) * Ring.inverse (1 + t • B) = 1 ∧
      Ring.inverse (1 + t • B) * (1 + t • B) = 1 :=
  ⟨Ring.mul_inverse_cancel _ (innerVariation_operator_isUnit B ht),
    Ring.inverse_mul_cancel _ (innerVariation_operator_isUnit B ht)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the actual operator perturbation has derivative `-B` at zero. -/
theorem innerVariation_operator_inverse_hasDerivAt {n : ℕ}
    (B : Domain n →L[ℝ] Domain n) :
    HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • B)) (-B) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => (1 : Domain n →L[ℝ] Domain n) + t • B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add 1
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Domain n →L[ℝ] Domain n)ˣ)
  have hzero : ((1 : Domain n →L[ℝ] Domain n) + (0 : ℝ) • B) =
      ↑(1 : (Domain n →L[ℝ] Domain n)ˣ) := by
    ext x i
    simp
  rw [← hzero] at hi
  have hc := hi.comp_hasDerivAt (0 : ℝ) hlin
  simpa only [Units.val_one, inv_one, Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, one_mul, mul_one] using hc

/-- The first derivative of the matrix determinant at the identity is its trace. -/
theorem innerVariation_matrix_det_hasDerivAt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.det (1 + t • M)) (Matrix.trace M) 0 := by
  let p := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)).divX.divX
  have hp := p.hasDerivAt (0 : ℝ)
  have ht := (hasDerivAt_id (0 : ℝ)).pow 2
  have hpoly := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul (Matrix.trace M))).add (hp.mul ht)
  have hform : (fun t : ℝ => 1 + Matrix.trace M * t + p.eval t * t ^ 2) =
      (fun t : ℝ => Matrix.det (1 + t • M)) := by
    funext t
    exact (Matrix.det_one_add_smul t M).symm
  change HasDerivAt (fun t : ℝ => 1 + Matrix.trace M * t + p.eval t * t ^ 2) _ 0 at hpoly
  rw [hform] at hpoly
  simpa using hpoly

/-- The actual operator determinant has the coordinate trace derivative. -/
theorem innerVariation_operator_det_hasDerivAt {n : ℕ}
    (B : Domain n →L[ℝ] Domain n) :
    HasDerivAt (fun t : ℝ => (1 + t • B).det)
      (∑ i : Fin n, (B (EuclideanSpace.single i 1)) i) 0 := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let M := LinearMap.toMatrix b b B.toLinearMap
  have hm := innerVariation_matrix_det_hasDerivAt M
  have heq (t : ℝ) : (1 + t • B).det = Matrix.det (1 + t • M) := by
    change LinearMap.det ((1 + t • B).toLinearMap) = _
    rw [← LinearMap.det_toMatrix b]
    congr 1
    change LinearMap.toMatrix b b (1 + t • B.toLinearMap) = _
    simp only [map_add, map_smul, LinearMap.toMatrix_one, M]
  have htrace : Matrix.trace M = ∑ i : Fin n, (B (EuclideanSpace.single i 1)) i := by
    simp only [Matrix.trace, Matrix.diag, M, LinearMap.toMatrix_apply, b,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    rfl
  simpa only [← heq, htrace] using hm

/-- The absolute Jacobian has the same derivative because its value at zero is one. -/
theorem innerVariation_operator_abs_det_hasDerivAt {n : ℕ}
    (B : Domain n →L[ℝ] Domain n) :
    HasDerivAt (fun t : ℝ => |(1 + t • B).det|)
      (∑ i : Fin n, (B (EuclideanSpace.single i 1)) i) 0 := by
  have h := (innerVariation_operator_det_hasDerivAt B).hasFDerivAt.abs_of_pos
    (by simp [ContinuousLinearMap.det] : 0 < ((1 : Domain n →L[ℝ] Domain n) + (0 : ℝ) • B).det)
  simpa using h.hasDerivAt

end HarmonicMaps
