module

public import StationaryHarmonicMaps.Geometry.OrientationSign
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The actual determinant sign of a native orthogonal frame

The determinant is the finite polynomial in the real operator entries.
Its actual C1 composition with a bounded native Sobolev frame has a
constant sign by the two-point Sobolev argument.
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

/-- The determinant of the same actual native orthogonal frame has one constant orientation sign. -/
theorem exists_constant_operator_det_of_native_orthogonal {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
    (hp : MemW12 (ballDomain (0 : Domain n) 1) p Dp)
    (horth : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (p x)) * R (p x) = 1) :
    ∃ d : ℝ, (d = 1 ∨ d = -1) ∧
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), (R (p x)).det = d := by
  let e : Ambient 1 := EuclideanSpace.single (0 : Fin 1) 1
  let f : Ambient (q*q) → Ambient 1 := fun z => (R z).det • e
  have hf : ContDiff ℝ 1 f :=
    (((contDiff_operator_det q).comp R.contDiff).of_le (by simp)).smul contDiff_const
  have hs : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      f (p x) = EuclideanSpace.single (0 : Fin 1) 1 ∨
      f (p x) = -EuclideanSpace.single (0 : Fin 1) 1 := by
    filter_upwards [horth] with x hx
    rcases operator_det_eq_one_or_neg_one (R (p x)) hx with hd | hd
    · left; simp only [f, hd, one_smul, e]
    · right; simp only [f, hd, neg_one_smul, e]
  have hb := Analysis.ae_orthogonal_coordinates_bound (Ω := ballDomain (0 : Domain n) 1) E R hER hE p
    (by simpa only [ballDomain] using horth)
  obtain ⟨c, hc, hconst⟩ := Analysis.exists_constant_sign_of_c1_observable
    (0 : Domain n) (by norm_num) p Dp hp _ hb f hf hs
  refine ⟨c 0, ?_, ?_⟩
  · rcases hc with hc | hc
    · left; simp only [hc, PiLp.single_apply, ite_true]
    · right; simp only [hc, PiLp.neg_apply, PiLp.single_apply, ite_true]
  · filter_upwards [hconst] with x hx
    have H := congrArg (fun v : Ambient 1 => v (0 : Fin 1)) hx
    simpa only [Function.comp_apply, f, e, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, mul_one] using H

end StationaryHarmonicMaps

end
