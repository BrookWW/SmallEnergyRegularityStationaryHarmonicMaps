module

public import StationaryHarmonicMaps.Geometry.ProjectionCommutator
public import HarmonicMaps.Sobolev
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Algebra of orthogonal frame fluxes -/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps

/-- In finite dimension one orthogonality identity gives the other one. -/
theorem mul_star_eq_one_of_star_mul_eq_one {q : ℕ}
    (P : Ambient q →L[ℝ] Ambient q) (hP : star P * P = 1) : P * star P = 1 := by
  have h : (star P).toLinearMap * P.toLinearMap = 1 :=
    congrArg ContinuousLinearMap.toLinearMap hP
  have h' := mul_eq_one_symm h
  exact ContinuousLinearMap.coe_injective h'

/-- Differentiated orthogonality determines the derivative of the inverse frame. -/
theorem star_derivative_of_orthogonal_constraint {A : Type*} [Ring A] [StarRing A]
    (P D : A) (hP : P * star P = 1)
    (hD : star D * P + star P * D = 0) :
    star D = -(star P * D * star P) := by
  have h := congrArg (fun T : A => T * star P) hD
  rw [add_mul, mul_assoc (star D) P (star P), hP, mul_one, zero_mul] at h
  exact eq_neg_iff_add_eq_zero.mpr h

/-- The transformed right side is minus the gauged potential applied to the actual flux. -/
theorem orthogonal_flux_forcing_identity {n q : ℕ}
    (P : Ambient q →L[ℝ] Ambient q)
    (D A : Fin n → Ambient q →L[ℝ] Ambient q) (v : Fin n → Ambient q)
    (hP : P * star P = 1)
    (hD : ∀ i, star (D i) * P + star P * D i = 0) :
    star P (-(∑ i : Fin n, A i (v i))) + ∑ i : Fin n, star (D i) (v i) =
      -(∑ i : Fin n, (star P * D i + star P * A i * P) (star P (v i))) := by
  have hPinv (w : Ambient q) : P (star P w) = w :=
    congrArg (fun T : Ambient q →L[ℝ] Ambient q => T w) hP
  have hDi (i : Fin n) : star (D i) = -(star P * D i * star P) :=
    star_derivative_of_orthogonal_constraint P (D i) hP (hD i)
  simp only [map_neg, map_sum, hDi, neg_apply, mul_apply_eq_comp, add_apply, hPinv,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  congr 1
  funext i
  abel

end StationaryHarmonicMaps

end
