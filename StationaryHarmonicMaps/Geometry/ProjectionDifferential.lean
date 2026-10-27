module

public import StationaryHarmonicMaps.Geometry.ProjectionCommutator
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Differentiating an orthogonal projection field

Directional derivatives of a differentiable field of self-adjoint projections
are self-adjoint and satisfy differentiated idempotence. The resulting
commutators act by the derivative on the kernel and by its negative on the
range. All projection-field assumptions are local to the differentiation point.
Norms of continuous linear maps are operator norms.
-/

public section

open Filter Topology

namespace StationaryHarmonicMaps.Geometry

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Q : X → E →L[ℝ] E} {dQ : X →L[ℝ] E →L[ℝ] E} {x : X}

/-- Differentiating local self-adjointness gives a self-adjoint directional derivative. -/
theorem projection_derivative_isSelfAdjoint
    (hQ : HasFDerivAt Q dQ x)
    (hself : ∀ᶠ y in 𝓝 x, IsSelfAdjoint (Q y)) (v : X) :
    IsSelfAdjoint (dQ v) := by
  have hEq : (fun y => star (Q y)) =ᶠ[𝓝 x] Q :=
    hself.mono fun _ hy => hy.star_eq
  have hderiv := hQ.star.unique (hQ.congr_of_eventuallyEq hEq)
  have hv := congrArg (fun L : X →L[ℝ] E →L[ℝ] E => L v) hderiv
  change star (dQ v) = dQ v
  exact hv

omit [CompleteSpace E] in
/-- Differentiating local idempotence gives the two mixed composition terms. -/
theorem projection_derivative_idempotence
    (hQ : HasFDerivAt Q dQ x)
    (hidem : ∀ᶠ y in 𝓝 x, Q y * Q y = Q y) (v : X) :
    dQ v * Q x + Q x * dQ v = dQ v := by
  have hEq : (fun y => (Q y).comp (Q y)) =ᶠ[𝓝 x] Q := hidem
  have hderiv := (hQ.clm_comp hQ).unique (hQ.congr_of_eventuallyEq hEq)
  have hv := congrArg (fun L : X →L[ℝ] E →L[ℝ] E => L v) hderiv
  change Q x * dQ v + dQ v * Q x = dQ v at hv
  rw [add_comm]
  exact hv

omit [CompleteSpace E] in
/-- A derivative of a projection sends a kernel vector into its range. -/
theorem projection_field_derivative_apply_of_kernel
    (hQ : HasFDerivAt Q dQ x)
    (hidem : ∀ᶠ y in 𝓝 x, Q y * Q y = Q y)
    (v : X) (w : E) (hw : Q x w = 0) :
    Q x (dQ v w) = dQ v w :=
  StationaryHarmonicMaps.projection_derivative_apply_of_kernel (Q x) (dQ v)
    (projection_derivative_idempotence hQ hidem v) w hw

omit [CompleteSpace E] in
/-- A derivative of a projection sends a range vector into its kernel. -/
theorem projection_field_derivative_apply_of_range
    (hQ : HasFDerivAt Q dQ x)
    (hidem : ∀ᶠ y in 𝓝 x, Q y * Q y = Q y)
    (v : X) (w : E) (hw : Q x w = w) :
    Q x (dQ v w) = 0 := by
  have happly := congrArg (fun T : E →L[ℝ] E => T w)
    (projection_derivative_idempotence hQ hidem v)
  have heq : dQ v w + Q x (dQ v w) = dQ v w := by
    simpa only [add_apply, mul_apply_eq_comp, hw] using happly
  exact add_left_cancel (heq.trans (add_zero (dQ v w)).symm)

/-- The commutator of a differentiable self-adjoint field and its derivative is skew. -/
theorem projection_field_commutator_mem_skewAdjoint
    (hQ : HasFDerivAt Q dQ x)
    (hself : ∀ᶠ y in 𝓝 x, IsSelfAdjoint (Q y)) (v : X) :
    projectionCommutator (Q x) (dQ v) ∈ skewAdjoint (E →L[ℝ] E) :=
  projectionCommutator_mem_skewAdjoint (Q x) (dQ v) hself.self_of_nhds
    (projection_derivative_isSelfAdjoint hQ hself v)

omit [CompleteSpace E] in
/-- On the kernel, the differential commutator equals the directional derivative. -/
theorem projection_field_commutator_apply_of_kernel
    (hQ : HasFDerivAt Q dQ x)
    (hidem : ∀ᶠ y in 𝓝 x, Q y * Q y = Q y)
    (v : X) (w : E) (hw : Q x w = 0) :
    projectionCommutator (Q x) (dQ v) w = dQ v w :=
  projectionCommutator_apply_of_kernel (Q x) (dQ v)
    (projection_derivative_idempotence hQ hidem v) w hw

omit [CompleteSpace E] in
/-- On the range, the differential commutator equals the negative derivative. -/
theorem projection_field_commutator_apply_of_range
    (hQ : HasFDerivAt Q dQ x)
    (hidem : ∀ᶠ y in 𝓝 x, Q y * Q y = Q y)
    (v : X) (w : E) (hw : Q x w = w) :
    projectionCommutator (Q x) (dQ v) w = -(dQ v w) := by
  have hnormal := projection_field_derivative_apply_of_range hQ hidem v w hw
  rw [projectionCommutator_apply, hnormal, hw, zero_sub]

/-- A self-adjoint projection gives a constant-two commutator bound. -/
theorem norm_projectionCommutator_le_of_projection (P D : E →L[ℝ] E)
    (hself : IsSelfAdjoint P) (hidem : P * P = P) :
    ‖projectionCommutator P D‖ ≤ 2 * ‖D‖ := by
  have hproj : IsStarProjection P := ⟨hidem, hself⟩
  calc
    ‖projectionCommutator P D‖ ≤ 2 * ‖P‖ * ‖D‖ :=
      norm_projectionCommutator_le P D
    _ ≤ 2 * 1 * ‖D‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (IsStarProjection.norm_le P hproj) (by norm_num))
        (norm_nonneg D)
    _ = 2 * ‖D‖ := by rw [mul_one]

/-- The differential commutator is bounded by the derivative operator norm. -/
theorem norm_projection_field_commutator_le
    (hself : ∀ᶠ y in 𝓝 x, IsSelfAdjoint (Q y))
    (hidem : ∀ᶠ y in 𝓝 x, Q y * Q y = Q y) (v : X) :
    ‖projectionCommutator (Q x) (dQ v)‖ ≤ 2 * ‖dQ‖ * ‖v‖ := by
  calc
    ‖projectionCommutator (Q x) (dQ v)‖ ≤ 2 * ‖dQ v‖ :=
      norm_projectionCommutator_le_of_projection (Q x) (dQ v)
        hself.self_of_nhds hidem.self_of_nhds
    _ ≤ 2 * (‖dQ‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (dQ.le_opNorm v) (by norm_num)
    _ = 2 * ‖dQ‖ * ‖v‖ := (mul_assoc _ _ _).symm

end StationaryHarmonicMaps.Geometry

end
