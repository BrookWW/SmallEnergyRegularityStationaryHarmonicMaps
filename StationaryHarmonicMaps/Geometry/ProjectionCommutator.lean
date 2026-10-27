module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The commutator of a projection and its derivative

The algebraic identities below apply to a normal projection and a directional
derivative of its field. Self-adjointness and the differentiated idempotence
identity are hypotheses of these algebraic results. They do not assert that an
arbitrary operator field is a differentiable projection field.

All norms of continuous linear operators in this file are operator norms.
-/

public section

namespace StationaryHarmonicMaps

/-- The commutator of two self-adjoint elements is skew-adjoint. -/
theorem selfAdjoint_commutator_mem_skewAdjoint {A : Type*}
    [Ring A] [StarRing A] (Q D : A)
    (hQ : IsSelfAdjoint Q) (hD : IsSelfAdjoint D) :
    Q * D - D * Q ∈ skewAdjoint A := by
  rw [skewAdjoint.mem_iff, star_sub, star_mul, star_mul,
    hQ.star_eq, hD.star_eq, neg_sub]

/-- The normed-ring bound for a commutator uses only submultiplicativity. -/
theorem norm_commutator_le_two_mul {A : Type*} [NormedRing A] (Q D : A) :
    ‖Q * D - D * Q‖ ≤ 2 * ‖Q‖ * ‖D‖ := by
  calc
    ‖Q * D - D * Q‖ ≤ ‖Q * D‖ + ‖D * Q‖ := norm_sub_le _ _
    _ ≤ ‖Q‖ * ‖D‖ + ‖D‖ * ‖Q‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖Q‖ * ‖D‖ := by ring

section RealHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The operator appearing in the global normal-projection formulation. -/
@[expose] def projectionCommutator (Q D : E →L[ℝ] E) : E →L[ℝ] E :=
  Q * D - D * Q

/-- The commutator acts by the literal difference of the two compositions. -/
theorem projectionCommutator_apply (Q D : E →L[ℝ] E) (v : E) :
    projectionCommutator Q D v = Q (D v) - D (Q v) := rfl

/-- Self-adjointness supplies the skew-adjoint operator property. -/
theorem projectionCommutator_mem_skewAdjoint [CompleteSpace E] (Q D : E →L[ℝ] E)
    (hQ : IsSelfAdjoint Q) (hD : IsSelfAdjoint D) :
    projectionCommutator Q D ∈ skewAdjoint (E →L[ℝ] E) :=
  selfAdjoint_commutator_mem_skewAdjoint Q D hQ hD

/-- Differentiated idempotence maps vectors in the kernel into the range. -/
theorem projection_derivative_apply_of_kernel (Q D : E →L[ℝ] E)
    (hderivative : D * Q + Q * D = D) (v : E) (hQv : Q v = 0) :
    Q (D v) = D v := by
  have happly := congrArg (fun T : E →L[ℝ] E => T v) hderivative
  simpa only [add_apply, mul_apply_eq_comp,
    hQv, map_zero, zero_add] using happly

/-- On a vector annihilated by the projection, the commutator equals its derivative. -/
theorem projectionCommutator_apply_of_kernel (Q D : E →L[ℝ] E)
    (hderivative : D * Q + Q * D = D) (v : E) (hQv : Q v = 0) :
    projectionCommutator Q D v = D v := by
  have hQD := projection_derivative_apply_of_kernel Q D hderivative v hQv
  simpa only [projectionCommutator, sub_apply,
    mul_apply_eq_comp, hQv, map_zero, sub_zero] using hQD

/-- The bound is for the continuous-linear-map operator norm. -/
theorem norm_projectionCommutator_le (Q D : E →L[ℝ] E) :
    ‖projectionCommutator Q D‖ ≤ 2 * ‖Q‖ * ‖D‖ :=
  norm_commutator_le_two_mul Q D

/-- A skew-adjoint real operator has zero quadratic form. -/
theorem inner_apply_eq_zero_of_skewAdjoint [CompleteSpace E] (T : E →L[ℝ] E)
    (hT : T ∈ skewAdjoint (E →L[ℝ] E)) (v : E) :
    inner ℝ v (T v) = 0 := by
  have hstar : star T = -T := skewAdjoint.mem_iff.mp hT
  have hinner : inner ℝ v ((star T) v) = inner ℝ (T v) v :=
    ContinuousLinearMap.adjoint_inner_right T v v
  rw [hstar] at hinner
  simp only [neg_apply, inner_neg_right] at hinner
  rw [real_inner_comm v (T v)] at hinner
  linarith only [hinner]

/-- The antisymmetric potential is pointwise orthogonal to its input vector. -/
theorem inner_projectionCommutator_apply_eq_zero [CompleteSpace E] (Q D : E →L[ℝ] E)
    (hQ : IsSelfAdjoint Q) (hD : IsSelfAdjoint D) (v : E) :
    inner ℝ v (projectionCommutator Q D v) = 0 :=
  inner_apply_eq_zero_of_skewAdjoint _
    (projectionCommutator_mem_skewAdjoint Q D hQ hD) v

end RealHilbert

end StationaryHarmonicMaps

end
