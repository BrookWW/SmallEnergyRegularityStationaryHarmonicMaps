module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Gram formulas for orthogonal projections

An injective linear map between finite-dimensional real Hilbert spaces has an
invertible Gram operator. Its range projection and normal projection have the
usual Gram formulas. A differentiable family of injective maps therefore has a
differentiable family of actual orthogonal normal projections.
-/

public section

open scoped ContDiff

namespace StationaryHarmonicMaps.Geometry

variable {E F X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Injectivity of a finite-dimensional map makes its Gram operator invertible. -/
theorem gram_isInvertible_of_injective (A : E →L[ℝ] F)
    (hA : Function.Injective A) : (A.adjoint.comp A).IsInvertible := by
  have hG : Function.Injective (A.adjoint.comp A) :=
    A.adjoint_comp_self_injective_iff.mpr hA
  have hker : (A.adjoint.comp A).ker = ⊥ := LinearMap.ker_eq_bot.mpr hG
  have hrange : (A.adjoint.comp A).range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hG)
  exact ⟨ContinuousLinearEquiv.ofBijective (A.adjoint.comp A) hker hrange,
    ContinuousLinearEquiv.coe_ofBijective (A.adjoint.comp A) hker hrange⟩

/-- The orthogonal range projection equals the Gram formula at an injective map. -/
theorem range_starProjection_eq_gram (A : E →L[ℝ] F) (hA : Function.Injective A) :
    A.range.starProjection = A.comp ((A.adjoint.comp A).inverse.comp A.adjoint) := by
  apply ContinuousLinearMap.ext
  intro y
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨(A.adjoint.comp A).inverse (A.adjoint y), rfl⟩
  · rw [A.orthogonal_range, LinearMap.mem_ker]
    change A.adjoint (y - A ((A.adjoint.comp A).inverse (A.adjoint y))) = 0
    rw [map_sub]
    change A.adjoint y - (A.adjoint.comp A)
      ((A.adjoint.comp A).inverse (A.adjoint y)) = 0
    rw [(gram_isInvertible_of_injective A hA).self_apply_inverse, sub_self]

/-- The actual orthogonal normal projection equals the complementary Gram formula. -/
theorem normal_starProjection_eq_gram (A : E →L[ℝ] F) (hA : Function.Injective A) :
    A.rangeᗮ.starProjection = ContinuousLinearMap.id ℝ F -
      A.comp ((A.adjoint.comp A).inverse.comp A.adjoint) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [Submodule.starProjection_orthogonal_val, range_starProjection_eq_gram A hA]
  rfl

variable [NormedAddCommGroup X] [NormedSpace ℝ X]
  {m : ℕ∞ω} {U : Set X} {A : X → E →L[ℝ] F}

/-- Taking Gram operators preserves the regularity of a linear-map family. -/
theorem contDiffOn_gram (hA : ContDiffOn ℝ m A U) :
    ContDiffOn ℝ m (fun x => (A x).adjoint.comp (A x)) U := by
  have hAdj : ContDiffOn ℝ m (fun x => (A x).adjoint) U :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).contDiff.comp_contDiffOn hA
  exact hAdj.clm_comp hA

/-- Gram inverses have the same regularity on a family of injective maps. -/
theorem contDiffOn_gram_inverse_of_injective (hA : ContDiffOn ℝ m A U)
    (hinj : ∀ x ∈ U, Function.Injective (A x)) :
    ContDiffOn ℝ m (fun x => ((A x).adjoint.comp (A x)).inverse) U := by
  intro x hx
  exact (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
    (gram_isInvertible_of_injective (A x) (hinj x hx))).comp_contDiffWithinAt x
    (contDiffOn_gram hA x hx)

/-- Orthogonal normal projections vary with the regularity of an injective family. -/
theorem contDiffOn_normal_starProjection_of_injective (hA : ContDiffOn ℝ m A U)
    (hinj : ∀ x ∈ U, Function.Injective (A x)) :
    ContDiffOn ℝ m (fun x => (A x).rangeᗮ.starProjection) U := by
  have hAdj : ContDiffOn ℝ m (fun x => (A x).adjoint) U :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).contDiff.comp_contDiffOn hA
  have hInv := contDiffOn_gram_inverse_of_injective hA hinj
  have hFormula : ContDiffOn ℝ m (fun x => ContinuousLinearMap.id ℝ F -
      (A x).comp (((A x).adjoint.comp (A x)).inverse.comp (A x).adjoint)) U :=
    contDiffOn_const.sub (hA.clm_comp (hInv.clm_comp hAdj))
  exact hFormula.congr fun x hx => normal_starProjection_eq_gram (A x) (hinj x hx)

end StationaryHarmonicMaps.Geometry

end
