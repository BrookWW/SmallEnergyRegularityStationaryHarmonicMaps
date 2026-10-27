module

public import StationaryHarmonicMaps.Frozen.NormalProjectionCharacterization
public import StationaryHarmonicMaps.Geometry.C2NormalProjection

/-!
# Characterization and regularity of the normal projection

The source characterization gives the full orthogonal decomposition and
uniqueness among all ambient continuous linear operators. The algebraic and
regularity APIs use this characterization on the actual target carrier.
-/

public section

open scoped Manifold ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

/-- The complete characterization identifies the operator with the standard projection. -/
theorem normalProjection_eq_starProjection {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) : N.normalProjection p = (N.tangentImage p)ᗮ.starProjection := by
  apply Eq.symm
  apply ((N.normalProjection_characterization p).2 _).mp
  intro v
  refine ⟨Submodule.starProjection_apply_mem _ v, ?_⟩
  simpa only [Submodule.orthogonal_orthogonal] using
    (Submodule.sub_starProjection_mem_orthogonal (K := (N.tangentImage p)ᗮ) v)

/-- The normal component belongs to the genuine normal subspace. -/
theorem normalProjection_apply_mem {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) (v : EuclideanSpace ℝ (Fin q)) :
    N.normalProjection p v ∈ (N.tangentImage p)ᗮ :=
  ((N.normalProjection_characterization p).1 v).1

/-- The residual component belongs to the genuine tangent subspace. -/
theorem sub_normalProjection_apply_mem {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) (v : EuclideanSpace ℝ (Fin q)) :
    v - N.normalProjection p v ∈ N.tangentImage p :=
  ((N.normalProjection_characterization p).1 v).2

/-- The source normal projection is self-adjoint. -/
theorem normalProjection_isSelfAdjoint {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) : IsSelfAdjoint (N.normalProjection p) := by
  rw [N.normalProjection_eq_starProjection p]
  exact isSelfAdjoint_starProjection _

/-- The source normal projection is idempotent. -/
theorem normalProjection_idempotent {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) : N.normalProjection p * N.normalProjection p =
      N.normalProjection p := by
  rw [N.normalProjection_eq_starProjection p]
  exact Submodule.isIdempotentElem_starProjection _

/-- The source normal projection has operator norm at most one. -/
theorem normalProjection_norm_le_one {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) : ‖N.normalProjection p‖ ≤ 1 := by
  rw [N.normalProjection_eq_starProjection p]
  exact Submodule.starProjection_norm_le _

/-- The kernel is exactly the ambient tangent subspace. -/
@[simp] theorem normalProjection_apply_eq_zero_iff {q : ℕ}
    (N : CompactC2EmbeddedTarget q) (p : N.Carrier) (v : EuclideanSpace ℝ (Fin q)) :
    N.normalProjection p v = 0 ↔ v ∈ N.tangentImage p := by
  rw [N.normalProjection_eq_starProjection p,
    Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]

/-- Actual C² target geometry gives C¹ regularity of the source projection field. -/
theorem normalProjection_contMDiff {q : ℕ} (N : CompactC2EmbeddedTarget q) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
      𝓘(ℝ, EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q)) 1
      N.normalProjection := by
  have hEq : N.normalProjection =
      fun p : N.Carrier => (N.tangentImage p)ᗮ.starProjection :=
    funext (fun p => N.normalProjection_eq_starProjection p)
  rw [hEq]
  exact N.normal_projection_contMDiff

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end
