module

public import StationaryHarmonicMaps.Foundation.NormalProjection

/-! # Orthogonal decomposition and uniqueness for the normal projection -/

public section

namespace StationaryHarmonicMaps.Providers

/-- The full source characterization of the actual orthogonal normal projection. -/
theorem normalProjectionCharacterization :
    ∀ {q : ℕ} (N : CompactC2EmbeddedTarget q) (p : N.Carrier),
    (∀ v : EuclideanSpace ℝ (Fin q),
      N.normalProjection p v ∈ (N.tangentImage p)ᗮ ∧
        v - N.normalProjection p v ∈ N.tangentImage p) ∧
    ∀ P : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q),
      (∀ v : EuclideanSpace ℝ (Fin q),
        P v ∈ (N.tangentImage p)ᗮ ∧ v - P v ∈ N.tangentImage p) ↔
        P = N.normalProjection p := by
  intro q N p
  have hspec : ∀ v : EuclideanSpace ℝ (Fin q),
      N.normalProjection p v ∈ (N.tangentImage p)ᗮ ∧
        v - N.normalProjection p v ∈ N.tangentImage p := by
    intro v
    refine ⟨Submodule.starProjection_apply_mem _ v, ?_⟩
    simpa only [CompactC2EmbeddedTarget.normalProjection, Submodule.orthogonal_orthogonal] using
      (Submodule.sub_starProjection_mem_orthogonal (K := (N.tangentImage p)ᗮ) v)
  refine ⟨hspec, ?_⟩
  intro P
  constructor
  · intro hP
    exact (N.normalProjection_existsUnique p).unique hP hspec
  · rintro rfl
    exact hspec

end StationaryHarmonicMaps.Providers

end
