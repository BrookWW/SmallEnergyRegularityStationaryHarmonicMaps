module

public import StationaryHarmonicMaps.Foundation.TangentImage
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

public section

namespace StationaryHarmonicMaps.Providers

/-- There is a unique operator giving the tangent-normal orthogonal decomposition. -/
theorem normalProjectionExistsUnique {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    ∃! P : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q),
      ∀ v : EuclideanSpace ℝ (Fin q),
        P v ∈ (N.tangentImage p)ᗮ ∧ v - P v ∈ N.tangentImage p := by
  refine ⟨(N.tangentImage p)ᗮ.starProjection, ?_, ?_⟩
  · intro v
    refine ⟨Submodule.starProjection_apply_mem _ v, ?_⟩
    simpa only [Submodule.orthogonal_orthogonal] using
      (Submodule.sub_starProjection_mem_orthogonal (K := (N.tangentImage p)ᗮ) v)
  · intro P hP
    apply ContinuousLinearMap.ext
    intro v
    apply Eq.symm
    apply Submodule.eq_starProjection_of_mem_orthogonal (hP v).1
    simpa only [Submodule.orthogonal_orthogonal] using (hP v).2

end StationaryHarmonicMaps.Providers

end
