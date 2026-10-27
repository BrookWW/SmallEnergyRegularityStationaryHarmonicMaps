module

public import StationaryHarmonicMaps.Geometry.C2ProjectionLocalExtension
public import StationaryHarmonicMaps.Geometry.LocalExtensionGluing

/-!
# Compactly supported ambient extensions of the normal projection

Actual C² target charts produce local C¹ ambient extensions. Smooth
partition-of-unity gluing and a compact cutoff give a global C¹ extension
which agrees with the normal projection at every target point. Its derivative
has a uniform ambient operator bound. The extension is not canonical.
-/

public section

open scoped ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

/-- The actual normal projection of a compact C² target has a compact C¹ ambient extension. -/
theorem exists_global_ambient_normal_projection_extension {q : ℕ}
    (N : CompactC2EmbeddedTarget q) :
    ∃ G : EuclideanSpace ℝ (Fin q) →
      EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ∀ p : N.Carrier, G p.val = (N.tangentImage p)ᗮ.starProjection :=
  Geometry.exists_compactlySupported_contDiff_extension_of_local
    N.carrierSet N.isCompact (fun p : N.Carrier => (N.tangentImage p)ᗮ.starProjection)
    (fun p => N.exists_local_ambient_normal_projection_extension p)

/-- The extension admits one uniform bound for its actual ambient Fréchet derivative. -/
theorem exists_global_ambient_normal_projection_extension_bounded_derivative {q : ℕ}
    (N : CompactC2EmbeddedTarget q) :
    ∃ (G : EuclideanSpace ℝ (Fin q) →
        EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q)) (C : ℝ),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ p : N.Carrier, G p.val = (N.tangentImage p)ᗮ.starProjection) ∧
      0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin q), ‖fderiv ℝ G x‖ ≤ C :=
  Geometry.exists_compactlySupported_contDiff_extension_bounded_derivative
    N.carrierSet N.isCompact (fun p : N.Carrier => (N.tangentImage p)ᗮ.starProjection)
    (fun p => N.exists_local_ambient_normal_projection_extension p)

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end
