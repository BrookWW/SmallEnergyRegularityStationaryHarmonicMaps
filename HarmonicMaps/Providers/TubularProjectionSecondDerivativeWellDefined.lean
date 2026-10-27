module
public import HarmonicMaps.Geometry.TubularProjectionCharacterization
public section
open scoped ContDiff
namespace HarmonicMaps.Providers.TubularProjectionSecondDerivativeWellDefined

theorem result (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
    (z : tubularTube q N) :
  ∃! H : Ambient q →L[ℝ] (Ambient q →L[ℝ] Ambient q),
    ∀ (V : Set (Ambient q)) (g : Ambient q → Ambient q),
      IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
      fderiv ℝ (fderiv ℝ g) z.val = H :=
by
  have hSpec := (tubularProjection_characterization q N).2
  obtain ⟨V₀, hV₀, hz₀, hVU₀, g₀, hg₀, hgP₀⟩ := hSpec.2.2.2.1 z
  refine ⟨fderiv ℝ (fderiv ℝ g₀) z.val, ?_, ?_⟩
  · intro V g hV hz hVU hg hgP
    exact (hSpec.2.2.2.2.1 z V V₀ g g₀ hV hV₀ hz hz₀ hVU hVU₀ hg hg₀ hgP hgP₀).2
  · intro H hH
    exact (hH V₀ g₀ hV₀ hz₀ hVU₀ hg₀ hgP₀).symm

end HarmonicMaps.Providers.TubularProjectionSecondDerivativeWellDefined
end
