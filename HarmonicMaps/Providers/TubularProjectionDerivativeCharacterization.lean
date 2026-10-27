module
public import HarmonicMaps.Geometry.TubularProjectionDerivative
public section
open scoped ContDiff
namespace HarmonicMaps.Providers.TubularProjectionDerivativeCharacterization

theorem result (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  (∀ (z : tubularTube q N) (V : Set (Ambient q)) (g : Ambient q → Ambient q),
    IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
    (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
    fderiv ℝ g z.val = tubularProjectionDerivative q N z) ∧
  (∀ z : tubularTube q N, ∃ V : Set (Ambient q),
    IsOpen V ∧ z.val ∈ V ∧ V ⊆ tubularTube q N ∧
    ∃ g : Ambient q → Ambient q,
      ContDiffOn ℝ ∞ g V ∧
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) ∧
      ContDiffOn ℝ ∞ (fderiv ℝ g) V ∧
      ∀ w : tubularTube q N, w.val ∈ V →
        fderiv ℝ g w.val = tubularProjectionDerivative q N w) ∧
  ∀ S : tubularTube q N → (Ambient q →L[ℝ] Ambient q),
    (∀ (z : tubularTube q N) (V : Set (Ambient q)) (g : Ambient q → Ambient q),
      IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
      fderiv ℝ g z.val = S z) → S = tubularProjectionDerivative q N :=
by
  have hField (z : tubularTube q N) := (Classical.choose_spec (tubularProjectionDerivativeWellDefined q N z)).1
  refine ⟨(fun z => hField z), ?_, ?_⟩
  · intro z
    obtain ⟨V, hV, hz, hVU, g, hg, hgP⟩ :=
      (tubularProjection_characterization q N).2.2.2.2.1 z
    have hJetSmooth : ContDiffOn ℝ ∞ (fderiv ℝ g) V :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen hV).1 hg).2
    refine ⟨V, hV, hz, hVU, g, hg, hgP, hJetSmooth, ?_⟩
    intro w hw
    exact hField w V g hV hw hVU hg hgP
  · intro S hS
    funext z
    exact (Classical.choose_spec (tubularProjectionDerivativeWellDefined q N z)).2 (S z) (hS z)

end HarmonicMaps.Providers.TubularProjectionDerivativeCharacterization
end
