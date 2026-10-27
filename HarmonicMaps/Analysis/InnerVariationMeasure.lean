module

public import HarmonicMaps.Analysis.InnerVariationGeometry
public import HarmonicMaps.Minimizer
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Almost-everywhere properties under smooth inverse maps

A differentiable map sends Lebesgue null sets to null sets. Applying this
to the forward map proves that composition with its smooth inverse preserves
almost-everywhere target membership on any preserved ball.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

/-- An inverse with differentiable forward map preserves the Lebesgue null-set
class. Both inverse equations refer to the actual maps. -/
theorem quasiMeasurePreserving_of_differentiable_inverse {n : ℕ}
    {f g : Domain n → Domain n} (hf : Differentiable ℝ f) (hg : Continuous g)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f) :
    Measure.QuasiMeasurePreserving g volume volume := by
  refine ⟨hg.measurable, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs0
  rw [Measure.map_apply hg.measurable hs]
  have heq : g ⁻¹' s = f '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨g x, hx, hfg x⟩
    · rintro ⟨y, hy, rfl⟩
      exact show g (f y) ∈ s by rw [hgf y]; exact hy
  rw [heq]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hf.differentiableOn hs0

/-- Target membership is retained by the genuine inverse-coordinate
composition on a ball preserved by that inverse. -/
theorem TakesValuesIn.comp_smooth_inverse {n q : ℕ}
    {N : CompactSmoothEmbeddedTarget q} {a : Domain n} {R : ℝ}
    {u : Domain n → Ambient q} (hu : TakesValuesIn N (ballDomain a R) u)
    {f g : Domain n → Domain n} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f)
    (hball : MapsTo g (Metric.ball a R) (Metric.ball a R)) :
    TakesValuesIn N (ballDomain a R) (u ∘ g) :=
  ((quasiMeasurePreserving_of_differentiable_inverse (hf.differentiable (by simp))
    hg.continuous hfg hgf).restrict hball).ae hu

/-- The inner-variation inverse preserves a.e. target membership throughout
the same two-sided parameter interval as the proved smooth geometry. -/
theorem innerVariation_exists_target_preserving_inverse {n q : ℕ}
    {ζ : Domain n → Domain n} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    {a : Domain n} {R : ℝ} (hsupp : tsupport ζ ⊆ Metric.ball a R)
    {N : CompactSmoothEmbeddedTarget q} {u : Domain n → Ambient q}
    (hu : TakesValuesIn N (ballDomain a R) u) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∃ g : Domain n → Domain n, ContDiff ℝ ∞ g ∧
        (∀ z, g z + t • ζ (g z) = z) ∧ (∀ x, g (x + t • ζ x) = x) ∧
        TakesValuesIn N (ballDomain a R) (u ∘ g) := by
  obtain ⟨ε, hε, hgeom⟩ := innerVariation_diffeomorphism hζ hc hsupp
  refine ⟨ε, hε, ?_⟩
  intro t ht
  obtain ⟨hf, _, hinv, himage, _⟩ := hgeom t ht
  obtain ⟨g, hg, _⟩ := hinv
  have hball : MapsTo g (Metric.ball a R) (Metric.ball a R) := by
    intro z hz
    rw [← himage] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [hg.2.1 x]
    exact hx
  exact ⟨g, hg.2.2, hg.1, hg.2.1,
    hu.comp_smooth_inverse hf hg.2.2 hg.1 hg.2.1 hball⟩

end HarmonicMaps
