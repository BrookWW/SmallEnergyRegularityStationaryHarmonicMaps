module

public import HarmonicMaps.Analysis.SmoothInverseSobolev
public import HarmonicMaps.Analysis.SobolevDifference
public import HarmonicMaps.Analysis.SobolevLocality
public import HarmonicMaps.Analysis.InnerVariationSupport
public import HarmonicMaps.SobolevRestriction

/-!
# Genuine Sobolev competitors for inner variations

The inverse-coordinate competitor has its actual transformed weak gradient,
almost-everywhere target values, and a zero boundary difference in the literal
Sobolev graph closure. All three conditions required by local minimality are
derived from the original map and smooth compact-support field.
-/

public section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace HarmonicMaps

/-- Inner variations produce genuine admissible competitors on a two-sided
interval, without a stationarity assumption or an assumed Sobolev chain rule. -/
theorem MemW12.innerVariation_admissible {n q : ℕ} {a : Domain n} {R : ℝ}
    (hR : 0 < R) {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) {N : CompactSmoothEmbeddedTarget q}
    (hN : TakesValuesIn N (ballDomain a R) u)
    {ζ : Domain n → Domain n} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Metric.ball a R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∃ g : Domain n → Domain n, ContDiff ℝ ∞ g ∧
        (∀ z, g z + t • ζ (g z) = z) ∧ (∀ x, g (x + t • ζ x) = x) ∧
        MemW12 (ballDomain a R) (u ∘ g)
          (fun x i => ∑ j : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1)) j • Du (g x) j) ∧
        TakesValuesIn N (ballDomain a R) (u ∘ g) ∧
        HasZeroBoundaryDifference (ballDomain a R) u Du (u ∘ g)
          (fun x i => ∑ j : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1)) j • Du (g x) j) := by
  obtain ⟨ε, hε, hgeom⟩ := innerVariation_diffeomorphism hζ hc hs
  refine ⟨ε, hε, ?_⟩
  intro t ht
  obtain ⟨hf, _, hinv, himage, _⟩ := hgeom t ht
  obtain ⟨g, hg, _⟩ := hinv
  have hfball : MapsTo (fun x => x + t • ζ x) (Metric.ball a R) (Metric.ball a R) := by
    intro x hx
    rw [← himage]
    exact mem_image_of_mem _ hx
  have hgball : MapsTo g (Metric.ball a R) (Metric.ball a R) := by
    intro z hz
    rw [← himage] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [hg.2.1 x]
    exact hx
  have hv := hu.comp_smooth_inverse_ball hR hf hg.2.2 hg.1 hg.2.1 hfball hgball
  have htarget := hN.comp_smooth_inverse hf hg.2.2 hg.1 hg.2.1 hgball
  have hdiff := hv.sub hu
  have hcomp := innerVariation_difference_hasCompactSupport hc hg.2.1 u
  have hsupp := (innerVariation_difference_tsupport_subset hg.2.1 u).trans hs
  exact ⟨g, hg.2.2, hg.1, hg.2.1, hv, htarget,
    hdiff.zeroBoundary_of_compactSupport_ball hR hcomp hsupp⟩

/-- Local minimality gives the actual competitor energy inequality for both
signs of the inner-variation parameter. Every admissibility field is derived. -/
theorem IsLocallyEnergyMinimizing.innerVariation_energy_minimum {n q : ℕ}
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val)
    {ζ : Domain n → Domain n} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Metric.ball a R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∃ g : Domain n → Domain n, ContDiff ℝ ∞ g ∧
        (∀ z, g z + t • ζ (g z) = z) ∧ (∀ x, g (x + t • ζ x) = x) ∧
        dirichletEnergy Du (Metric.ball a R) ≤
          dirichletEnergy
            (fun x i => ∑ j : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1)) j • Du (g x) j)
            (Metric.ball a R) := by
  have hw := hu.memW12_ball hball
  have ht : TakesValuesIn N (ballDomain a R) u :=
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hball) hN
  obtain ⟨ε, hε, hcomp⟩ := hw.innerVariation_admissible hR ht hζ hc hs
  refine ⟨ε, hε, ?_⟩
  intro t ht'
  obtain ⟨g, hg, hfg, hgf, hv, hNv, hzero⟩ := hcomp t ht'
  exact ⟨g, hg, hfg, hgf, hmin a R hR hball (u ∘ g) _ hv hNv hzero⟩

end HarmonicMaps
