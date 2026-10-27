module

public import StationaryHarmonicMaps.Geometry.SmoothNormalExtension
public import StationaryHarmonicMaps.Analysis.VariationalWeakPoisson
public import HolderToCK.Frozen.HolderQuadraticPoissonSmooth

/-!
# The separate smooth-target Hölder bootstrap

For an actual smooth target, its smooth normal extension supplies the smooth
quadratic coefficient A(y)=-DG(y). The original map variation gives its signed
weak Poisson equation. A genuine local Hölder hypothesis then yields smoothness
of the same map. This statement adds no conclusion to the C² target theorem.
-/

public section

open HarmonicMaps MeasureTheory
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A locally Hölder weakly harmonic map into a smooth target is smooth on its original domain. -/
theorem smooth_of_locallyHolder_smooth_target {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (hweak : IsWeaklyHarmonicByTangentVariations (SmoothTarget.toC2 N) Ω u Du)
    (hHolder : HolderToCK.LocallyHolderOn Ω u) :
    ContDiffOn ℝ ∞ u Ω.val := by
  obtain ⟨G, L, hG, hcG, hGN, _hL, hDG⟩ :=
    SmoothTarget.exists_smooth_normal_projection_extension N
  have hNC2 : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ (SmoothTarget.toC2 N).carrierSet := by
    simpa only [SmoothTarget.toC2_carrierSet] using hN
  have hP := variational_weakPoissonOn (SmoothTarget.toC2 N) hu hNC2 hweak
    G (hG.of_le (by simp)) hcG hGN hDG
  let A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q :=
    fun y => -(fderiv ℝ G y)
  have hA : ContDiff ℝ ∞ A := (hG.fderiv_right (m := ∞) (by simp)).neg
  have hForcing : (fun x => -(∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i))) =
      (fun x => ∑ i : Fin n, A (u x) (Du x i) (Du x i)) := by
    funext x
    simp only [A, neg_apply, Finset.sum_neg_distrib]
  rw [hForcing] at hP
  exact HolderToCK.holderQuadraticPoisson_smooth n q hn Ω u Du A hA hu hHolder hP

end StationaryHarmonicMaps.Analysis

end
