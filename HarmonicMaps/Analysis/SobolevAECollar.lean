module

public import HarmonicMaps.Analysis.SobolevAECongruence
public import HarmonicMaps.Analysis.SobolevCutoffBoundary
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Zero boundary values from almost-everywhere vanishing in a collar

A compact smooth cutoff leaves the original map unchanged almost everywhere
inside the ball. The genuine weak-gradient uniqueness theorem identifies its
product columns with the original columns. Its compact smooth graph-norm
approximation therefore converges to the original Sobolev data.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

/-- A Sobolev map vanishing almost everywhere in an outer ball collar has
zero boundary values for its original weak gradient. The inner radius may be zero. -/
theorem MemW12.zeroBoundary_of_ae_zero_collar_ball {n q : ℕ}
    {a : Domain n} {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : MemW12 (ballDomain a R) f Df)
    (hzero : ∀ᵐ x ∂volume.restrict (Metric.ball a R \ Metric.closedBall a r), f x = 0) :
    HasZeroBoundaryValues (ballDomain a R) f Df := by
  let ρ : ℝ := (r + R) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith only [hr, hR]
  have hrρ : r ≤ ρ := by dsimp [ρ]; linarith only [hrR]
  have hρR : ρ < R := by dsimp [ρ]; linarith only [hrR]
  let χ : ContDiffBump a := ⟨ρ, (ρ + R) / 2, hρ, by linarith only [hρR]⟩
  have hχ : ContDiff ℝ ∞ (χ : Domain n → ℝ) := χ.contDiff
  have hsχ : tsupport (χ : Domain n → ℝ) ⊆ Metric.ball a R := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith only [hρR])
  have hzero_on : ∀ᵐ x ∂volume, x ∈ Metric.ball a R \ Metric.closedBall a r → f x = 0 :=
    (ae_restrict_iff' (Metric.isOpen_ball.measurableSet.diff
      Metric.isClosed_closedBall.measurableSet)).1 hzero
  have heq : (fun x => χ x • f x) =ᵐ[volume.restrict (Metric.ball a R)] f := by
    apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
    filter_upwards [hzero_on] with x hx hxR
    by_cases hxr : x ∈ Metric.closedBall a r
    · have hxρ : x ∈ Metric.closedBall a χ.rIn :=
        (Metric.closedBall_subset_closedBall hrρ) hxr
      rw [χ.one_of_mem_closedBall hxρ, one_smul]
    · rw [hx ⟨hxR, hxr⟩, smul_zero]
  have hz := hf.smoothCutoff_zeroBoundary_ball hR hχ χ.hasCompactSupport hsχ
  have hgrad := hz.1.1.ae_eq_of_ae_eq_map hf.1 heq
  exact hz.congr_ae heq hgrad

end HarmonicMaps
