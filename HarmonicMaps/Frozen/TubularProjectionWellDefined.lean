module

public import HarmonicMaps.Sobolev
public import HarmonicMaps.Target
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import HarmonicMaps.Providers.TubularProjectionWellDefined

/-! # Uniform unique smooth tubular projection

A uniform tubular neighborhood admits a unique nearest-point projection.
Local smooth extensions agree on the carrier and determine the same
derivatives there.
-/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

open Set
open scoped ContDiff

namespace HarmonicMaps

theorem tubularProjectionWellDefined (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  ∃ ρ : ℝ, 0 < ρ ∧
  let U : Set (Ambient q) := {z | Metric.infDist z N.carrierSet < 2 * ρ}
  IsOpen U ∧
  ∃! P : U → N.Carrier,
    (∀ z : U,
      (∀ p : N.Carrier, dist z.val (P z).val ≤ dist z.val p.val) ∧
      ∀ p : N.Carrier,
        (∀ p' : N.Carrier, dist z.val p.val ≤ dist z.val p'.val) → p = P z) ∧
    (∀ z : U, ∃ V : Set (Ambient q), IsOpen V ∧ z.val ∈ V ∧ V ⊆ U ∧
      ∃ g : Ambient q → Ambient q, ContDiffOn ℝ ∞ g V ∧
        ∀ w : U, w.val ∈ V → g w.val = (P w).val) ∧
    (∀ (z : U) (V₁ V₂ : Set (Ambient q)) (g₁ g₂ : Ambient q → Ambient q),
      IsOpen V₁ → IsOpen V₂ → z.val ∈ V₁ → z.val ∈ V₂ → V₁ ⊆ U → V₂ ⊆ U →
      ContDiffOn ℝ ∞ g₁ V₁ → ContDiffOn ℝ ∞ g₂ V₂ →
      (∀ w : U, w.val ∈ V₁ → g₁ w.val = (P w).val) →
      (∀ w : U, w.val ∈ V₂ → g₂ w.val = (P w).val) →
      fderiv ℝ g₁ z.val = fderiv ℝ g₂ z.val ∧
      fderiv ℝ (fderiv ℝ g₁) z.val = fderiv ℝ (fderiv ℝ g₂) z.val) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.TubularProjectionWellDefined.result q N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps

end
-- FROZEN_ANCHOR_SUFFIX_END
