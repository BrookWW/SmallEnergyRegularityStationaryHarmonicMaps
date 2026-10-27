module

public import HarmonicMaps.Sobolev
public import HarmonicMaps.Target
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import HarmonicMaps.Geometry.TargetNearestCertificateOverlap

/-!
# Unique smooth closest-point projection on a uniform tube

Actual uniform nearest-point certificates give pointwise uniqueness before a
tube-valued selection is formed. The same selection has smooth local ambient
certificates, and every pair of such certificates has the same first and second
derivatives on its open overlap.
-/

public section

open Set
open scoped ContDiff

namespace HarmonicMaps.Providers.TubularProjectionWellDefined

theorem result (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
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
      fderiv ℝ (fderiv ℝ g₁) z.val = fderiv ℝ (fderiv ℝ g₂) z.val) := by
  classical
  obtain ⟨ρ, hρ, hUniform⟩ := N.exists_uniform_nearest_certificate_overlap
  let U : Set (Ambient q) := {z | Metric.infDist z N.carrierSet < 2 * ρ}
  have hU : IsOpen U :=
    isOpen_lt (Metric.continuous_infDist_pt N.carrierSet) continuous_const
  have hPoint : ∀ z : U,
      ∃! p : N.Carrier, ∀ r : N.Carrier, dist z.val p.val ≤ dist z.val r.val := by
    intro z
    obtain ⟨epsilon, hepsilon, _, g, _, hMin, _⟩ := hUniform z.val z.property
    obtain ⟨hmem, hmin, hunique⟩ := hMin z.val (Metric.mem_ball_self hepsilon)
    exact ⟨⟨g z.val, hmem⟩, hmin, fun p hp => Subtype.ext (hunique p hp)⟩
  let P : U → N.Carrier := fun z => Classical.choose (hPoint z)
  have hP : ∀ z : U,
      (∀ p : N.Carrier, dist z.val (P z).val ≤ dist z.val p.val) ∧
      ∀ p : N.Carrier,
        (∀ p' : N.Carrier, dist z.val p.val ≤ dist z.val p'.val) → p = P z :=
    fun z => Classical.choose_spec (hPoint z)
  refine ⟨ρ, hρ, hU, P, ⟨hP, ?_, ?_⟩, ?_⟩
  · intro z
    obtain ⟨epsilon, hepsilon, hBallTube, g, hg, hMin, _⟩ := hUniform z.val z.property
    refine ⟨Metric.ball z.val epsilon, Metric.isOpen_ball,
      Metric.mem_ball_self hepsilon, hBallTube, g, hg, ?_⟩
    intro w hw
    exact ((hMin w.val hw).2.2 (P w) (hP w).1).symm
  · intro z V₁ V₂ g₁ g₂ hV₁ hV₂ hz₁ hz₂ hsub₁ hsub₂ _hg₁ _hg₂ hcert₁ hcert₂
    exact HarmonicMaps.localCertificate_derivatives_eq (fun w : U => (P w).val)
      z V₁ V₂ g₁ g₂ hV₁ hV₂ hz₁ hz₂ hsub₁ hsub₂ hcert₁ hcert₂
  · intro Q hQ
    funext z
    exact (hP z).2 (Q z) (hQ.1 z).1

end HarmonicMaps.Providers.TubularProjectionWellDefined

end
