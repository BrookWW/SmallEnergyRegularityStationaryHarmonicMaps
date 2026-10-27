module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Derivative locality for ambient certificates

Two certificates of the same subtype map agree on their open overlap.
Their first and second total derivatives therefore agree at every point
of that overlap. Certificate existence and smoothness are separate facts.
-/

public section

open Filter Set
open scoped Topology

namespace HarmonicMaps

/-- Open-overlap equality determines both derivative operators. -/
theorem localCertificate_derivatives_eq {q r : ℕ} {U : Set (Ambient q)}
    (f : U → Ambient r) (z : U) (V₁ V₂ : Set (Ambient q))
    (g₁ g₂ : Ambient q → Ambient r)
    (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (hz₁ : z.val ∈ V₁) (hz₂ : z.val ∈ V₂)
    (hsub₁ : V₁ ⊆ U) (hsub₂ : V₂ ⊆ U)
    (hcert₁ : ∀ w : U, w.val ∈ V₁ → g₁ w.val = f w)
    (hcert₂ : ∀ w : U, w.val ∈ V₂ → g₂ w.val = f w) :
    fderiv ℝ g₁ z.val = fderiv ℝ g₂ z.val ∧
    fderiv ℝ (fderiv ℝ g₁) z.val = fderiv ℝ (fderiv ℝ g₂) z.val := by
  have heq : g₁ =ᶠ[𝓝 z.val] g₂ := by
    filter_upwards [(hV₁.inter hV₂).mem_nhds ⟨hz₁, hz₂⟩] with x hx
    exact (hcert₁ ⟨x, hsub₁ hx.1⟩ hx.1).trans
      (hcert₂ ⟨x, hsub₂ hx.2⟩ hx.2).symm
  exact ⟨heq.fderiv_eq, heq.fderiv.fderiv_eq⟩

end HarmonicMaps

end
