module
public import HarmonicMaps.Geometry.TubularProjection
public section
open Set
open scoped ContDiff
namespace HarmonicMaps.Providers.TubularProjectionCharacterization

theorem result (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  0 < tubularBaseRadius q N ∧
  let U := tubularTube q N
  let P := tubularProjection q N
  IsOpen U ∧
  (∀ z : U,
    (∀ p : N.Carrier, dist z.val (P z).val ≤ dist z.val p.val) ∧
    ∀ p : N.Carrier,
      (∀ p' : N.Carrier, dist z.val p.val ≤ dist z.val p'.val) → p = P z) ∧
  (∀ p : N.Carrier, ∃ hp : p.val ∈ U, P ⟨p.val, hp⟩ = p) ∧
  (∀ z : U, ∃ V : Set (Ambient q), IsOpen V ∧ z.val ∈ V ∧ V ⊆ U ∧
    ∃ g : Ambient q → Ambient q, ContDiffOn ℝ ∞ g V ∧
      ∀ w : U, w.val ∈ V → g w.val = (P w).val) ∧
  (∀ (z : U) (V₁ V₂ : Set (Ambient q)) (g₁ g₂ : Ambient q → Ambient q),
    IsOpen V₁ → IsOpen V₂ → z.val ∈ V₁ → z.val ∈ V₂ → V₁ ⊆ U → V₂ ⊆ U →
    ContDiffOn ℝ ∞ g₁ V₁ → ContDiffOn ℝ ∞ g₂ V₂ →
    (∀ w : U, w.val ∈ V₁ → g₁ w.val = (P w).val) →
    (∀ w : U, w.val ∈ V₂ → g₂ w.val = (P w).val) →
    fderiv ℝ g₁ z.val = fderiv ℝ g₂ z.val ∧
    fderiv ℝ (fderiv ℝ g₁) z.val = fderiv ℝ (fderiv ℝ g₂) z.val) ∧
  ∀ S : U → N.Carrier,
    (∀ z : U, ∀ p : N.Carrier, dist z.val (S z).val ≤ dist z.val p.val) → S = P :=
by
  classical
  have hRadius := Classical.choose_spec (tubularProjectionWellDefined q N)
  have hP := Classical.choose_spec hRadius.2.2
  have hSpec := hP.1
  refine ⟨hRadius.1, hRadius.2.1, hSpec.1, ?_, hSpec.2.1, hSpec.2.2, ?_⟩
  · intro p
    have hp : p.val ∈ tubularTube q N := by
      change Metric.infDist p.val N.carrierSet < 2 * tubularBaseRadius q N
      rw [Metric.infDist_zero_of_mem p.property]
      exact mul_pos (by norm_num) hRadius.1
    refine ⟨hp, ?_⟩
    symm
    apply (hSpec.1 ⟨p.val, hp⟩).2 p
    intro p'
    simp only [dist_self, dist_nonneg]
  · intro S hS
    funext z
    exact ((hSpec.1 z).2 (S z) (hS z))

end HarmonicMaps.Providers.TubularProjectionCharacterization
end
