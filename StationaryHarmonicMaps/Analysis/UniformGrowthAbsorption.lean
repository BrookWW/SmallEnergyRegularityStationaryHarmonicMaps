module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Absorption of a finite uniform weighted growth coefficient

The actual ratios f(x)/w(x) form a nonempty bounded real set. Its least
upper bound is an effective growth coefficient, so the original improvement
rule applies to that coefficient and yields the absorbed bound.
-/

public section

namespace StationaryHarmonicMaps.Analysis

/-- A genuine finite uniform weighted bound and its contraction improvement
give the absorbed bound for the same original nonnegative function. -/
theorem uniform_weighted_growth_absorption {X : Type*} [Nonempty X]
    (f w : X → ℝ) (hf : ∀ x, 0 ≤ f x) (hw : ∀ x, 0 < w x)
    (a b K₀ : ℝ) (ha : 0 ≤ a) (haOne : a < 1) (hb : 0 ≤ b)
    (hFinite : ∀ x, f x ≤ K₀ * w x)
    (hStep : ∀ K : ℝ, 0 ≤ K → (∀ x, f x ≤ K * w x) →
      ∀ x, f x ≤ (a * K + b) * w x) :
    ∀ x, f x ≤ (b / (1 - a)) * w x := by
  let S := Set.range (fun x => f x / w x)
  let M := sSup S
  have hNonempty : S.Nonempty := Set.range_nonempty _
  have hBounded : BddAbove S := by
    refine ⟨K₀, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (div_le_iff₀ (hw x)).mpr (hFinite x)
  have hMNonneg : 0 ≤ M := by
    obtain ⟨_, x, rfl⟩ := hNonempty
    exact (div_nonneg (hf x) (hw x).le).trans (le_csSup hBounded ⟨x, rfl⟩)
  have hMEffective (x : X) : f x ≤ M * w x :=
    (div_le_iff₀ (hw x)).mp (le_csSup hBounded ⟨x, rfl⟩)
  have hImproved := hStep M hMNonneg hMEffective
  have hSupImproved : M ≤ a * M + b := by
    apply Real.sSup_le
    · rintro _ ⟨x, rfl⟩
      exact (div_le_iff₀ (hw x)).mpr (hImproved x)
    · exact add_nonneg (mul_nonneg ha hMNonneg) hb
  have hAbsorbed : M ≤ b / (1 - a) := by
    apply (le_div_iff₀ (sub_pos.mpr haOne)).mpr
    nlinarith only [hSupImproved]
  intro x
  exact (hMEffective x).trans (mul_le_mul_of_nonneg_right hAbsorbed (hw x).le)

end StationaryHarmonicMaps.Analysis

end
