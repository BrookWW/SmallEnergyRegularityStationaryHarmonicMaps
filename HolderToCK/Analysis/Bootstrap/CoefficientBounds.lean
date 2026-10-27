module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-! # One sequence of compact coefficient bounds

Smoothness gives a bounded derivative of every order on a fixed closed
Euclidean ball. The next entry of the same sequence controls the Lipschitz
variation of the current derivative on that convex ball. The entire sequence
is chosen before the points at which any derivative is evaluated.
-/

public section

open HarmonicMaps Set
open scoped ContDiff NNReal

namespace HolderToCK

theorem compact_coefficient_derivative_bounds {q : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Ambient q → E) (hA : ContDiff ℝ ∞ A) (c : Ambient q) (R : ℝ) :
    ∃ b : ℕ → ℝ≥0,
      (∀ k : ℕ, ∀ z ∈ Metric.closedBall c R, ‖iteratedFDeriv ℝ k A z‖ ≤ (b k : ℝ)) ∧
      ∀ k : ℕ, ∀ x ∈ Metric.closedBall c R, ∀ y ∈ Metric.closedBall c R,
        ‖iteratedFDeriv ℝ k A x - iteratedFDeriv ℝ k A y‖ ≤
          (b (k + 1) : ℝ) * ‖x - y‖ := by
  have hAk (k : ℕ) : ContDiff ℝ ∞ (iteratedFDeriv ℝ k A) :=
    hA.iteratedFDeriv_right (i := k) (m := ∞) le_rfl
  have hbound (k : ℕ) : ∃ M : ℝ≥0, ∀ z ∈ Metric.closedBall c R,
      ‖iteratedFDeriv ℝ k A z‖ ≤ (M : ℝ) := by
    obtain ⟨M, hM⟩ := ((isCompact_closedBall c R).image_of_continuousOn
      (hAk k).continuous.continuousOn).isBounded.exists_norm_le
    refine ⟨⟨max M 0, le_max_right _ _⟩, ?_⟩
    intro z hz
    exact (hM _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  choose b hb using hbound
  refine ⟨b, hb, ?_⟩
  intro k x hx y hy
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ((hAk k).differentiable (by simp)).differentiableAt)
    (fun z hz => by rw [norm_fderiv_iteratedFDeriv]; exact hb (k + 1) z hz)
    (convex_closedBall c R) hy hx

end HolderToCK
end
