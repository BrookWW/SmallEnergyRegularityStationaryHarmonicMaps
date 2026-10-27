module

public import HarmonicMaps.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Pointwise Holder bounds on Euclidean sets

The predicate is the literal pairwise estimate from the manuscript. Exponent
and constant sign conditions are explicit hypotheses of theorems using it.
-/

@[expose] public section

namespace HolderToCK

open HarmonicMaps

/-- The pairwise Holder estimate on a specified carrier. -/
def HolderBoundOn {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (s : Set (Domain n)) (f : Domain n → E) (α H : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s,
    ‖f x - f y‖ ≤ H * Real.rpow (dist x y) α

/-- Every point has a compactly contained ball with a finite Holder estimate.
The local exponent and constant are allowed to depend on the ball. -/
def LocallyHolderOn {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Ω : OpenDomain n) (f : Domain n → E) : Prop :=
  ∀ x ∈ Ω.val, ∃ r : HarmonicMaps.PositiveRadius,
    Metric.closedBall x r.val ⊆ Ω.val ∧
      ∃ α H : ℝ, 0 < α ∧ α < 1 ∧ 0 ≤ H ∧
        HolderBoundOn (Metric.ball x r.val) f α H

/-- Restrict a literal Holder bound to a smaller set. -/
theorem HolderBoundOn.mono {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s t : Set (Domain n)} {f : Domain n → E} {α H : ℝ}
    (h : HolderBoundOn s f α H) (ht : t ⊆ s) : HolderBoundOn t f α H := by
  intro x hx y hy
  exact h x (ht hx) y (ht hy)

end HolderToCK
end
