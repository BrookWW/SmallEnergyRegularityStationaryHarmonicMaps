module

public import HolderToCK.Foundation.HolderBounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! # Ambient derivative estimates on an open carrier

The derivative object is Mathlib's iterated Frechet derivative. Its public
carrier includes smoothness on the open domain, so the formula is used only
where the mathematical derivative exists. No off-domain value is prescribed.
-/

@[expose] public section

namespace HolderToCK

open HarmonicMaps
open scoped ContDiff

/-- A pointwise operator-norm bound for the actual iterated derivative. -/
def DerivativeNormBoundOn {n q : ℕ} (Ω : OpenDomain n)
    (w : Domain n → Ambient q) (_hSmooth : ContDiffOn ℝ ∞ w Ω.val)
    (k : ℕ) (M : ℝ) : Prop :=
  ∀ x ∈ Ω.val, ‖iteratedFDeriv ℝ k w x‖ ≤ M

/-- A Holder bound for the same iterated derivative object. -/
def DerivativeHolderBoundOn {n q : ℕ} (Ω : OpenDomain n)
    (w : Domain n → Ambient q) (_hSmooth : ContDiffOn ℝ ∞ w Ω.val)
    (k : ℕ) (γ M : ℝ) : Prop :=
  HolderBoundOn Ω.val (iteratedFDeriv ℝ k w) γ M

end HolderToCK
end
