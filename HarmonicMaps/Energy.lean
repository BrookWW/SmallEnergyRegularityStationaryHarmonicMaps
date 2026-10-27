module

public import HarmonicMaps.Sobolev

/-!
# Hilbert--Schmidt Dirichlet energy

Energy is an extended nonnegative integral. In particular, a nonintegrable
energy density is never silently assigned real value zero. Finite-energy
hypotheses allow conversion to real numbers where a quantitative bound needs it.
The normalization uses no factor of one half.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace HarmonicMaps

/-- Strictly positive radii are the public carrier of normalized energy. -/
abbrev PositiveRadius := {r : ℝ // 0 < r}

noncomputable section

/-- The squared Hilbert--Schmidt norm of the gradient columns. -/
def hsNormSq {n q : ℕ} (A : Gradient n q) : ℝ :=
  ∑ i : Fin n, ‖A i‖ ^ 2

/-- Dirichlet energy, including the possible value infinity. -/
def dirichletEnergy {n q : ℕ} (Du : Domain n → Gradient n q)
    (U : Set (Domain n)) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (hsNormSq (Du x))

/-- The normalized energy r^(2-n) E(B_r(a)) on strictly positive radii. -/
def normalizedEnergy {n q : ℕ} (Du : Domain n → Gradient n q)
    (a : Domain n) (r : PositiveRadius) : ℝ≥0∞ :=
  ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
    dirichletEnergy Du (Metric.ball a r.val)

end
end HarmonicMaps

end
