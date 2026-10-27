module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The signed weak Poisson equation

The displayed gradient is used in the test pairing. The equation carries
the integrability needed by those pairings and no regularity consequence.
-/

@[expose] public section

namespace HolderToCK

open HarmonicMaps MeasureTheory
open scoped ContDiff

/-- The distributional equation `Δu = F`, with its explicit gradient columns.
Sobolev membership is a separate hypothesis when this predicate is used. -/
def WeakPoissonOn {n q : ℕ} (Ω : OpenDomain n)
    (Du : Domain n → Gradient n q) (F : Domain n → Ambient q) : Prop :=
  LocallyIntegrableOn F Ω.val volume ∧
    ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      IntegrableOn (fun x => ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val ∧
      IntegrableOn (fun x => inner ℝ (F x) (ψ x)) Ω.val ∧
      (∫ x in Ω.val, ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        -(∫ x in Ω.val, inner ℝ (F x) (ψ x))

end HolderToCK
end
