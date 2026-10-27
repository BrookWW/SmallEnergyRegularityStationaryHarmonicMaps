module

public import HarmonicMaps.Energy

/-! # The domain stress identity with the displayed weak gradient -/

@[expose] public section

open HarmonicMaps MeasureTheory
open scoped BigOperators ContDiff

namespace StationaryHarmonicMaps

/-- The domain stress identity against every smooth compactly supported
vector field in the open domain. Sobolev membership is a separate condition. -/
def IsDomainStationary {n q : ℕ} (Ω : OpenDomain n)
    (Du : Domain n → Gradient n q) : Prop :=
  ∀ (X : Domain n → Domain n), ContDiff ℝ ∞ X →
    HasCompactSupport X → tsupport X ⊆ Ω.val →
    IntegrableOn (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) Ω.val volume ∧
    (∫ x in Ω.val, hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) = 0

end StationaryHarmonicMaps

end
