module

public import HarmonicMaps.Sobolev

/-! # Continuous representatives on an open domain

The representative is a function on the domain subtype itself. Uniqueness on
this carrier does not assert uniqueness of an extension outside the domain.
-/

@[expose] public section

open MeasureTheory

namespace HarmonicMaps

/-- A continuous representative agrees with the ambient Sobolev map almost
everywhere on the specified domain. The subtype function has no off-domain values. -/
def IsContinuousRepresentative {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (w : Ω.val → Ambient q) : Prop :=
  Continuous w ∧
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ hx : x ∈ Ω.val, w ⟨x, hx⟩ = u x

end HarmonicMaps

end
