module

public import HarmonicMaps.Analysis.InnerVariationGeometry

/-!
# Interior support of inverse-coordinate differences

Outside the support of the vector field, the domain variation is the
identity. Its actual inverse therefore fixes these points, and composition
with that inverse changes a map only on the same compact support.
-/

public section

open Set

namespace HarmonicMaps

/-- The inverse fixes every point outside the closed support of the field. -/
theorem innerVariation_inverse_eq_self_off_support {n : ℕ}
    {ζ g : Domain n → Domain n} {t : ℝ}
    (hg : ∀ x, g (x + t • ζ x) = x) {x : Domain n} (hx : x ∉ tsupport ζ) :
    g x = x := by
  have hz : ζ x = 0 := image_eq_zero_of_notMem_tsupport hx
  simpa only [hz, smul_zero, add_zero] using hg x

/-- The actual map difference has no support outside that of the field. -/
theorem innerVariation_difference_tsupport_subset {n q : ℕ}
    {ζ g : Domain n → Domain n} {t : ℝ} (hg : ∀ x, g (x + t • ζ x) = x)
    (u : Domain n → Ambient q) :
    tsupport (u ∘ g - u) ⊆ tsupport ζ := by
  apply closure_minimal _ (isClosed_tsupport ζ)
  intro x hx
  by_contra hn
  apply hx
  change u (g x) - u x = 0
  rw [innerVariation_inverse_eq_self_off_support hg hn, sub_self]

/-- Compact support of the vector field yields actual compact support of
its inverse-coordinate difference, without any regularity assumption on u. -/
theorem innerVariation_difference_hasCompactSupport {n q : ℕ}
    {ζ g : Domain n → Domain n} {t : ℝ} (hc : HasCompactSupport ζ)
    (hg : ∀ x, g (x + t • ζ x) = x) (u : Domain n → Ambient q) :
    HasCompactSupport (u ∘ g - u) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (innerVariation_difference_tsupport_subset hg u)

end HarmonicMaps
