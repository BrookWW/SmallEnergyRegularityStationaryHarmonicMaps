-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.Monotonicity

/-! # Monotonicity from the actual domain stress identity -/

public section

open HarmonicMaps MeasureTheory Set
open scoped BigOperators

namespace StationaryHarmonicMaps

theorem IsDomainStationary.monotonicity {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hstationary : IsDomainStationary Ω Du) (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (hrR : r ≤ R) :
    IntegrableOn (fun x => ‖x - a‖ ^ (2 - (n : ℤ)) *
      ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2)
      (Metric.ball a r \ Metric.ball a s) volume ∧
    ((normalizedEnergy Du a ⟨r, hs.trans hsr⟩).toReal -
      (normalizedEnergy Du a ⟨s, hs⟩).toReal =
      2 * ∫ x in Metric.ball a r \ Metric.ball a s, ‖x - a‖ ^ (2 - (n : ℤ)) *
        ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) ∧
    normalizedEnergy Du a ⟨s, hs⟩ ≤ normalizedEnergy Du a ⟨r, hs.trans hsr⟩ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StationaryHarmonicMaps.Providers.monotonicity hn hstationary hu hR hball hs hsr hrR
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps

end
-- FROZEN_ANCHOR_SUFFIX_END
