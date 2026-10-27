module

public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.Analysis.PoincareSobolevLimit

/-!
# Poincare inequality for finite weak Sobolev maps on balls

Whole-ball smooth density supplies every approximation premise of the passage
to the limit in Giaquinta's smooth estimate. The ball average, weak gradient,
HS energy normalization and constant are unchanged.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

/-- Giaquinta's ball Poincare estimate for the same displayed weak gradient. -/
theorem MemW12.poincare_ball {n q : ℕ} {a : Domain n} {r : ℝ} (hr : 0 < r)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du) :
    (∫ x in Metric.ball a r, ‖u x - ⨍ y in Metric.ball a r, u y‖ ^ 2) ≤
      (2 : ℝ) ^ (n + 1) * r ^ 2 * ∫ x in Metric.ball a r, hsNormSq (Du x) := by
  obtain ⟨m, hm, hmW, hconv, hDconv⟩ := hu.smoothDensity_memW12_ball hr
  exact poincare_ball_of_smooth_L2_approximation a hr hu.2.1 hu.2.2 m
    (fun k => (hm k).contDiffOn) (fun k => (hmW k).2.1)
    (fun k => (hmW k).2.2) hconv hDconv

end HarmonicMaps
