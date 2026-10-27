module

public import HarmonicMaps.Analysis.RadialVectorField

/-!
# Admissibility of smooth radial domain tests

A smooth profile constant near zero and vanishing beyond an interior radius
gives a smooth, compactly supported vector field inside the specified ball.
-/

public section

open Set
open scoped ContDiff

namespace HarmonicMaps

/-- Radial cutoff profiles have closed support in the corresponding closed
ball, including for a translated center. -/
theorem radialVectorField_tsupport_subset_closedBall {n : ℕ}
    {eta : ℝ → ℝ} {ρ : ℝ} (hvanish : ∀ t : ℝ, ρ ≤ t → eta t = 0)
    (a : Domain n) :
    tsupport (fun x => radialVectorField eta (x - a)) ⊆ Metric.closedBall a ρ := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm_sub]
  by_contra h
  have he := hvanish ‖x - a‖ (le_of_lt (lt_of_not_ge h))
  exact hx (by simp only [radialVectorField, he, zero_smul])

/-- A bounded radial profile supplies compact support for the translated
radial vector field. -/
theorem radialVectorField_hasCompactSupport {n : ℕ}
    {eta : ℝ → ℝ} {ρ : ℝ} (hvanish : ∀ t : ℝ, ρ ≤ t → eta t = 0)
    (a : Domain n) : HasCompactSupport (fun x => radialVectorField eta (x - a)) :=
  (isCompact_closedBall a ρ).of_isClosed_subset (isClosed_tsupport _)
    (radialVectorField_tsupport_subset_closedBall hvanish a)

/-- Source radial test profiles give actual smooth compact-support tests
inside the ball around any center. -/
theorem radialVectorField_admissible {n : ℕ} {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta)
    (hplateau : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0)
    {ρ R : ℝ} (hρR : ρ < R) (hvanish : ∀ t : ℝ, ρ ≤ t → eta t = 0)
    (a : Domain n) :
    ContDiff ℝ ∞ (fun x => radialVectorField eta (x - a)) ∧
    HasCompactSupport (fun x => radialVectorField eta (x - a)) ∧
    tsupport (fun x => radialVectorField eta (x - a)) ⊆ Metric.ball a R :=
  ⟨(radialVectorField_contDiff hs hplateau).comp (contDiff_id.sub contDiff_const),
    radialVectorField_hasCompactSupport hvanish a,
    (radialVectorField_tsupport_subset_closedBall hvanish a).trans
      (Metric.closedBall_subset_ball hρR)⟩

end HarmonicMaps
