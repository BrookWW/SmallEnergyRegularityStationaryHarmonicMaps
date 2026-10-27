module

public import HarmonicMaps.Analysis.PoissonBoundaryConvergence
import Mathlib.Topology.ExtendFrom

/-!
# Continuous completion of the canonical ball Poisson integral

The canonical scaled-polar integral determines a unique continuous function
on the closed ball, with the prescribed values at every sphere point. The
statement concerns this canonical measure and makes no surface-area or
closed-boundary differentiability assertion.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

/-- The literal canonical integral has a unique continuous closed-ball
completion with the actual prescribed sphere values. -/
theorem poisson_scaledPolar_continuousClosedBall_existsUnique {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    ∃! v : Metric.closedBall (0 : Domain n) R.val → Ambient q,
      Continuous v ∧
      (∀ x : Metric.ball (0 : Domain n) R.val,
        v ⟨x.val, Metric.ball_subset_closedBall x.property⟩ =
          ((R.val ^ 2 - ‖x.val‖ ^ 2) /
            ((n : ℝ) * (volume : Measure (Domain n)).real
              (Metric.ball 0 1) * R.val)) •
            (∫ y : Domain n, (‖x.val - y‖ ^ n)⁻¹ • m y
              ∂Measure.map
                (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
                (ENNReal.ofReal (R.val ^ (n - 1)) •
                  (volume : Measure (Domain n)).toSphere))) ∧
      (∀ b : Metric.sphere (0 : Domain n) R.val,
        v ⟨b.val, Metric.sphere_subset_closedBall b.property⟩ = m b.val) := by
  classical
  let F : Domain n → Ambient q := fun x =>
    ((R.val ^ 2 - ‖x‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) •
            (volume : Measure (Domain n)).toSphere))
  have hF : ContinuousOn F (Metric.ball (0 : Domain n) R.val) :=
    (poisson_scaledPolar_integral_smooth_harmonic hn R U hU hclosed m hm).1.continuousOn
  have hclosure : Metric.closedBall (0 : Domain n) R.val ⊆
      closure (Metric.ball (0 : Domain n) R.val) := by
    rw [closure_ball 0 (ne_of_gt R.property)]
  have hlimit : ∀ x ∈ Metric.closedBall (0 : Domain n) R.val,
      ∃ y : Ambient q, Tendsto F (nhdsWithin x (Metric.ball (0 : Domain n) R.val))
        (nhds y) := by
    intro x hx
    by_cases hxb : x ∈ Metric.ball (0 : Domain n) R.val
    · exact ⟨F x, hF x hxb⟩
    · have hxs : x ∈ Metric.sphere (0 : Domain n) R.val := by
        have hsplit : x ∈ Metric.sphere (0 : Domain n) R.val ∪
            Metric.ball (0 : Domain n) R.val := by
          rw [Metric.sphere_union_ball]
          exact hx
        exact hsplit.resolve_right hxb
      exact ⟨m x, poisson_scaledPolar_boundary_tendsto hn R U hU hclosed m hm x hxs⟩
  let G : Domain n → Ambient q := extendFrom (Metric.ball (0 : Domain n) R.val) F
  have hG : ContinuousOn G (Metric.closedBall (0 : Domain n) R.val) :=
    continuousOn_extendFrom hclosure hlimit
  have hInterior (x : Metric.ball (0 : Domain n) R.val) : G x.val = F x.val :=
    extendFrom_extends hF x.val x.property
  have hBoundary (b : Metric.sphere (0 : Domain n) R.val) : G b.val = m b.val :=
    extendFrom_eq (hclosure (Metric.sphere_subset_closedBall b.property))
      (poisson_scaledPolar_boundary_tendsto hn R U hU hclosed m hm b.val b.property)
  let v : Metric.closedBall (0 : Domain n) R.val → Ambient q := fun x => G x.val
  refine ⟨v, ⟨hG.restrict, hInterior, hBoundary⟩, ?_⟩
  rintro w ⟨_, hwInterior, hwBoundary⟩
  funext x
  by_cases hxb : x.val ∈ Metric.ball (0 : Domain n) R.val
  · exact (hwInterior ⟨x.val, hxb⟩).trans (hInterior ⟨x.val, hxb⟩).symm
  · have hxs : x.val ∈ Metric.sphere (0 : Domain n) R.val := by
      have hsplit : x.val ∈ Metric.sphere (0 : Domain n) R.val ∪
          Metric.ball (0 : Domain n) R.val := by
        rw [Metric.sphere_union_ball]
        exact x.property
      exact hsplit.resolve_right hxb
    exact (hwBoundary ⟨x.val, hxs⟩).trans (hBoundary ⟨x.val, hxs⟩).symm

end HarmonicMaps

end
