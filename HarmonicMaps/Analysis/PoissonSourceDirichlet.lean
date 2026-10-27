module

public import HarmonicMaps.Analysis.PoissonDirichletAssembly
public import HarmonicMaps.Analysis.SphereSurfaceMeasure

/-!
# Euclidean surface-measure Dirichlet construction

The Poisson solution uses the manuscript's normalized Euclidean surface measure.
For data smooth near the closed ball, the same solution has native Sobolev data,
a genuine zero-boundary difference, and uniqueness on the closed-ball carrier.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The literal source surface-area formula, closed-ball solution, Sobolev data,
zero-boundary difference and uniqueness all concern the same witnesses. -/
theorem poisson_source_closedData_dirichlet_assembly {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    ∃ v : Metric.closedBall (0 : Domain n) R.val → Ambient q,
      Continuous v ∧
      (∀ b : Metric.sphere (0 : Domain n) R.val,
        v ⟨b.val, Metric.sphere_subset_closedBall b.property⟩ = m b.val) ∧
      ∃ w : Domain n → Ambient q,
        (∀ x : Metric.closedBall (0 : Domain n) R.val, w x.val = v x) ∧
        ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) R.val,
          w x = ((R.val ^ 2 - ‖x‖ ^ 2) /
            ((n : ℝ) * (volume : Measure (Domain n)).real
              (Metric.ball 0 1) * R.val)) •
            (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
              ∂((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
                (Metric.sphere (0 : Domain n) R.val)))) ∧
        MemW12 (ballDomain (0 : Domain n) R.val) w
          (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) (m - w)
          (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
            fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        (∀ z : Domain n → Ambient q,
          ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) R.val) →
          (∀ x ∈ Metric.sphere (0 : Domain n) R.val, z x = m x) →
          (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian z x = 0) →
          EqOn z w (Metric.closedBall (0 : Domain n) R.val)) ∧
        (∀ v' : Metric.closedBall (0 : Domain n) R.val → Ambient q,
          (∃ z : Domain n → Ambient q,
            (∀ x : Metric.closedBall (0 : Domain n) R.val, z x.val = v' x) ∧
            ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) R.val) ∧
            (∀ x ∈ Metric.sphere (0 : Domain n) R.val, z x = m x) ∧
            (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian z x = 0)) →
          v' = v) := by
  simpa only [poisson_scaledPolar_eq_euclideanSphereArea hn R] using
    poisson_scaledPolar_dirichlet_assembly hn R U hU hclosed m hm

end HarmonicMaps
end
