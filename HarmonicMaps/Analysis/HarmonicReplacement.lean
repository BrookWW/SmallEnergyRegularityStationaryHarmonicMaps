module

public import HarmonicMaps.Analysis.PoissonSourceDirichlet
public import HarmonicMaps.Analysis.InteriorMollification

/-!
# Harmonic replacement of the actual fixed-scale smoothing

The literal source mollification at scale eta^(1/4) determines a harmonic
replacement on the half-unit ball. Finite source energy and the compact target
produce the mollification's smooth neighborhood data internally. The same
replacement has the source surface-integral formula, Sobolev columns,
zero-boundary difference and closed-carrier uniqueness.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The source fixed-scale smoothing has a genuine harmonic replacement on
the half-unit ball, with all boundary, Sobolev and uniqueness conclusions. -/
theorem harmonicReplacement_fixedScale {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u)
    (η : ℝ) (hη : 0 < η) (hηscale : η ^ (1 / 4 : ℝ) ≤ 1 / 4)
    (hsmall : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η) :
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
    ∃ v : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ) → Ambient q,
      Continuous v ∧
      (∀ b : Metric.sphere (0 : Domain n) (1 / 2 : ℝ),
        v ⟨b.val, Metric.sphere_subset_closedBall b.property⟩ = m b.val) ∧
      ∃ w : Domain n → Ambient q,
        (∀ x : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ), w x.val = v x) ∧
        ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ)) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), Laplacian.laplacian w x = 0) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          w x = (((1 / 2 : ℝ) ^ 2 - ‖x‖ ^ 2) /
            ((n : ℝ) * (volume : Measure (Domain n)).real
              (Metric.ball 0 1) * (1 / 2 : ℝ))) •
            (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
              ∂((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
                (Metric.sphere (0 : Domain n) (1 / 2 : ℝ))))) ∧
        MemW12 (ballDomain (0 : Domain n) (1 / 2 : ℝ)) w
          (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        HasZeroBoundaryValues (ballDomain (0 : Domain n) (1 / 2 : ℝ)) (m - w)
          (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
            fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        (∀ z : Domain n → Ambient q,
          ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ)) →
          (∀ x ∈ Metric.sphere (0 : Domain n) (1 / 2 : ℝ), z x = m x) →
          (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), Laplacian.laplacian z x = 0) →
          EqOn z w (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ))) ∧
        (∀ v' : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ) → Ambient q,
          (∃ z : Domain n → Ambient q,
            (∀ x : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ), z x.val = v' x) ∧
            ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ)) ∧
            (∀ x ∈ Metric.sphere (0 : Domain n) (1 / 2 : ℝ), z x = m x) ∧
            (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), Laplacian.laplacian z x = 0)) →
          v' = v) := by
  let h : PositiveRadius := ⟨η ^ (1 / 4 : ℝ), Real.rpow_pos_of_pos hη _⟩
  have hfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  obtain ⟨_, _, hm, hclosed, _⟩ := hu.interiorMollification_spec N hN hfinite h hηscale
  let R : PositiveRadius := ⟨1 / 2, by norm_num⟩
  exact poisson_source_closedData_dirichlet_assembly hn R (Metric.ball 0 (3 / 4))
    Metric.isOpen_ball hclosed
    (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)) hm

end HarmonicMaps
end
